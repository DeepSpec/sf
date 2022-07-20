(** * WPgen: Weakest Precondition Generator *)

Set Implicit Arguments.
From SLF Require Import WPsem.

Implicit Types f : var.
Implicit Types b : bool.
Implicit Types v : val.
Implicit Types h : heap.
Implicit Types P : Prop.
Implicit Types H : hprop.
Implicit Types Q : val->hprop.

(* ################################################################# *)
(** * First Pass *)

(** In the previous chapter, we have introduced a predicate called [wp]
    to describe the weakest precondition of a term [t] with respect to
    a given postcondition [Q]. The weakest precondition [wp] is defined
    by the equivalence: [H ==> wp t Q] if and only if [triple t H Q].

    With respect to this "characterization of the semantics of [wp]",
    we could prove "wp-style" reasoning rules. For example, the lemma
    [wp_seq] asserts: [wp t1 (fun r => wp t2 Q) ==> wp (trm_seq t1 t2) Q].

    In this chapter, we introduce a function, called [wpgen], to
    "effectively compute" the weakest precondition of a term.
    The value of [wpgen t] is defined recursively over the structure
    of the term [t], and ultimately produces a formula that is logically
    equivalent to [wp t].

    The major difference between [wp] and [wpgen] is that, whereas [wp t]
    is a predicate that we can reason about by "applying" reasoning rules,
    [wpgen t] is a predicate that we can reason about simply by "unfolding"
    its definition. Moreover, [wp] and [wpgen] differs on the way they handle
    variable substitution. Consider, e.g., a let-binding. The wp-style
    reasoning rule for a let-binding introduces a substitution of the form
    [wp (subst x v t2)], which the user must simplify explicitly. On the
    contrary, when working with [wpgen], all the substitutions get automatically
    simplified during the initial evaluation of [wpgen] on the source program;
    the end-user sees none of these substitutions.

    At a high level, the introduction of [wpgen] is a key ingredient to
    smoothening the user-experience of conducting interactive proofs in
    Separation Logic. The matter of the present chapter is to show:

    - how to define [wpgen t] as a recursive function that computes in Coq,
    - how to integrate support for the frame rule in this recursive definition,
    - how to carry out practical proofs using [wpgen].

    A bonus section explains how to establish the soundness theorem for
    [wpgen]. *)

(** The "first pass" section that comes next is fairly short.
    It only gives a bird-eye tour of the steps of the construction.
    Detailed explanations are provided in the main body of the chapter. *)

(** As first approximation, [wpgen t Q] is defined as a recursive function
    that pattern matches on its argument [t], and produces the appropriate
    heap predicate in each case. The definitions somewhat mimic those of
    [wp]. For example, where the rule [wp_let] asserts the entailment,
    [wp t1 (fun v => wp (subst x v t2) Q) ==> wp (trm_let x t1 t2) Q],
    the definition of [wpgen] is such that [wpgen (trm_let x t1 t2) Q]
    is, by definition, equal to [wpgen t1 (fun v => wpgen (subst x v t2) Q)].
    One special case is that of applications. We define [wpgen (trm_app v1 v2)]
    as [wp (trm_app v1 v2)], that is, we fall back onto the semantical
    definition of weakest precondition.

    Fixpoint wpgen (t:trm) (Q:val->hprop) : hprop :=
      match t with
      | trm_val v => Q v
      | trm_var x => \[False]
      | trm_app v1 v2 => wp t Q
      | trm_let x t1 t2 => wpgen t1 (fun v => wpgen (subst x v t2) Q)
      ...
      end.

    From there, to obtain the actual definition of [wpgen], we need to
    refine the above definition in four steps.

    In a first step, we modify the definition in order to make it
    structurally recursive. Indeed, in the above the recursive call
    [wpgen (subst x v t2)] is not made to a strict subterm of
    [trm_let x t1 t2], thus Coq refuse this definition as it stands.

    To fix the issue, we change the definition to the form [wpgen E t Q],
    where [E] denotes an association list bindings values to variables.
    The intention is that [wpgen E t Q] computes the weakest precondition
    for the term obtained by substituting all the bindings from [E] in [t].
    (This term is described by the operation [isubst E t] in the chapter.)

    The updated definition looks as follows. Observe how, when traversing
    [trm_let x t1 t2], the context [E] gets extended as [(x,v)::E].
    Observe also how, when reaching a variable [x], a lookup for [x]
    into the context [E] is performed for recovering the value that,
    morally, should have been substituted for [x].

    Fixpoint wpgen (E:ctx) (t:trm) (Q:val->hprop) : hprop :=
      match t with
      | trm_val v => Q v
      | trm_var x =>
           match lookup x E with
           | Some v => Q v
           | None => \[False]
           end
      | trm_app v1 v2 => wp (isubst E t) Q
      | trm_let x t1 t2 => wpgen E t1 (fun v => wpgen ((x,v)::E) t2 Q)
      ...
      end.
*)

(** In a second step, we slightly tweak the definition so as to swap
    the place where [Q] is taken as argument with the place where
    the pattern matching on [t] occurs. The idea is to make it obvious
    that [wpgen E t] can be computed without any knowledge of [Q].

    The type of [wpgen E t] is [(val->hprop)->hprop], a type which we
    thereafter call [formula].

    Fixpoint wpgen (E:ctx) (t:trm) : formula :=
      match t with
      | trm_val v =>  fun (Q:val->hprop) => Q v
      | trm_var x =>  fun (Q:val->hprop) =>
           match lookup x E with
           | Some v => Q v
           | None => \[False]
           end
      | trm_app v1 v2 => fun (Q:val->hprop) => wp (isubst E t) Q
      | trm_let x t1 t2 => fun (Q:val->hprop) =>
                              wpgen E t1 (fun v => wpgen ((x,v)::E) t2 Q)
      ...
      end.
*)

(** In a third step, we introduce auxiliary definitions to improve
    the readability of the output of calls to [wpgen]. For example,
    we let [wpgen_val v] be a shorthand for [fun (Q:val->hprop) => Q v].
    Likewise, we let [wpgen_let F1 F2] be a shorthand for
    [fun (Q:val->hprop) => F1 (fun v => F2 Q)]. Using these auxiliary
    definitions, the definition of [wpgen] rewrites as follows.

    Fixpoint wpgen (E:ctx) (t:trm) : formula :=
      match t with
      | trm_val v => wpgen_val v
      | trm_var x => wpgen_var E x
      | trm_app t1 t2 => wp (isubst E t)
      | trm_let x t1 t2 => wpgen_let (wpgen E t1) (fun v => wpgen ((x,v)::E) t2)
      ...
      end.

    Each of the auxiliary definitions introduced comes with a custom notation
    that enables a nice display of the output of [wpgen]. For example, we set
    up the notation [Let' v := F1 in F2] to stand for
    [wpgen_let F1 (fun v => F2)].
    Thanks to this notation, the result of computing [wpgen] on a source term
    [Let x := t1 in t2] (which is an Coq expression of type [trm]) will be a
    formula displayed in the form [Let' x := F1 in F2] (which is an Coq
    expression of type [formula]).

    Thanks to these auxiliary definitions and pieces of notation, the formula
    that [wpgen] produces as output reads pretty much like the source term
    provided as input. *)

(** In a fourth step, we refine the definition of [wpgen] in order to equip
    it with inherent support for applications of the structural rules of the
    logic, namely the frame rule and the rule of consequence. To achieve this,
    we consider a well-crafted predicate called [mkstruct], and insert it
    at the head of the output of every call to [wpgen], including all its
    recursive calls. The definition of [wpgen] thus now admits the following
    structure.

    Fixpoint wpgen (E:ctx) (t:trm) : formula :=
      mkstruct (match t with
                | trm_val v => ...
                | ...
                end).

    Without entering the details, the predicate [mkstruct] is a function
    of type [formula->formula] that captures the essence of the wp-style
    consequence-frame structural rule. This rule, called [wp_conseq_frame]
    in the previous chapter, asserts:
    [Q1 \*+ H ===> Q2  ->  (wp t Q1) \* H ==> (wp t Q2)]. *)

(** This concludes our little journey towards the definition of [wpgen].

    For conducting proofs in practice, there remains to state lemmas and
    define tactics to assist the user in the manipulation of the formula
    produced by [wpgen]. Ultimately, the end-user only manipulates CFML's
    "x-tactics" (recall the first two chapters), without ever being
    required to understand how [wpgen] is defined.

    In other words, the contents of this chapter reveals the details
    that we work very hard to make completely invisible to the end user. *)

(* ################################################################# *)
(** * More Details *)

(* ================================================================= *)
(** ** Definition of [wpgen] for Term Rules *)

(** [wpgen] computes a heap predicate that has the same meaning as [wp].
    In essence, [wpgen] takes the form of a recursive function that,
    like [wp], expects a term [t] and a postcondition [Q], and produces
    a heap predicate. The function is recursively defined and its result
    is guided by the structure of the term [t].

    In essence, the definition of [wpgen] admits the following shape:

    Fixpoint wpgen (t:trm) (Q:val->hprop) : hprop :=
      match t with
      | trm_val v => ..
      | trm_seq t1 t2 => ..
      | trm_let x t1 t2 => ..
      | trm_var x => ..
      | trm_app t1 t2 => ..
      | trm_fun x t1 => ..
      | trm_fix f x t1 => ..
      | trm_if v0 t1 t2 => ..
      end).

    Our first goal is to figure out how to fill in the dots for each of the
    term constructors.

    The intention that guides us for filling the dot is the soundness theorem
    for [wpgen], which takes the following form:

      wpgen t Q ==> wp t Q

    This entailment asserts in particular that, if we are able to establish
    a statement of the form [H ==> wpgen t Q], then we can derive from it
    [H ==> wp t Q]. The latter is also equivalent to [triple t H Q].
    Thus, [wpgen] can be viewed as a practical tool to establish triples.

    Remark: the main difference between [wpgen] and a "traditional" weakest
    precondition generator (as the reader might have seen for Hoare logic)
    is that here we compute the weakest precondition of a raw term, that is,
    a term not annotated with any invariant or specification. *)

(* ----------------------------------------------------------------- *)
(** *** Definition of [wpgen] for Values *)

(** Consider first the case of a value [v]. Recall the reasoning
    rule for values in weakest-precondition style. *)

Parameter wp_val : forall v Q,
  Q v ==> wp (trm_val v) Q.

(** The soundness theorem for [wpgen] requires the entailment
    [wpgen (trm_val v) Q ==> wp (trm_val v) Q] to hold.

    To satisfy this entailment, according to the rule [wp_val],
    it suffices to define [wpgen (trm_val v) Q] as [Q v].

    Concretely, we fill in the first dots as follows:

    Fixpoint wpgen (t:trm) (Q:val->hprop) : hprop :=
      match t with
      | trm_val v => Q v
      ...
*)

(* ----------------------------------------------------------------- *)
(** *** Definition of [wpgen] for Functions *)

(** Consider the case of a function definition [trm_fun x t].
    Recall that the [wp] reasoning rule for functions is very
    similar to that for values. *)

Parameter wp_fun : forall x t1 Q,
  Q (val_fun x t1) ==> wp (trm_fun x t1) Q.

(** So, likewise, we can define [wpgen] for functions and for
    recursive functions as follows:

    Fixpoint wpgen (t:trm) (Q:val->hprop) : hprop :=
      match t with
      ...
      | trm_fun x t1   => Q (val_fun x t1)
      | trm_fix f x t1 => Q (val_fix f x t1)
      ...
*)

(** An important observation is that we here do not attempt to
    recursively compute [wpgen] over the body of the function.
    This is something that we could do, and that we will see how
    to achieve further on, yet we postpone it for now because it is
    relatively technical. In practice, if the program features a
    local function definition, the user may explicitly request the
    computation of [wpgen] over the body of that function. Thus,
    the fact that we do not recursively traverse functions bodies
    does not harm expressiveness. *)

(* ----------------------------------------------------------------- *)
(** *** Definition of [wpgen] for Sequence *)

(** Recall the [wp] reasoning rule for a sequence [trm_seq t1 t2]. *)

Parameter wp_seq : forall t1 t2 Q,
  wp t1 (fun v => wp t2 Q) ==> wp (trm_seq t1 t2) Q.

(** The intention is for [wpgen] to admit the same semantics as [wp].
    We thus expect the definition of [wpgen (trm_seq t1 t2) Q] to have a
    similar shape as [wp t1 (fun v => wp t2 Q)].

    We therefore define [wpgen (trm_seq t1 t2) Q] as
    [wpgen t1 (fun v => wpgen t2 Q)]. The definition of [wpgen]
    thus gets refined as follows:

    Fixpoint wpgen (t:trm) (Q:val->hprop) : hprop :=
      match t with
      ...
      | trm_seq t1 t2 => wpgen t1 (fun v => wpgen t2 Q)
      ...
*)

(* ----------------------------------------------------------------- *)
(** *** Definition of [wpgen] for Let-Bindings *)

(** The case of let bindings is similar to that of sequences,
    except that it involves a substitution. Recall the [wp] rule: *)

Parameter wp_let : forall x t1 t2 Q,
  wp t1 (fun v => wp (subst x v t2) Q) ==> wp (trm_let x t1 t2) Q.

(** We fill in the dots as follows:

    Fixpoint wpgen (t:trm) (Q:val->hprop) : hprop :=
      match t with
      ...
      | trm_let x t1 t2 => wpgen t1 (fun v => wpgen (subst x v t2) Q)
      ...

    One important observation to make at this point is that the
    function [wpgen] is no longer structurally recursive. Indeed,
    while the first recursive call to [wpgen] is invoked on [t1], which
    is a strict subterm of [t], the second call is invoked on
    [subst x v t2], which is not a strict subterm of [t].

    It is technically possible to convince Coq that the function [wpgen]
    terminates, yet with great effort. Alternatively, we can circumvent
    the problem altogether by casting the function in a form that makes
    it structurally recursive. Concretely, we will see further on how to
    add as argument to [wpgen] a substitution context (written [E]) to
    delay the computation of substitutions until the leaves of the recursion. *)

(* ----------------------------------------------------------------- *)
(** *** Definition of [wpgen] for Variables *)

(** We have seen no reasoning rules for establishing a triple for a program
    variable, that is, to prove [triple (trm_var x) H Q]. Indeed, [trm_var x]
    is a stuck term: its execution does not produce an output.

    While a source term may contain program variables, all these variables
    should get substituted away before the execution reaches them.

    In the case of the function [wpgen], a variable bound by let-binding
    get substituted while traversing that let-binding construct. Thus,
    if a free variable is reached by [wpgen], it means that this variable
    was originally a dangling free variable, and therefore that the initial
    source term was invalid.

    Although we have presented no reasoning rules for [triple (trm_var x) H Q]
    nor for [H ==> wp (trm_var x) Q], we nevertheless have to provide some
    meaningful definition for [wpgen (trm_var x) Q]. This definition should
    capture the fact that this case must not happen. The heap predicate
    [\[False]] captures this intention perfectly well.

    Fixpoint wpgen (t:trm) (Q:val->hprop) : hprop :=
      match t with
      ...
      | trm_var x => \[False]
      ...
*)

(** Remark: the definition of \[False] translates the fact that,
    technically, we could have stated a Separation Logic rule
    for free variables, using [False] as a premise [\[False]]
    as precondition. There are three canonical ways of presenting
    this rule, they are shown next. *)

Lemma wp_var : forall x Q,
  \[False] ==> wp (trm_var x) Q.
Proof using. intros. intros h Hh. destruct (hpure_inv Hh). false. Qed.

Lemma triple_var : forall x H Q,
  False ->
  triple (trm_var x) H Q.
Proof using. intros. false. Qed.

Lemma triple_var' : forall x Q,
  triple (trm_var x) \[False] Q.
Proof using. intros. rewrite <- wp_equiv. applys wp_var. Qed.

(** All these rules are correct, albeit totally useless. *)

(* ----------------------------------------------------------------- *)
(** *** Definition of [wpgen] for Function Applications *)

(** Consider an application in A-normal form, that is,
    an application of the form [trm_app v1 v2].

    We have seen [wp]-style rules to reason about the application of
    a known function, e.g. [trm_app (val_fun x t1) v2].
    However, if [v1] is an abstrat value (e.g., a Coq variable
    of type [val]), we have no reasoning rule at hand that applies.

    Thus, we will simply define [wpgen (trm_app v1 v2) Q] as
    [wp (trm_app v1 v2) Q]. In other words, to define [wpgen] for
    a function application, we fall back to the semantic definition
    of [wp]. We thus extend the definition of [wpgen] as follows.

    Fixpoint wpgen (t:trm) (Q:val->hprop) : hprop :=
      match t with
      ...
      | trm_app v1 v2 => wp (trm_app v1 v2) Q
      ...

    As we carry out verification proofs in practice, when reaching
    an application we will face a goal of the form:

    H ==> wpgen (trm_app v1 v2) Q

    By revealing the definition of [wpgen] on applications, we get:

    H ==> wp (trm_app v1 v2) Q

    Then, by exploiting the equivalence with triples, we obtain:

    triple (trm_app v1 v2) H Q

    Such a proof obligation can be discharged by invoking a specification
    triple for the function [v1].

    In other words, by falling back to the semantics definition when
    reaching a function application, we allow the user to choose which
    specification lemma to exploit for reasoning about this particular
    function application. *)

(** Remark: we assume throughout the course that terms are written
    in A-normal form. Nevertheless, we need to define [wpgen] even
    on terms that are not in A-normal form. One possibility is
    to map all these terms to [\[False]]. In the specific case of an
    application of the form [trm_app t1 t2] where [t1] and [t2] are
    not both values, it is still correct to define [wpgen (trm_app t1 t2))]
    as [wp (trm_app t1 t2)]. So, we need not bother checking in the
    definition of [wpgen] that the arguments of [trm_app] are actually
    values. *)

(** Thus, the most concise definition for [wpgen] on applications is:

    Fixpoint wpgen (t:trm) (Q:val->hprop) : hprop :=
      match t with
      ...
      | trm_app t1 t2 => wp t Q
      ...
*)

(* ----------------------------------------------------------------- *)
(** *** Definition of [wpgen] for Conditionals *)

(** The last remaining case is that for conditionals. Recall the
    [wp]-style reasoning rule stated using a Coq conditional. *)

Parameter wp_if : forall (b:bool) t1 t2 Q,
  (if b then (wp t1 Q) else (wp t2 Q)) ==> wp (trm_if (val_bool b) t1 t2) Q.

(** We need to define [wpgen] for all conditionals in A-normal form, i.e.,
    all terms of the form [trm_if (trm_val v0) t1 t2], where [v0] could be a
    value of unknown shape. Typically, a program may feature a conditional
    [trm_if (trm_var x) t1 t2] that, after substitution for [x], becomes
    [trm_if (trm_val v) t1 t2], for some abstract [v] of type [val] that
    we might not yet know to be a boolean value.

    Yet, the rule [wp_if] only applies when the first argument of [trm_if]
    is syntactically a boolean value [b]. To handle this mismatch, we
    set up [wpgen] to pattern-match a conditional as [trm_if t0 t1 t2],
    and then express using a Separation Logic existential quantifier that
    there should exist a boolean [b] such that [t0 = trm_val (val_bool b)].

    This way, we delay the moment at which the argument of the conditional
    needs to be shown to be a boolean value. The formal definition is:

    Fixpoint wpgen (t:trm) (Q:val->hprop) : hprop :=
      match t with
      ...
      | trm_if t0 t1 t2 =>
          \exists (b:bool), \[t0 = trm_val (val_bool b)]
            \* (if b then (wpgen t1) Q else (wpgen t2) Q)
      ...
*)

(* ----------------------------------------------------------------- *)
(** *** Summary of the Definition of [wpgen] for Term Rules *)

(** In summary, we have defined:

    Fixpoint wpgen (t:trm) (Q:val->hprop) : hprop :=
      match t with
      | trm_val v => Q v
      | trm_fun x t1 => Q (val_fun x t)
      | trm_fix f x t1 => Q (val_fix f x t)
      | trm_seq t1 t2 => wpgen t1 (fun v => wpgen t2 Q)
      | trm_let x t1 t2 => wpgen t1 (fun v => wpgen (subst x v t2) Q)
      | trm_var x => \[False]
      | trm_app v1 v2 => wp t Q
      | trm_if t0 t1 t2 =>
          \exists (b:bool), \[t0 = trm_val (val_bool b)]
            \* (if b then (wpgen t1) Q else (wpgen t2) Q)
      end.

    As pointed out earlier, this definition is not structurally recursive
    and thus not accepted by Coq, due to the recursive call
    [wpgen (subst x v t2) Q]. Our next step is to fix this issue. *)

(* ================================================================= *)
(** ** Computing with [wpgen] *)

(** [wpgen] is not structurally recursive because of the substitutions
    that takes places in-between recursive calls. To fix this, we are
    going to delay the substitutions until the leaves of the recursion.

    To that end, we introduce a substitution context, written [E], to
    record the substitutions that should have been performed.

    Concretely, we modify the function to take the form [wpgen E t],
    where [E] denotes a set of bindings from variables to values.
    The intention is that [wpgen E t] computes the weakest precondition
    for the term [isubst E t], which denotes the result of substituting
    all bindings from E inside the term [t]. *)

(* ----------------------------------------------------------------- *)
(** *** Definition of Contexts and Operations on Them *)

(** The simplest way to define a context [E] is as an association
    list relating variables to values. *)

Definition ctx : Type := list (var*val).

(** Before we explain how to revisit the definition of [wpgen] using
    contexts, we need to define the "iterated substitution" operation.
    This operation, written [isubst E t], describes the substitution
    of all the bindings form [E] inside a term [t].

    The definition of iterated substitution is relatively standard:
    we traverse the term recursively and, when reaching a variable,
    we perform a lookup in the context [E]. We need to take care
    to respect variable shadowing. To that end, when traversing a
    binder that binds a variable [x], we remove all occurrences of [x]
    that might exist in [E].

    The formal definition of [isubst] involves two auxiliary functions:
    lookup and removal on association lists.

    The definition of the operation [lookup x E] on association lists
    is standard. It returns an option on a value. *)

Fixpoint lookup (x:var) (E:ctx) : option val :=
  match E with
  | nil => None
  | (y,v)::E1 => if var_eq x y
                   then Some v
                   else lookup x E1
  end.

(** The definition of the removal operation, written [rem x E], is
    also standard. It returns a filtered context. *)

Fixpoint rem (x:var) (E:ctx) : ctx :=
  match E with
  | nil => nil
  | (y,v)::E1 =>
      let E1' := rem x E1 in
      if var_eq x y then E1' else (y,v)::E1'
  end.

(** The definition of the operation [isubst E t] can then be expressed
    as a recursive function over the term [t]. It invokes [lookup x E]
    when reaching a variable [x]. It invokes [rem x E] when traversing
    a binding on the name [x]. *)

Fixpoint isubst (E:ctx) (t:trm) : trm :=
  match t with
  | trm_val v =>
       v
  | trm_var x =>
       match lookup x E with
       | None => t
       | Some v => v
       end
  | trm_fun x t1 =>
       trm_fun x (isubst (rem x E) t1)
  | trm_fix f x t1 =>
       trm_fix f x (isubst (rem x (rem f E)) t1)
  | trm_app t1 t2 =>
       trm_app (isubst E t1) (isubst E t2)
  | trm_seq t1 t2 =>
       trm_seq (isubst E t1) (isubst E t2)
  | trm_let x t1 t2 =>
       trm_let x (isubst E t1) (isubst (rem x E) t2)
  | trm_if t0 t1 t2 =>
       trm_if (isubst E t0) (isubst E t1) (isubst E t2)
  end.

(** Remark: it is also possible to define the substitution by iterating
    the unary substitution [subst] over the list of bindings from [E].
    However, this alternative approach yields a less efficient function
    and leads to more complicated proofs. *)

(** In what follows, we present the definition of [wpgen E t] case by
    case. Throughout these definitions, recall that [wpgen E t] is
    interpreted as the weakest precondition of [isubst E t]. *)

(* ----------------------------------------------------------------- *)
(** *** [wpgen]: the Let-Binding Case *)

(** When [wpgen] traverses a let-binding, rather than eagerly performing
    a substitution, it simply extends the current context.

    Concretely, a call to [wpgen E (trm_let x t1 t2)] triggers a recursive
    call to [wpgen ((x,v)::E) t2]. The corresponding definition is:

  Fixpoint wpgen (E:ctx) (t:trm) : formula :=
    mkstruct (match t with
      ...
      | trm_let x t1 t2 => fun Q =>
           (wpgen E t1) (fun v => wpgen ((x,v)::E) t2)
      ...
      ) end.
*)

(* ----------------------------------------------------------------- *)
(** *** [wpgen]: the Variable Case *)

(** When [wpgen] reaches a variable, it lookups for a binding on the
    variable [x] inside the context [E]. Concretely, the evaluation
    of [wpgen E (trm_var x)] triggers a call to [lookup x E].

    If the context [E] binds the variable [x] to some value [v], then
    the operation [lookup x E] returns [Some v]. In that case, [wpgen]
    returns the weakest precondition for that value [v], that is, [Q v].

    Otherwise, if [E] does not bind [x], the lookup operation returns [None].
    In that case, [wpgen] returns [\[False]], which we have explained to be
    the weakest precondition for a stuck program.

  Fixpoint wpgen (E:ctx) (t:trm) : formula :=
    mkstruct (match t with
      ...
      | trm_var x => fun Q =>
           match lookup x E with
           | Some v => Q v
           | None => \[False]
           end
      ...
      ) end.
*)

(* ----------------------------------------------------------------- *)
(** *** [wpgen]: the Application Case *)

(** In the previous definition of [wpgen] (the one without contexts),
    we argued that, in the case where [t] denotes an application, the
    result of [wpgen t Q] should be simply [wp t Q].

    In the definition of [wpgen] with contexts, the interpretation of
    [wpgen E t] is the weakest precondition of the term [isubst E t]
    (which denotes the result of substituting variables from [E] in [t]).

    When [t] is an application, we thus define [wpgen E t] as the
    formula [fun Q => wp (isubst E t) Q], which simplifies to
    [wp (isubst E t)] after eliminating the eta-expansion.

  Fixpoint wpgen (t:trm) : formula :=
    mkstruct (match t with
      ...
      | trm_app v1 v2 => wp (isubst E t)
      ..
*)

(* ----------------------------------------------------------------- *)
(** *** [wpgen]: the Function Definition Case *)

(** Consider the case where [t] is a function definition, for example
    [trm_fun x t1]. Here again, the formula [wpgen E t] is interpreted
    as the weakest precondition of [isubst E t].

    By unfolding the definition of [isubst] in the case where [t] is
    [trm_fun x t1], we obtain [trm_fun x (isubst (rem x E) t1)].

    The corresponding value is [trm_val x (isubst (rem x E) t1)].
    The weakest precondition for that value is
    [fun Q => Q (val_fun x (isubst (rem x E) t1))].

    Thus, [wpgen E t] handles functions, and recursive functions,
    as follows:

  Fixpoint wpgen (E:ctx) (t:trm) : formula :=
    mkstruct (match t with
      ...
      | trm_fun x t1 => fun Q => Q (val_fun x (isubst (rem x E) t1))
      | trm_fix f x t1 => fun Q => Q (val_fix f x (isubst (rem x (rem f E)) t1))
      ...
      ) end.
*)

(* ----------------------------------------------------------------- *)
(** *** [wpgen]: at Last, an Executable Function *)

Module WpgenExec1.

(** At last, we arrive to a definition of [wpgen] that type-checks in Coq,
    and that can be used to effectively compute weakest preconditions in
    Separation Logic. *)

Fixpoint wpgen (E:ctx) (t:trm) (Q:val->hprop) : hprop :=
  match t with
  | trm_val v => Q v
  | trm_fun x t1 => Q (val_fun x (isubst (rem x E) t1))
  | trm_fix f x t1 => Q (val_fix f x (isubst (rem x (rem f E)) t1))
  | trm_seq t1 t2 => wpgen E t1 (fun v => wpgen E t2 Q)
  | trm_let x t1 t2 => wpgen E t1 (fun v => wpgen ((x,v)::E) t2 Q)
  | trm_var x =>
       match lookup x E with
       | Some v => Q v
       | None => \[False]
       end
  | trm_app v1 v2 => wp (isubst E t) Q
  | trm_if t0 t1 t2 =>
      \exists (b:bool), \[t0 = trm_val (val_bool b)]
        \* (if b then (wpgen E t1) Q else (wpgen E t2) Q)
  end.

(** Compared with the presentation using the form [wpgen t], the new
    presentation using the form [wpgen E t] has the main benefits that
    it is structurally recursive, thus easy to define in Coq.
    Moreover, it is algorithmically more efficient in general, because
    it performs substitutions lazily rather than eagerly. *)

(** Let us state the soundness theorem and its corollary for establishing
    triples for functions. *)

Parameter wpgen_sound : forall E t Q,
   wpgen E t Q ==> wp (isubst E t) Q.

(** The entailment above asserts in particular that if we can derive
    [triple t H Q] by proving [H ==> wpgen t Q]. *)

(** A useful corrolary combines the soundness theorem with the rule
    [triple_app_fun], which allows establishing triples for functions.
    Recall the rule [triple_app_fun] from [Rules]. *)

Parameter triple_app_fun : forall x v1 v2 t1 H Q,
  v1 = val_fun x t1 ->
  triple (subst x v2 t1) H Q ->
  triple (trm_app v1 v2) H Q.

(** Reformulating the rule above into a rule for [wpgen] takes 3 steps.

    First, we rewrite the premise [triple (subst x v2 t1) H Q] using [wp].
    It becomes [H ==> wp (subst x v2 t1) Q].

    Second, we observe that the term [subst x v2 t1] is equal to
    [isubst ((x,v2)::nil) t1]. (This equality is captured by the lemma
    [subst_eq_isubst_one] proved in the bonus section of the chapter.)
    Thus, the heap predicate [wp (subst x v2 t1) Q] is equivalent to
    [wp (isubst ((x,v2)::nil) t1)].

    Third, according to [wpgen_sound], the predicate
    [wp (isubst ((x,v2)::nil) t1)] is entailed by [wpgen ((x,v2)::nil) t1].
    Thus, we can use the latter as premise in place of the former.
    We thereby obtain the following lemma. *)

Parameter triple_app_fun_from_wpgen : forall v1 v2 x t1 H Q,
  v1 = val_fun x t1 ->
  H ==> wpgen ((x,v2)::nil) t1 Q ->
  triple (trm_app v1 v2) H Q.

(* ----------------------------------------------------------------- *)
(** *** Executing [wpgen] on a Concrete Program *)

Import ExamplePrograms.

(** Let us exploit [triple_app_fun_from_wpgen] to demonstrate the
    computation of [wpgen] on a practical program.

    Recall the function [incr] (defined in Rules), and its
    specification, whose statement appears below. *)

Lemma triple_incr : forall (p:loc) (n:int),
  triple (trm_app incr p)
    (p ~~> n)
    (fun _ => p ~~> (n+1)).
Proof using.
  intros. applys triple_app_fun_from_wpgen. { reflexivity. }
  simpl. (* Read the goal here... *)
Abort.

(** The goal takes the form [H ==> wpgen body Q], where [H] denotes
    the precondition, [Q] the postcondition, and [body] the body of
    the function [incr].

    Observe the invocations of [wp] on the application of primitive
    operations.

    Observe that the goal is nevertheless somewhat hard to relate
    to the original program.

    In what follows, we explain how to remedy the situation, and
    set up [wpgen] is such a way that its output is human-readable,
    moreover resembles the original source code. *)

End WpgenExec1.

(* ================================================================= *)
(** ** Optimizing the Readability of [wpgen] Output *)

(** To improve the readability of the formulae produced by [wpgen],
    we take the following 3 steps:

    - first, we modify the presentation of [wpgen] so that the
      [fun (Q:val->hprop) =>] appears insides the branches of the
      [match t with] rather than around it,
    - second, we introduce one auxiliary definition for each branch
      of the [match t with],
    - third, we introduce one piece of notation for each of these
      auxiliary definitions. *)

(* ----------------------------------------------------------------- *)
(** *** Reability Step 1: Moving the Function below the Branches. *)

(** We distribute the [fun Q] into the branches of the [match t].
    Concretely, we change from:

 Fixpoint wpgen (E:ctx) (t:trm) (Q:val->hprop) : hprop :=
   match t with
   | trm_val v     =>  Q v
   | trm_fun x t1  =>  Q (val_fun x (isubst (rem x E) t1))
   ...
   end.

    to the equivalent form:

 Fixpoint wpgen (E:ctx) (t:trm) : (val->hprop)->hprop :=
   match t with
   | trm_val v     =>  fun (Q:val->hprop) => Q v
   | trm_fun x t1  =>  fun (Q:val->hprop) => Q (val_fun x (isubst (rem x E) t1))
   ...
   end.
*)

(** The result type of [wpgen E t] is [(val->hprop)->hprop].
    Thereafter, we let [formula] be a shorthand for this type. *)

Definition formula : Type := (val->hprop)->hprop.

(* ----------------------------------------------------------------- *)
(** *** Readability Steps 2 and 3, Illustrated on the Case of Sequences *)

(** We introduce auxiliary definitions to denote the result of each of the
    branches of the [match t] construct. Concretely, we change from:

    Fixpoint wpgen (E:ctx) (t:trm) : formula :=
      match t with
      ...
      | trm_seq t1 t2 =>  fun Q => (wpgen E t1) (fun v => wpgen E t2 Q)
      ...
      end.

    to the equivalent form:

    Fixpoint wpgen (E:ctx) (t:trm) : formula :=
      match t with
      ...
      | trm_seq t1 t2 =>  wpgen_seq (wpgen E t1) (wpgen E t2)
      ...
     end.

    where [wpgen_seq] is defined as shown below.
*)

Definition wpgen_seq (F1 F2:formula) : formula := fun Q =>
  F1 (fun v => F2 Q).

(** Remark: above, [F1] and [F2] denote the results of the recursive calls,
    [wpgen E t1] and [wpgen E t2], respectively.

    With the above definitions, [wgpen E (trm_seq t1 t2)]
    evaluates to [wp_seq (wpgen E t1) (wpgen E t2)]. *)

(** Finally, we introduce a piece of notation for each case. In the case
    of the sequence, we set up the notation defined next to so that any
    formula of the form [wpgen_seq F1 F2] gets displayed as [Seq F1 ; F2 ]. *)

Notation "'Seq' F1 ; F2" :=
  ((wpgen_seq F1 F2))
  (at level 68, right associativity,
   format "'[v' 'Seq'  '[' F1 ']'  ';'  '/'  '[' F2 ']' ']'").

(** Thanks to this notation, the [wpgen] of a sequence [t1 ; t2] displays as
    [Seq F1 ; F2] where [F1] and [F2] denote the [wpgen] of [t1] and [t2],
    respectively. *)

(* ----------------------------------------------------------------- *)
(** *** Readability Step 2: Auxiliary Definitions for other Constructs *)

(** We generalize the approach illustrated for sequences to every other
    term construct. The corresponding definitions are stated below.
    It is not required to understand the details in this subsection. *)

Definition wpgen_val (v:val) : formula := fun Q =>
  Q v.

Definition wpgen_let (F1:formula) (F2of:val->formula) : formula := fun Q =>
  F1 (fun v => F2of v Q).

Definition wpgen_if (t:trm) (F1 F2:formula) : formula := fun Q =>
  \exists (b:bool), \[t = trm_val (val_bool b)] \* (if b then F1 Q else F2 Q).

Definition wpgen_fail : formula := fun Q =>
  \[False].

Definition wpgen_var (E:ctx) (x:var) : formula :=
  match lookup x E with
  | None => wpgen_fail
  | Some v => wpgen_val v
  end.

(** The new definition of [wpgen] reads as follows. *)

Module WpgenExec2.

Fixpoint wpgen (E:ctx) (t:trm) : formula :=
  match t with
  | trm_val v => wpgen_val v
  | trm_var x => wpgen_var E x
  | trm_fun x t1 => wpgen_val (val_fun x (isubst (rem x E) t1))
  | trm_fix f x t1 => wpgen_val (val_fix f x (isubst (rem x (rem f E)) t1))
  | trm_app t1 t2 => wp (isubst E t)
  | trm_seq t1 t2 => wpgen_seq (wpgen E t1) (wpgen E t2)
  | trm_let x t1 t2 => wpgen_let (wpgen E t1) (fun v => wpgen ((x,v)::E) t2)
  | trm_if t0 t1 t2 => wpgen_if (isubst E t0) (wpgen E t1) (wpgen E t2)
  end.

(** This definition is, up to unfolding of the new intermediate definitions,
    totally equivalent to the previous one. We will prove the soundness
    result and its corollary further on. *)

Parameter wpgen_sound : forall E t Q,
   wpgen E t Q ==> wp (isubst E t) Q.

Parameter triple_app_fun_from_wpgen : forall v1 v2 x t1 H Q,
  v1 = val_fun x t1 ->
  H ==> wpgen ((x,v2)::nil) t1 Q ->
  triple (trm_app v1 v2) H Q.

End WpgenExec2.

(* ----------------------------------------------------------------- *)
(** *** Readability Step 3: Notation for Auxiliary Definitions *)

(** We generalize the notation introduced for sequences to every other
    term construct. The corresponding notation is defined below.
    It is not required to understand the details from this subsection.

    To avoid conflicts with other existing notation, we write
    [Let'] and [If'] in place of [Let] and [If].

    Here again, it is not required to understand all the details. *)

Declare Scope wpgen_scope.

Notation "'Val' v" :=
  ((wpgen_val v))
  (at level 69) : wpgen_scope.

Notation "'Let'' x ':=' F1 'in' F2" :=
  ((wpgen_let F1 (fun x => F2)))
  (at level 69, x ident, right associativity,
  format "'[v' '[' 'Let''  x  ':='  F1  'in' ']'  '/'  '[' F2 ']' ']'")
  : wpgen_scope.

Notation "'If'' b 'Then' F1 'Else' F2" :=
  ((wpgen_if b F1 F2))
  (at level 69) : wpgen_scope.

Notation "'Fail'" :=
  ((wpgen_fail))
  (at level 69) : wpgen_scope.

(** In addition, we introduce handy notation of the result of [wpgen t]
    where [t] denotes an application. *)

Notation "'App' f v1 " :=
  ((wp (trm_app f v1)))
  (at level 68, f, v1 at level 0) : wpgen_scope.

(* ----------------------------------------------------------------- *)
(** *** Test of [wpgen] with Notation. *)

(** Consider again the example of [incr]. *)

Module WPgenWithNotation.
Import ExamplePrograms WpgenExec2.
Open Scope wpgen_scope.

Lemma triple_incr : forall (p:loc) (n:int),
  triple (trm_app incr p)
    (p ~~> n)
    (fun _ => p ~~> (n+1)).
Proof using.
  intros. applys triple_app_fun_from_wpgen. { reflexivity. }
  simpl. (* Read the goal here... It is of the form [H ==> F Q],
            where [F] vaguely looks like the code of the body of [incr]. *)
Abort.

(** Up to proper tabulation, alpha-renaming, and removal of
    parentheses (and dummy quotes after [Let] and [If]),
    the formula [F] reads as:

      Let n := App val_get p in
      Let m := App (val_add n) 1 in
      App (val_set p) m
*)

(** With the introduction of intermediate definitions for [wpgen] and
    the introduction of associated notations for each term construct,
    what we achieved is that the output of [wpgen] is, for any input term
    [t], a human readable formula whose display closely resembles the
    syntax source code of the term [t]. *)

End WPgenWithNotation.

(* ================================================================= *)
(** ** Extension of [wpgen] to Handle Structural Rules *)

(** The definition of [wpgen] proposed so far integrates the logic of
    the reasoning rules for terms, however it lacks support for conveniently
    exploiting the structural rules of the logic.

    We fix this next, by showing how to tweak the definition of [wpgen] in
    such a way that, by construction, it satisfies both:
    - the frame rule, which asserts
      [(wpgen t Q) \* H ==> wpgen t (Q \*+ H)],
    - and the rule of consequence, which asserts that [Q1 ===> Q2] implies
      [wpgen t Q1 ==> wpgen t Q2].

*)

(* ----------------------------------------------------------------- *)
(** *** Introduction of [mkstruct] in the Definition of [wpgen] *)

(** Recall from the previous chapter the statement of the frame rule
    in [wp]-style. *)

Parameter wp_frame : forall t H Q,
  (wp t Q) \* H ==> wp t (Q \*+ H).

(** We would like [wpgen] to satisfy the same rule, so that we can
    exploit the frame rule while reasoning about a program using
    the heap predicate produced by [wpgen].

    With the definition of [wpgen] set up so far, it is possible
    to prove, for any concrete term [t], that the frame property
    [(wpgen t Q) \* H ==> wpgen t (Q \*+ H)] holds.
    However, establishing this result requires an induction over
    the entire structure of the term [t]---a lot of tedious work.

    Instead, we are going to tweak the definition of [wpgen] so as to
    produce, at every step of the recursion, a special token to capture
    the idea that whatever the details of the output predicate produced
    by [wpgen], this predicate does satisfy the frame property. *)

(** We achieve this magic by introducing a predicate called [mkstruct],
    and inserting it at the head of the output produced by [wpgen]
    (and all of its recursive invocation) as follows:

    Fixpoint wpgen (E:ctx) (t:trm) : (val->hprop)->hprop :=
      mkstruct (
        match t with
        | trm_val v => wpgen_val v
        ...
        end).

    The interest of the insertion of [mkstruct] above is that every result
    of a computation of [wpgen t] on a concrete term [t] is, by construction,
    of the form [mkstruct F] for some argument [F].

    There remains to investigate how [mkstruct] should be defined. *)

(* ----------------------------------------------------------------- *)
(** *** Properties of [mkstruct] *)

Module MkstructProp.

(** Let us state the properties that [mkstruct] should satisfy. *)

(** Because [mkstruct] appears between the prototype and the [match]
    in the body of [wpgen], the predicate [mkstruct] must have type
    [formula->formula]. *)

Parameter mkstruct : formula->formula.

(** There remains to find a suitable definition for [mkstruct] that enables
    the frame property and the consequence property. These properties can
    be stated by mimicking the rules [wp_frame] and [wp_conseq]. *)

Parameter mkstruct_frame : forall (F:formula) H Q,
  (mkstruct F Q) \* H ==> mkstruct F (Q \*+ H).

Parameter mkstruct_conseq : forall (F:formula) Q1 Q2,
  Q1 ===> Q2 ->
  mkstruct F Q1 ==> mkstruct F Q2.

(** In addition, it should be possible to erase [mkstruct] from the head
    of the output produced [wpgen t] when we do not need to apply any
    structural rule. In other words, we need to be able to prove
    [H ==> mkstruct F Q] by proving [H ==> F Q], for any [H].
    This erasure property is captured by the following entailment. *)

Parameter mkstruct_erase : forall (F:formula) Q,
  F Q ==> mkstruct F Q.

(** Moreover, [mkstruct] should be monotone with respect to the formula:
    if [F1] is stronger than [F2], then [mkstruct F1] should be stronger
    then [mkstruct F2]. *)

Parameter mkstruct_monotone : forall F1 F2 Q,
  (forall Q, F1 Q ==> F2 Q) ->
  mkstruct F1 Q ==> mkstruct F2 Q.

End MkstructProp.

(* ----------------------------------------------------------------- *)
(** *** Realization of [mkstruct] *)

(** Fortunately, it turns out that there exists a predicate [mkstruct]
    satisfying the four required properties. To begin with, let us just
    pull out of our hat a definition of [mkstruct] that works. *)

Definition mkstruct (F:formula) : formula :=
  fun (Q:val->hprop) => \exists Q1 H, F Q1 \* H \* \[Q1 \*+ H ===> Q].

(** We postpone to a bonus section the discussion of why it works and of how
    one could have guessed this definition. Again, it really does not matter
    the details of the definition of [mkstruct]. All that matters is that
    [mkstruct] satisfies the three required properties: [mkstruct_frame],
    [mkstruct_conseq], and [mkstruct_erase]. Let us establish these properties
    for the definition considered. (Proof details can be skipped over.) *)

Lemma mkstruct_frame : forall F H Q,
  (mkstruct F Q) \* H ==> mkstruct F (Q \*+ H).
Proof using.
  intros. unfold mkstruct. xpull; intros Q' H' M. xsimpl. xchange M.
Qed.

Lemma mkstruct_conseq : forall F Q1 Q2,
  Q1 ===> Q2 ->
  mkstruct F Q1 ==> mkstruct F Q2.
Proof using.
  introv WQ. unfold mkstruct. xpull; intros Q' H' M.
  xsimpl. xchange M. xchange WQ.
Qed.

Lemma mkstruct_erase : forall F Q,
  F Q ==> mkstruct F Q.
Proof using. intros. unfold mkstruct. xsimpl. xsimpl. Qed.

Lemma mkstruct_monotone : forall F1 F2 Q,
  (forall Q, F1 Q ==> F2 Q) ->
  mkstruct F1 Q ==> mkstruct F2 Q.
Proof using.
  introv WF. unfolds mkstruct. xpull. intros Q' H M.
  xchange WF. xsimpl Q'. applys M.
Qed.

(** An interesting property of [mkstruct] is it has no effect on a
    formula of the form [wp t]. Intuitively, such a formula already
    satisfies all the structural reasoning rules, hence adding
    [mkstruct] to it does not increase its expressive power. *)

Lemma mkstruct_wp : forall t,
  mkstruct (wp t) = (wp t).
Proof using.
  intros. applys fun_ext_1. intros Q. applys himpl_antisym.
  { unfold mkstruct. xpull. intros H Q' M. applys wp_conseq_frame M. }
  { applys mkstruct_erase. }
Qed.

(** Another interesting property of [mkstruct] is its idempotence
    property, that is, it is such that [mkstruct (mkstruct F) = mkstruct F].

    Idempotence asserts that applying the predicate [mkstruct] more than
    once does not provide more expressiveness than applying it just once.

    Intuitively, idempotence reflects in particular the fact that two nested
    applications of the rule of consequence can always be combined into a
    single application of that rule (due to the transitivity of entailment);
    and that, similarly, two nested applications of the frame rule can always
    be combined into a single application of that rule (framing on [H1] then
    framing on [H2] is equivalent to framing on [H1 \* H2]). *)

(** **** Exercise: 3 stars, standard, especially useful (mkstruct_idempotent)

    Complete the proof of the idempotence of [mkstruct].
    Hint: leverage [xpull] and [xsimpl]. *)

Lemma mkstruct_idempotent : forall F,
  mkstruct (mkstruct F) = mkstruct F.
Proof using.
  intros. apply fun_ext_1. intros Q. applys himpl_antisym.
  (* FILL IN HERE *) Admitted.

(** [] *)

(* ----------------------------------------------------------------- *)
(** *** Definition of [wpgen] that Includes [mkstruct] *)

(** Our final definition of [wpgen] refines the previous one by
    inserting the [mkstruct] predicate to the front of the
    [match t with] construct. *)

Fixpoint wpgen (E:ctx) (t:trm) : formula :=
  mkstruct (match t with
  | trm_val v => wpgen_val v
  | trm_var x => wpgen_var E x
  | trm_fun x t1 => wpgen_val (val_fun x (isubst (rem x E) t1))
  | trm_fix f x t1 => wpgen_val (val_fix f x (isubst (rem x (rem f E)) t1))
  | trm_app t1 t2 => wp (isubst E t)
  | trm_seq t1 t2 => wpgen_seq (wpgen E t1) (wpgen E t2)
  | trm_let x t1 t2 => wpgen_let (wpgen E t1) (fun v => wpgen ((x,v)::E) t2)
  | trm_if t0 t1 t2 => wpgen_if (isubst E t0) (wpgen E t1) (wpgen E t2)
  end).

(** Again, we assert the soundness theorem and its corollary,
    and we postpone the proof. *)

Parameter wpgen_sound : forall E t Q,
   wpgen E t Q ==> wp (isubst E t) Q.

Parameter triple_app_fun_from_wpgen : forall v1 v2 x t1 H Q,
  v1 = val_fun x t1 ->
  H ==> wpgen ((x,v2)::nil) t1 Q ->
  triple (trm_app v1 v2) H Q.

(* ----------------------------------------------------------------- *)
(** *** Notation for [mkstruct] and Test *)

(** To avoid clutter in reading the output of [wpgen], we introduce a
    lightweight shorthand to denote [mkstruct F], allowing it to display
    simply as [`F]. *)

Notation "` F" := (mkstruct F) (at level 10, format "` F") : wpgen_scope.

(** Let us test again the readability of the output of [wpgen] on
    a concrete example. *)

Module WPgenWithMkstruct.
Import ExamplePrograms.
Open Scope wpgen_scope.

Lemma triple_incr : forall (p:loc) (n:int),
  triple (trm_app incr p)
    (p ~~> n)
    (fun _ => p ~~> (n+1)).
Proof using.
  intros. applys triple_app_fun_from_wpgen. { reflexivity. }
  simpl.
Abort.

(** Up to proper tabulation, alpha-renaming, and removal of
    parentheses (and dummy quotes after [Let] and [If]),
    [F] reads as:

    `Let n := `(App val_get p) in
    `Let m := `(App (val_add n) 1) in
    `App (val_set p) m
*)

End WPgenWithMkstruct.

(* ================================================================= *)
(** ** Lemmas for Handling [wpgen] Goals *)

(** The last major step of the setup of our Separation Logic
    based verification framework consists of lemmas and tactics
    to assist in the processing of formulas produced by [wpgen].
    For each term construct, and for [mkstruct], we introduce
    a dedicated lemma, called "x-lemma", to help with the
    elimination of the construct. *)

(** [xstruct_lemma] is a reformulation of [mkstruct_erase]. *)

Lemma xstruct_lemma : forall F H Q,
  H ==> F Q ->
  H ==> mkstruct F Q.
Proof using. introv M. xchange M. applys mkstruct_erase. Qed.

(** [xval_lemma] reformulates the definition of [wpgen_val].
    It just unfolds the definition. *)

Lemma xval_lemma : forall v H Q,
  H ==> Q v ->
  H ==> wpgen_val v Q.
Proof using. introv M. applys M. Qed.

(** [xlet_lemma] reformulates the definition of [wpgen_let].
    It just unfolds the definition. *)

Lemma xlet_lemma : forall H F1 F2of Q,
  H ==> F1 (fun v => F2of v Q) ->
  H ==> wpgen_let F1 F2of Q.
Proof using. introv M. xchange M. Qed.

(** Likewise, [xseq_lemma] reformulates [wpgen_seq]. *)

Lemma xseq_lemma : forall H F1 F2 Q,
  H ==> F1 (fun v => F2 Q) ->
  H ==> wpgen_seq F1 F2 Q.
Proof using. introv M. xchange M. Qed.

(** [xapp_lemma] applies to goals produced by [wpgen] on an
    application. In such cases, the proof obligation is of the form
    [H ==> wp t Q].

    [xapp_lemma] reformulates the frame-consequence rule, and
    states the premise of the rule using a [triple], because
    triples are used for stating specification lemmas. *)

Lemma xapp_lemma : forall t Q1 H1 H2 H Q,
  triple t H1 Q1 ->
  H ==> H1 \* H2 ->
  Q1 \*+ H2 ===> Q ->
  H ==> wp t Q.
Proof using.
  introv M WH WQ. rewrite wp_equiv. applys* triple_conseq_frame M.
Qed.

(** [xwp_lemma] is another name for [triple_app_fun_from_wpgen].
    It is used for establishing a triple for a function application. *)

Lemma xwp_lemma : forall v1 v2 x t1 H Q,
  v1 = val_fun x t1 ->
  H ==> wpgen ((x,v2)::nil) t1 Q ->
  triple (trm_app v1 v2) H Q.
Proof using. introv M1 M2. applys* triple_app_fun_from_wpgen. Qed.

(* ================================================================= *)
(** ** An Example Proof *)

(** Let us illustrate how the "x-lemmas" help clarifying verification
    proof scripts. *)

Module ProofsWithXlemmas.
Import ExamplePrograms.
Open Scope wpgen_scope.

Lemma triple_incr : forall (p:loc) (n:int),
  triple (trm_app incr p)
    (p ~~> n)
    (fun _ => p ~~> (n+1)).
Proof using.
  intros.
  applys xwp_lemma. { reflexivity. }
  (* Here the [wpgen] function computes. *)
  simpl.
  (* Observe how each node begin with [mkstruct].
     Observe how program variables are all eliminated. *)
  applys xstruct_lemma.
  applys xlet_lemma.
  applys xstruct_lemma.
  applys xapp_lemma. { apply triple_get. } { xsimpl. }
  xpull; intros ? ->.
  applys xstruct_lemma.
  applys xlet_lemma.
  applys xstruct_lemma.
  applys xapp_lemma. { apply triple_add. } { xsimpl. }
  xpull; intros ? ->.
  applys xstruct_lemma.
  applys xapp_lemma. { apply triple_set. } { xsimpl. }
  xsimpl.
Qed.

(** **** Exercise: 2 stars, standard, especially useful (triple_succ_using_incr_with_xlemmas)

    Using x-lemmas, verify the proof of [triple_succ_using_incr].
    (The proof was carried out using triples in chapter [Rules].) *)

Lemma triple_succ_using_incr_with_xlemmas : forall (n:int),
  triple (trm_app succ_using_incr n)
    \[]
    (fun v => \[v = n+1]).
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

End ProofsWithXlemmas.

(* ================================================================= *)
(** ** Making Proof Scripts More Concise *)

(** For each x-lemma, we introduce a dedicated tactic to apply
    that lemma and perform the associated bookkeeping. *)

(** [xstruct] eliminates the leading [mkstruct]. *)

Tactic Notation "xstruct" :=
  applys xstruct_lemma.

(** [val], [xseq] and [xlet] invoke the corresponding x-lemmas,
   after calling [xstruct] if a leading [mkstruct] is in the way. *)

Tactic Notation "xstruct_if_needed" :=
  try match goal with |- ?H ==> mkstruct ?F ?Q => xstruct end.

Tactic Notation "xval" :=
  xstruct_if_needed; applys xval_lemma.

Tactic Notation "xlet" :=
  xstruct_if_needed; applys xlet_lemma.

Tactic Notation "xseq" :=
  xstruct_if_needed; applys xseq_lemma.

(** [xapp_nosubst] applys [xapp_lemma], after calling [xseq] or [xlet]
    if applicable. (We will subsequently define [xapp] as an enhanced version
    of [xapp_nosusbt] that is able to automatically perform substitutions. *)

Tactic Notation "xseq_xlet_if_needed" :=
  try match goal with |- ?H ==> mkstruct ?F ?Q =>
  match F with
  | wpgen_seq ?F1 ?F2 => xseq
  | wpgen_let ?F1 ?F2of => xlet
  end end.

Tactic Notation "xapp_nosubst" constr(E) :=
  xseq_xlet_if_needed; xstruct_if_needed;
  applys xapp_lemma E; [ xsimpl | xpull ].

(** [xwp] applys [xwp_lemma], then requests Coq to evaluate the
    [wpgen] function. (For technical reasons, we need to explicitly
    request the unfolding of [wpgen_var].) *)

Tactic Notation "xwp" :=
  intros; applys xwp_lemma;
  [ reflexivity
  | simpl; unfold wpgen_var; simpl ].

(** Let us revisit the previous proof scripts using x-tactics
    instead of x-lemmas. The reader may contemplate the gain
    in conciseness. *)

Module ProofsWithXtactics.
Import ExamplePrograms.
Open Scope wpgen_scope.

Lemma triple_incr : forall (p:loc) (n:int),
  triple (trm_app incr p)
    (p ~~> n)
    (fun _ => p ~~> (n+1)).
Proof using.
  xwp.
  xapp_nosubst triple_get. intros ? ->.
  xapp_nosubst triple_add. intros ? ->.
  xapp_nosubst triple_set.
  xsimpl.
Qed.

(** **** Exercise: 2 stars, standard, especially useful (triple_succ_using_incr_with_xtactics)

    Using x-tactics, verify the proof of [succ_using_incr]. *)

Lemma triple_succ_using_incr_with_xtactics : forall (n:int),
  triple (trm_app succ_using_incr n)
    \[]
    (fun v => \[v = n+1]).
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

End ProofsWithXtactics.

(* ================================================================= *)
(** ** Further Improvements to the [xapp] Tactic. *)

(** In this section, we describe two improvements to the [xapp]
    tactic. *)

(** The pattern [xapp_nosubst E. intros ? ->.] appears frequently
    in the above proofs. This pattern is typically useful whenever
    the specification [E] features a postcondition of the form
    [fun v => \[v = ..]] or of the form [fun v => \[v = ..] \* ..].

    Likewise, the pattern [xapp_nosubst E. intros ? p ->.] appears
    frequently. This pattern is typically useful whenever the
    specification [E] features a postcondition of the form
    [fun v => \exists p, \[v = ..] \* ... ].

    It therefore makes sense to introduce a tactic [xapp E] that,
    after calling [xapp_nosubst E], attempts to invoke [intros ? ->]
    or [intros ? x ->; revert x]. In the latter case, to ensure that
    the name [x] that we use does not modify the existing name of the
    bound variable, we play some Ltac hacks, captured by the tactic
    [xapp_try_subst]. *)

Tactic Notation "xapp_try_subst" := (* for internal use only *)
  try match goal with
  | |- forall (r:val), (r = _) -> _ => intros ? ->
  | |- forall (r:val), forall x, (r = _) -> _ =>
      let y := fresh x in intros ? y ->; revert y
  end.

Tactic Notation "xapp" constr(E) :=
  xapp_nosubst E; xapp_try_subst.

(** Explicitly providing arguments to [xapp_nosubst] or [xapp]
    is very tedious. To avoid that effort, we can set up the tactics
    to automatically look up for the relevant specification.

    To that end, we instrument [eauto] to exploit a database of
    already-established specification triples. This database, named
    [triple], can be populated using the [Hint Resolve ... : triple]
    command, as illustrated below. *)

Hint Resolve triple_get triple_set triple_ref triple_free triple_add : triple.

(** The argument-free variants [xapp_subst] and [xapp] are implemented
    by invoking [eauto with triple] to retrieve the relevant
    specification.

    The definition from [Direct] is slightly more powerful, in that
    it is also able to pick up an induction hypothesis from the
    context for instantiating the triple.

    DISCLAIMER: the tactic [xapp] that leverages the [triple] database
    is not able to automatically apply specifications that feature a
    premise that [eauto] cannot solve. To exploit such specifications,
    one need to provide the specification explicitly (using [xapp E]),
    or to exploit a more complex hint mechanism (as done in CFML). (A
    poor-man's workaround consists in moving all the premises inside
    the precondition, however doing so harms readability.) *)

Tactic Notation "xapp_nosubst" :=
  xseq_xlet_if_needed; xstruct_if_needed;
  applys xapp_lemma; [ solve [ eauto with triple ] | xsimpl | xpull ].

Tactic Notation "xapp" :=
  xapp_nosubst; xapp_try_subst.

(* ================================================================= *)
(** ** Demo of a Practical Proof using x-Tactics. *)

Module ProofsWithAdvancedXtactics.
Import ExamplePrograms.
Open Scope wpgen_scope.

(** The proof script for the verification of [incr] using the tactic
    [xapps] with implicit argument. *)

Lemma triple_incr : forall (p:loc) (n:int),
  triple (trm_app incr p)
    (p ~~> n)
    (fun _ => p ~~> (n+1)).
Proof using.
  xwp. xapp. xapp. xapp. xsimpl.
Qed.

(** In order to enable automatically exploiting the specification
    of [triple] in the verification of [succ_using_incr], which
    includes a function call to [triple], we add it to the hint
    database [triple]. *)

Hint Resolve triple_incr : triple.

(** **** Exercise: 2 stars, standard, especially useful (triple_succ_using_incr_with_xapps)

    Using the improved x-tactics, verify the proof of [succ_using_incr]. *)

Lemma triple_succ_using_incr_with_xapps : forall (n:int),
  triple (trm_app succ_using_incr n)
    \[]
    (fun v => \[v = n+1]).
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** In summary, thanks to [wpgen] and its associated x-tactics,
    we are able to verify concrete programs in Separation Logic
    with concise proof scripts. *)

End ProofsWithAdvancedXtactics.

(* ################################################################# *)
(** * Optional Material *)

(* ================================================================= *)
(** ** Tactics [xconseq] and [xframe] *)

(** The tactic [xconseq] applies the weakening rule, from the perspective of
    the user, it replaces the current postcondition with a stronger one.
    Optionally, the tactic can be passed an explicit argument, using
    the syntax [xconseq Q].

    The tactic is implemented by applying the lemma [xconseq_lemma],
    stated below. *)

(** **** Exercise: 1 star, standard, optional (xconseq_lemma)

    Prove the [xconseq_lemma]. *)

Lemma xconseq_lemma : forall Q1 Q2 H F,
  H ==> mkstruct F Q1 ->
  Q1 ===> Q2 ->
  H ==> mkstruct F Q2.
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

Tactic Notation "xconseq" :=
  applys xconseq_lemma.

Tactic Notation "xconseq" constr(Q) :=
  applys xconseq_lemma Q.

(** The tactic [xframe] enables applying the frame rule on a formula
    produced by [wpgen]. The syntax [xframe H] is used to specify
    the heap predicate to keep, and the syntax [xframe_out H] is used
    to specify the heap predicate to frame out---everything else is kept. *)

(** **** Exercise: 2 stars, standard, optional (xframe_lemma)

    Prove the [xframe_lemma].
    Exploit the properties of [mkstruct]; do not try to unfold the
    definition of [mkstruct]. *)

Lemma xframe_lemma : forall H1 H2 H Q Q1 F,
  H ==> H1 \* H2 ->
  H1 ==> mkstruct F Q1 ->
  Q1 \*+ H2 ===> Q ->
  H ==> mkstruct F Q.
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

Tactic Notation "xframe" constr(H) :=
  eapply (@xframe_lemma H); [ xsimpl | | ].

Tactic Notation "xframe_out" constr(H) :=
  eapply (@xframe_lemma _ H); [ xsimpl | | ].

(** Let's illustrate the use of [xframe] on an example. *)

Module ProofsWithStructuralXtactics.
Import ExamplePrograms.
Open Scope wpgen_scope.

Lemma triple_incr_frame : forall (p q:loc) (n m:int),
  triple (trm_app incr p)
    (p ~~> n \* q ~~> m)
    (fun _ => (p ~~> (n+1)) \* (q ~~> m)).
Proof using.
  xwp.
(** Instead of calling [xapp], we put aside [q ~~> m] and focus on [p ~~> n]. *)
  xframe (p ~~> n). (* equivalent to [xframe_out (q ~~> m)].

    Then we can work in a smaller state that mentions only [p ~~> n]. *)
  xapp. xapp. xapp.
(** Finally we check the check that the current state augmented with
    the framed predicate [q ~~> m] matches with the claimed postcondition. *)
  xsimpl.
Qed.

End ProofsWithStructuralXtactics.

(* ================================================================= *)
(** ** Soundness Proof for [wpgen] *)

Module WPgenSound.

(* ----------------------------------------------------------------- *)
(** *** Introduction of the Predicate [formula_sound] *)

(** The soundness theorem that we aim to establish for [wpgen] is:

    Parameter wpgen_sound : forall E t Q,
      wpgen E t Q ==> wp (isubst E t) Q.
*)

(** Before we enter the details of the proof, let us reformulate the
    soundness statement of the soundness theorem in a way that will
    make proof obligations and induction hypotheses easier to read.
    To that end, we introduce the predicate [formula_sound t F],
    which asserts that [F] is a weakest-precondition style formula
    that entails [wp t]. Formally: *)

Definition formula_sound (t:trm) (F:formula) : Prop :=
  forall Q, F Q ==> wp t Q.

(** Using [formula_sound], the soundness theorem for [wpgen]
    reformulates as follows. *)

Parameter wpgen_sound' : forall E t,
  formula_sound (isubst E t) (wpgen E t).

(* ----------------------------------------------------------------- *)
(** *** Soundness for the Case of Sequences *)

(** Let us forget about the existence of [mkstruct] for a minute,
    that is, pretend that [wpgen] is defined without [mkstruct].

    In that setting, [wpgen E (trm_seq t1 t2)] evaluates to
    [wpgen_seq (wpgen E t1) (wpgen E t2)].

    Recall the definition of [wpgen_seq].

    Definition wpgen_seq (F1 F2:formula) : formula := fun Q =>
      F1 (fun v => F2 Q).
*)

(** Consider the soundness theorem [wpgen_sound] and let us specialize
    it to the particular case where [t] is of the form [trm_seq t1 t2].
    The corresponding statement is: *)

Parameter wpgen_sound_seq : forall E t1 t2,
  formula_sound (isubst E (trm_seq t1 t2)) (wpgen E (trm_seq t1 t2)).

(** In that statement:

    - [wpgen E (trm_seq t1 t2)] evaluates to
      [wpgen_seq (wpgen E t1) (wpgen E t2)].
    - [isubst E (trm_seq t1 t2)] evaluates to
      [trm_seq (isubst E t1) (isubst E t2)].

    Moreover, by induction hypothesis, we will be able to assume
    the soundness result to already hold for the subterms [t1] and [t2].

    Thus, to establish the soundness of [wpgen] for sequences, we
    have to prove the following result: *)

Parameter wpgen_sound_seq' : forall E t1 t2,
  formula_sound (isubst E t1) (wpgen E t1) ->
  formula_sound (isubst E t2) (wpgen E t2) ->
  formula_sound (trm_seq (isubst E t1) (isubst E t2))
                (wpgen_seq (wpgen E t1) (wpgen E t2)).

(** In the above statement, let us abstract [isubst E t1] as [t1']
    and [wpgen t1] as [F1], and similarly [isubst E t2] as [t2']
    and [wpgen t2] as [F2]. The statement reformulates as: *)

Lemma wpgen_seq_sound : forall t1' t2' F1 F2,
  formula_sound t1' F1 ->
  formula_sound t2' F2 ->
  formula_sound (trm_seq t1' t2') (wpgen_seq F1 F2).

(** This statement captures the essence of the correctness of
    the definition of [wpgen_seq]. Let's prove it. *)

Proof using.
  introv S1 S2.
  (* Reveal the soundness statement *)
  unfolds formula_sound.
  (* Consider a postcondition [Q] *)
  intros Q.
  (* Reveal [wpgen_seq F1 F2], which is defined as [F1 (fun v => F2 Q)]. *)
  unfolds wpgen_seq.
  (* By transitivity of entailment *)
  applys himpl_trans.
  (* Apply the soundness result for [wp] on sequences:
     [wp t1 (fun v => wp t2 Q) ==> wp (trm_seq t1 t2) Q]. *)
  2:{ applys wp_seq. }
  (* Exploit the induction hypotheses to conclude *)
  { applys himpl_trans.
    { applys S1. }
    { applys wp_conseq. intros v. applys S2. } }
Qed.

(* ----------------------------------------------------------------- *)
(** *** Soundness of [wpgen] for the Other Term Constructs *)

(** The proof for the other term constructs are shown below and
    will be used to set up the main induction. The reader may
    skip over the proof details. *)

Lemma wpgen_val_sound : forall v,
  formula_sound (trm_val v) (wpgen_val v).
Proof using. intros. intros Q. unfolds wpgen_val. applys wp_val. Qed.

Lemma wpgen_fun_val_sound : forall x t,
  formula_sound (trm_fun x t) (wpgen_val (val_fun x t)).
Proof using. intros. intros Q. unfolds wpgen_val. applys wp_fun. Qed.

Lemma wpgen_fix_val_sound : forall f x t,
  formula_sound (trm_fix f x t) (wpgen_val (val_fix f x t)).
Proof using. intros. intros Q. unfolds wpgen_val. applys wp_fix. Qed.

Lemma wpgen_let_sound : forall F1 F2of x t1 t2,
  formula_sound t1 F1 ->
  (forall v, formula_sound (subst x v t2) (F2of v)) ->
  formula_sound (trm_let x t1 t2) (wpgen_let F1 F2of).
Proof using.
  introv S1 S2. intros Q. unfolds wpgen_let. applys himpl_trans wp_let.
  applys himpl_trans S1. applys wp_conseq. intros v. applys S2.
Qed.

Lemma wpgen_if_sound : forall F1 F2 t0 t1 t2,
  formula_sound t1 F1 ->
  formula_sound t2 F2 ->
  formula_sound (trm_if t0 t1 t2) (wpgen_if t0 F1 F2).
Proof using.
  introv S1 S2. intros Q. unfold wpgen_if. xpull. intros b ->.
  applys himpl_trans wp_if. case_if. { applys S1. } { applys S2. }
Qed.

(** The formula [wpgen_fail] is a sound formula not just for a variable
   [trm_var x], but in fact for any term [t]. Indeed, the entailment
   [\[False] ==> wp t Q] is always true. Hence the general statement
   for [wpgen_fail] that appears next. *)

Lemma wpgen_fail_sound : forall t,
  formula_sound t wpgen_fail.
Proof using. intros. intros Q. unfold wpgen_fail. xpull. Qed.

(** The formula [wp t] is a sound formula for a term [t], not just when
    [t] is an application, but for any term [t]. Hence the general
    statement for [wp] that appears next. *)

Lemma wp_sound : forall t,
  formula_sound t (wp t).
Proof using. intros. intros Q. applys himpl_refl. Qed.

(* ----------------------------------------------------------------- *)
(** *** Soundness of [mkstruct] *)

(** To carry out the soundness proof for [wpgen], we also need to justify
    that the addition of [mkstruct] to the head of every call to [wpgen]
    preserves the entailment [wpgen t Q ==> wp t Q].

    Consider a term [t]. The result of [wpgen t] takes the form [mkstruct F],
    where [F] denotes the main pattern matching on [t] that occurs in the
    definition of [wpgen].

    Our goal is to show that if the formula [F] is a valid weakest
    precondition for [t], then so is [mkstruct F]. One way to prove
    this result is to exploit the fact that, when a formula [F] is of
    the form [wp t], applying [mkstruct] does not alter its meaning
    (recall lemma [mkstruct_wp]). *)

Lemma mkstruct_sound : forall t F,
  formula_sound t F ->
  formula_sound t (mkstruct F).
Proof using.
  introv M. unfolds formula_sound. intros Q.
  rewrite <- mkstruct_wp. applys mkstruct_monotone. applys M.
Qed.

(** Another, lower-level proof for the same result reveals the definition
    of [mkstruct] and exploits the consequence-frame rule for [wp]. *)

Lemma mkstruct_sound' : forall t F,
  formula_sound t F ->
  formula_sound t (mkstruct F).
Proof using.
  introv M. unfolds formula_sound.
  (* Consider a postcondition [Q] *)
  intros Q.
  (* Reveal the definition of [mkstruct] *)
  unfolds mkstruct.
  (* Extract the [Q'] quantified in the definition of [mkstruct] *)
  xsimpl; intros Q' H N.
  (* Instantiate the assumption on [F] with that [Q'], and exploit it. *)
  lets M': M Q'. xchange M'.
  (* Conclude using the structural rules for [wp]. *)
  applys wp_conseq_frame. applys N.
Qed.

(* ----------------------------------------------------------------- *)
(** *** Lemmas Capturing Properties of Iterated Substitutions *)

(** In the proof of soundness for [wpgen], we need to exploit two
    basic properties of the iterated substitution function [isubst].

    The first property asserts that the substitution for the empty
    context is the identity. This result is needed to cleanly state
    the final statement of the soundness theorem. *)

Parameter isubst_nil : forall t,
  isubst nil t = t.

(** The second property asserts that the substitution for a context
    [(x,v)::E] is the same as the substitution for the context [rem x E]
    followed with the substitution of [x] by [v] using the basic
    substitution function [subst]. This second property is needed to
    handle the case of let-bindings. *)

Parameter isubst_rem : forall x v E t,
  isubst ((x,v)::E) t = subst x v (isubst (rem x E) t).

(** The proofs for these two lemmas is technical and of limited interest.
    They can be found in appendix near the end of this chapter. *)

(* ----------------------------------------------------------------- *)
(** *** Main Induction for the Soundness Proof of [wpgen] *)

(** We prove the soundness of [wpgen E t] by structural induction on [t].

    As explained previously, the soundness lemma is stated with help of
    the predicate [formula_sound], in the form:
    [formula_sound (isubst E t) (wpgen t)].

    For each term construct, the proof case consists of two steps:

    - first, invoke the lemma [mkstruct_sound] to justify soundness
      of the leading [mkstruct] produced by [wpgen],
    - second, invoke the the soundness lemma specific to that term
      construct, e.g. [wpgen_seq_sound] for sequences.

*)

Lemma wpgen_sound_induct : forall E t,
  formula_sound (isubst E t) (wpgen E t).
Proof using.
  intros. gen E. induction t; intros; simpl;
   applys mkstruct_sound.
  { applys wpgen_val_sound. }
  { rename v into x. unfold wpgen_var. case_eq (lookup x E).
    { intros v EQ. applys wpgen_val_sound. }
    { intros N. applys wpgen_fail_sound. } }
  { applys wpgen_fun_val_sound. }
  { applys wpgen_fix_val_sound. }
  { applys wp_sound. }
  { applys wpgen_seq_sound. { applys IHt1. } { applys IHt2. } }
  { rename v into x. applys wpgen_let_sound.
    { applys IHt1. }
    { intros v. rewrite <- isubst_rem. applys IHt2. } }
  { applys wpgen_if_sound. { applys IHt2. } { applys IHt3. } }
Qed.

(* ----------------------------------------------------------------- *)
(** *** Statement of Soundness of [wpgen] for Closed Terms *)

(** For a closed term [t], the context [E] is instantiated as [nil],
    and [isubst nil t] simplifies to [t]. We obtain the main
    soundness statement for [wpgen]. *)

Lemma wpgen_sound : forall t Q,
  wpgen nil t Q ==> wp t Q.
Proof using.
  introv M. lets N: (wpgen_sound nil t). rewrite isubst_nil in N. applys* N.
Qed.

(** A corollary can be derived for deriving a triple of the
    form [triple t H Q] from [wpgen nil t]. *)

Lemma triple_of_wpgen : forall t H Q,
  H ==> wpgen nil t Q ->
  triple t H Q.
Proof using.
  introv M. rewrite <- wp_equiv. xchange M. applys wpgen_sound.
Qed.

(** The lemma [triple_app_fun_from_wpgen], used by the tactic [xwp],
    is a variant of [wpgen_of_triple] specialized for establishing
    a triple for a function application. (Recall that, in essence,
    this lemma is a reformulation of the rule [triple_app_fun].) *)

Lemma triple_app_fun_from_wpgen : forall v1 v2 x t1 H Q,
  v1 = val_fun x t1 ->
  H ==> wpgen ((x,v2)::nil) t1 Q ->
  triple (trm_app v1 v2) H Q.
Proof using.
  introv M1 M2. applys triple_app_fun M1.
  asserts_rewrite (subst x v2 t1 = isubst ((x,v2)::nil) t1).
  { rewrite isubst_rem. rewrite* isubst_nil. }
  rewrite <- wp_equiv. xchange M2. applys wpgen_sound_induct.
Qed.

(** The lemma [triple_app_fix_from_wpgen] is a variant of the above
    lemma suited for recursive functions. Note that the proof exploits a
    lemma called [isubst_rem_2] which is an immediate generalization of
    the lemma [isubst_rem]. The proof of [isubst_rem_2] appears near
    the bottom of this file. *)

Lemma triple_app_fix_from_wpgen : forall v1 v2 f x t1 H Q,
  v1 = val_fix f x t1 ->
  H ==> wpgen ((f,v1)::(x,v2)::nil) t1 Q ->
  triple (trm_app v1 v2) H Q.
Proof using.
  introv M1 M2. applys triple_app_fix M1.
  asserts_rewrite (subst x v2 (subst f v1 t1)
                 = isubst ((f,v1)::(x,v2)::nil) t1).
  { rewrite isubst_rem_2. rewrite* isubst_nil. }
  rewrite <- wp_equiv. xchange M2. applys wpgen_sound_induct.
Qed.

End WPgenSound.

(* ================================================================= *)
(** ** Guessing the Definition of [mkstruct] *)

Module MkstructGuess.

(** How could we have possibly guessed the definition of [mkstruct]?

    Recall that we observed, in an exercise, that the definition
    of [mkstruct] satisfies the idempotence property:

    Lemma mkstruct_idempotence : forall F
      mkstruct (mkstruct F) = mkstruct F

    This idempotence property reflects in particular the fact that consecutive
    applications of the frame rule can be combined into into a single
    application of this rule, and likewise for the rule of consequence. Since
    it seems to make some sense for [mkstruct] to be idempotent, let us pretend
    that this property is a requirement for [mkstruct].

    In other words, assume that we are searching for a predicate satisfying
    4 properties: [mkstruct_frame], [mkstruct_conseq], [mkstruct_erase], and
    [mkstruct_idempotence].

    The following reasoning steps can lead to figure out a definition of
    [mkstruct] that satisfies these properties. *)

(** Recall the statement of [mkstruct_frame] and of [mkstruct_conseq]. *)

Parameter mkstruct_frame : forall F H Q,
  (mkstruct F Q) \* H ==> mkstruct F (Q \*+ H).

Parameter mkstruct_conseq : forall F Q1 Q2,
  Q1 ===> Q2 ->
  mkstruct F Q1 ==> mkstruct F Q2.

(** The two rules can be combined into a single one as follows
    (similarly to the way it is done for [wp_conseq_frame]). *)

Parameter mkstruct_conseq_frame : forall F Q1 Q2 H,
  Q1 \*+ H ===> Q2 ->
  H \* (mkstruct F Q1) ==> mkstruct F Q2.

(** By the idempotence property [mkstruct_idempotence],
    [mkstruct F] should be equal to [mkstruct (mkstruct F)].
    Let's exploit this equality for the second occurrence of [mkstruct F]. *)

Parameter mkstruct_conseq_idempotence : forall F Q1 Q2 H,
  Q1 \*+ H ===> Q2 ->
  H \* (mkstruct F Q1) ==> mkstruct (mkstruct F) Q2.

(** Now, let's replace [mkstruct F] with [F']. Doing so results in the
    statment shown below, which gives a sufficient condition for the
    statement [mkstruct_conseq_idempotence] to hold. *)

Parameter mkstruct_conseq_idempotence_generalized : forall F' Q1 Q2 H,
  Q1 \*+ H ===> Q2 ->
  H \* (F' Q1) ==> mkstruct F' Q2.

(** We can reformulate the above statement as an introduction rule
    by merging the hypothesis into the left-hand side of the entailment
    from the conclusion. We thereby obtain an introduction lemma
    for [mkstruct]. *)

Parameter mkstruct_introduction : forall F' Q2,
  \exists Q1 H, \[Q1 \*+ H ===> Q2] \* H \* (F' Q1) ==> mkstruct F' Q2.

(** For this entailment to hold, because entailment is a reflexive relation,
    it is sufficient to define [mkstruct F' Q2], that is, the right-hand side
    of the entailment, as equal to the contents of the left-hand side. *)

Definition mkstruct (F':formula) : formula :=
  fun (Q2:val->hprop) => \exists Q1 H, \[Q1 \*+ H ===> Q2] \* H \* (F' Q1).

(** As we have proved earlier in this chapter, this definition indeed satisfies
    the 4 desired properties: [mkstruct_frame], [mkstruct_conseq],
    [mkstruct_erase], and [mkstruct_idempotence]. *)

End MkstructGuess.

(* ================================================================= *)
(** ** Proof of Properties of Iterated Substitution *)

(** In these proofs, we use the TLC tactic [fequals] which is an enhanced
    variant of the tactic [f_equal]. *)

Module IsubstProp.

Open Scope liblist_scope.

Implicit Types E : ctx.

(** Recall that [isubst E t] denotes the multi-substitution
    in the term [t] of all bindings form the association list [E].

    The soundness proof for [wpgen] and the proof of its corollary
    [triple_app_fun_from_wpgen] rely on two key properties of
    iterated substitutions, captured by the lemmas called [isubst_nil]
    and [isubst_rem], which we state and prove next.

    isubst nil t = t

    subst x v (isubst (rem x E) t) = isubst ((x,v)::E) t
*)

(** The first lemma is straightforward by induction. *)

Lemma isubst_nil : forall t,
  isubst nil t = t.
Proof using.
  intros t. induction t; simpl; fequals.
Qed.

(** The second lemma is much more involved to prove.

    We introduce the notion of "two equivalent contexts"
    [E1] and [E2], and argue that substitution for two
    equivalent contexts yields the same result.

    We then introduce the notion of "contexts with disjoint
    domains", and argue that if [E1] and [E2] are disjoint then
    [isubst (E1 ++ E2) t = isubst E1 (isubst E2 t)]. *)

(** Before we start, we describe the tactic [case_var], which
    helps with the case_analyses on variable equalities,
    and we prove an auxiliary lemma that describes the
    result of a lookup on a context from which a binding
    has been removed. It is defined in file [LibSepVar.v] as:

    Tactic Notation "case_var" :=
      repeat rewrite var_eq_spec in *; repeat case_if.

    The tactic [case_var*] is a shorthand for [case_var]
    followed with automation (essentially, [eauto]).
*)

(** On key auxiliary lemma relates [subst] and [isubst]. *)

Lemma subst_eq_isubst_one : forall x v t,
  subst x v t = isubst ((x,v)::nil) t.
Proof using.
  intros. induction t; simpl.
  { fequals. }
  { case_var*. }
  { fequals. case_var*. { rewrite* isubst_nil. } }
  { fequals. case_var; try case_var; simpl; try case_var;
              try rewrite isubst_nil; auto. }
  { fequals*. }
  { fequals*. }
  { fequals*. case_var*. { rewrite* isubst_nil. } }
  { fequals*. }
Qed.

(** A lemma about the lookup in a removal. *)

Lemma lookup_rem : forall x y E,
  lookup x (rem y E) = if var_eq x y then None else lookup x E.
Proof using.
  intros. induction E as [|(z,v) E'].
  { simpl. case_var*. }
  { simpl. case_var*; simpl; case_var*. }
Qed.

(** A lemma about the removal over an append. *)

Lemma rem_app : forall x E1 E2,
  rem x (E1 ++ E2) = rem x E1 ++ rem x E2.
Proof using.
  intros. induction E1 as [|(y,w) E1']; rew_list; simpl. { auto. }
  { case_var*. { rew_list. fequals. } }
Qed.

(** The definition of equivalent contexts. *)

Definition ctx_equiv E1 E2 :=
  forall x, lookup x E1 = lookup x E2.

(** The fact that removal preserves equivalence. *)

Lemma ctx_equiv_rem : forall x E1 E2,
  ctx_equiv E1 E2 ->
  ctx_equiv (rem x E1) (rem x E2).
Proof using.
  introv M. unfolds ctx_equiv. intros y.
  do 2 rewrite lookup_rem. case_var*.
Qed.

(** The fact that substitution for equivalent contexts
    yields equal results. *)

Lemma isubst_ctx_equiv : forall t E1 E2,
  ctx_equiv E1 E2 ->
  isubst E1 t = isubst E2 t.
Proof using.
  hint ctx_equiv_rem.
  intros t. induction t; introv EQ; simpl; fequals*.
  { rewrite EQ. auto. }
Qed.

(** The definition of disjoint contexts. *)

Definition ctx_disjoint E1 E2 :=
  forall x v1 v2, lookup x E1 = Some v1 -> lookup x E2 = Some v2 -> False.

(** Removal preserves disjointness. *)

Lemma ctx_disjoint_rem : forall x E1 E2,
  ctx_disjoint E1 E2 ->
  ctx_disjoint (rem x E1) (rem x E2).
Proof using.
  introv D. intros y v1 v2 K1 K2. rewrite lookup_rem in *.
  case_var. applys* D K1 K2.
Qed.

(** Lookup in the concatenation of two disjoint contexts *)

Lemma lookup_app : forall x E1 E2,
  lookup x (E1 ++ E2) = match lookup x E1 with
                        | None => lookup x E2
                        | Some v => Some v
                        end.
Proof using.
  introv. induction E1 as [|(y,w) E1']; rew_list; simpl; intros.
  { auto. }
  { case_var*. }
Qed.

(** The key induction shows that [isubst] distributes over
    context concatenation. *)

Lemma isubst_app : forall t E1 E2,
  isubst (E1 ++ E2) t = isubst E2 (isubst E1 t).
Proof using.
  hint ctx_disjoint_rem.
  intros t. induction t; simpl; intros.
  { fequals. }
  { rename v into x. rewrite* lookup_app.
    case_eq (lookup x E1); introv K1; case_eq (lookup x E2); introv K2; auto.
    { simpl. rewrite* K2. }
    { simpl. rewrite* K2. } }
  { fequals. rewrite* rem_app. }
  { fequals. do 2 rewrite* rem_app. }
  { fequals*. }
  { fequals*. }
  { fequals*. { rewrite* rem_app. } }
  { fequals*. }
Qed.

(** The next lemma asserts that the concatenation order is irrelevant
    in a substitution if the contexts have disjoint domains. *)

Lemma isubst_app_swap : forall t E1 E2,
  ctx_disjoint E1 E2 ->
  isubst (E1 ++ E2) t = isubst (E2 ++ E1) t.
Proof using.
  introv D. applys isubst_ctx_equiv. applys* ctx_disjoint_equiv_app.
Qed.

(** We are ready to derive the desired property of [isubst]. *)

Lemma isubst_rem : forall x v E t,
  isubst ((x, v)::E) t = subst x v (isubst (rem x E) t).
Proof using.
  intros. rewrite subst_eq_isubst_one. rewrite <- isubst_app.
  rewrite isubst_app_swap.
  { applys isubst_ctx_equiv. intros y. rew_list. simpl. case_var*.
    { rewrite lookup_rem. case_var*. } }
  { intros y v1 v2 K1 K2. simpls. case_var.
    { subst. rewrite lookup_rem in K1. case_var*. } }
Qed.

(** We also prove the variant lemma which is useful for handling recursive
    functions. *)

Lemma isubst_rem_2 : forall f x vf vx E t,
    isubst ((f,vf)::(x,vx)::E) t
  = subst x vx (subst f vf (isubst (rem x (rem f E)) t)).
Proof using.
  intros. do 2 rewrite subst_eq_isubst_one. do 2 rewrite <- isubst_app.
  rewrite isubst_app_swap.
  { applys isubst_ctx_equiv. intros y. rew_list. simpl.
    do 2 rewrite lookup_rem. case_var*. }
  { intros y v1 v2 K1 K2. rew_listx in *. simpls.
    do 2 rewrite lookup_rem in K1. case_var. }
Qed.

End IsubstProp.

(* ================================================================= *)
(** ** Historical Notes *)

(** Many verification tools based on Hoare Logic are based on a weakest-
    precondition generator. Typically, a tool takes as input a source code
    annotated with specifications and invariants, and produces a logical
    formula that entails the correctness of the program. This logical formula
    is typically expressed in first-order logic, and is discharged using
    automated tools such as SMT solvers.

    In contrast, the weakest-precondition generator presented in this chapter
    applies to un-annotated code. It thus produces a logical formula that does
    not depend at all on the specifications and invariants. Such formula,
    which can be constructed in a systematic manner, is called a "characteristic
    formula" in the literature. In general, a characteristic formula provides
    not just a sound but also a complete description of the semantics of a
    program. Discussion of completeness is beyond the scope of this course.

    The notion of characteristic formula was introduced work by
    [Hennessy and Milner 1985] (in Bib.v) on process calculi. It was first applied to
    program logic by [Honda, Berger, and Yoshida 2006] (in Bib.v). It was then applied
    to Separation Logic in the PhD work of [Charguéraud 2010] (in Bib.v), which
    resulted in the CFML tool. CFML 1.0 used an external tool that produced
    characteristic formulae in the form of Coq axioms. Later work by
    [Guéneau, Myreen, Kumar and Norrish 2017] (in Bib.v) showed how the
    characteristic formulae could be produced together with proofs justifying
    their correctness.

    In Charguéraud's PhD and in Guéneau et al.'s work, characteristic formulae
    were slightly more complicated than those presented here, because they did
    not leverage the weakest-precondition approach, which streamlines the
    presentation.

    Compared with Hoare Logic, one key aspect of characteristic formulae for
    Separation Logic is the need to support the frame rule. In this chapter,
    the predicate [mkstruct] introduced at every node of the output of [wpgen]
    serves that purpose. The definition of [wpgen] as stated in this chapter
    will probably be the matter of a publication in 2021. *)

(* 2022-07-20 20:58 *)
