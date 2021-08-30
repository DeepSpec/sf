(** * Rules: Reasoning Rules *)

Set Implicit Arguments.

(** This file imports [LibSepDirect.v] instead of [Hprop.v] and [Himpl.v].
    The file [LibSepDirect.v] contains definitions that are essentially similar
    to those from [Hprop.v] and [Himpl.v], yet with one main difference:
    [LibSepDirect] makes the definition of Separation Logic operators opaque.

    As a result, one cannot unfold the definition of [hstar], [hpure], etc.
    To carry out reasoning, one must use the introduction and elimination
    lemmas (e.g. [hstar_intro], [hstar_elim]). These lemmas enforce
    abstraction: they ensure that the proofs do not depend on the particular
    choice of the definitions used for constructing Separation Logic. *)

From SLF Require Export LibSepReference.
From SLF Require Basic.

(* ################################################################# *)
(** * First Pass *)

(** In the previous chapters, we have:

    - introduced the key heap predicate operators,
    - introduced the notion of Separation Logic triple,
    - introduced the entailment relation,
    - introduced the structural rules of Separation Logic.

    We are now ready to present the other reasoning rules,
    which enable establishing properties of concrete programs.

    These reasoning rules are proved correct with respect to the
    semantics of the programming language in which the programs
    are expressed. Thus, a necessary preliminary step is to present
    the syntax and the semantics of a (toy) programming language,
    for which we aim to provide Separation Logic reasoning rules.

    The present chapter is thus organized as follows:

    - definition of the syntax of the language,
    - definition of the semantics of the language,
    - statements of the reasoning rules associated with each of
      the term constructions from the language,
    - specification of the primitive operations of the language,
      in particular those associated with memory operations,
    - review of the 4 structural rules introduced in prior chapters,
    - examples of practical verification proofs.

    The bonus section (optional) also includes:
    - proofs of the reasoning rules associated with each term construct,
    - proofs of the specification of the primitive operations. *)

(* ================================================================= *)
(** ** Semantic of Terms *)

Module SyntaxAndSemantics.

(* ----------------------------------------------------------------- *)
(** *** Syntax *)

(** The syntax described next captures the "abstract syntax tree"
    of a programming language. It follows a presentation that
    distiguishes between closed values and terms. This presentation
    is intended to simplify the definition and evaluation of the
    substitution function: because values are always closed (i.e.,
    no free variables in them), the substitution function never
    needs to traverse through values.

    The grammar for values includes unit, boolean, integers,
    locations, functions, recursive functions, and primitive operations.
    For example, [val_int 3] denotes the integer value [3]. The value
    [val_fun x t] denotes the function [fun x => t], and the value
    [val_fix f x t] denotes the function [fix f x => t], which is
    written [let rec f x = t in f] in OCaml syntax.

    For conciseness, we include just a few primitive operations:
    [ref], [get], [set] and [free] for manipulating the mutable state,
    the operation [add] to illustrate a simple arithmetic operation,
    and the operation [div] to illustrate a partial operation. *)

Inductive val : Type :=
  | val_unit : val
  | val_bool : bool -> val
  | val_int : int -> val
  | val_loc : loc -> val
  | val_fun : var -> trm -> val
  | val_fix : var -> var -> trm -> val
  | val_ref : val
  | val_get : val
  | val_set : val
  | val_free : val
  | val_add : val
  | val_div : val

(** The grammar for terms includes values, variables, function definitions,
    recursive function definitions, function applications, sequences,
    let-bindings, and conditionals. *)

with trm : Type :=
  | trm_val : val -> trm
  | trm_var : var -> trm
  | trm_fun : var -> trm -> trm
  | trm_fix : var -> var -> trm -> trm
  | trm_app : trm -> trm -> trm
  | trm_seq : trm -> trm -> trm
  | trm_let : var -> trm -> trm -> trm
  | trm_if : trm -> trm -> trm -> trm.

(** Note that [trm_fun] and [trm_fix] denote functions that may feature free
    variables, unlike [val_fun] and [val_fix] which denote closed values.
    The intention is that the evaluation of a [trm_fun] in the empty context
    produces a [val_fun] value. Likewise, a [trm_fix] eventually evaluates to
    a [val_fix]. *)

(** Several value constructors are declared as coercions, to enable more
    concise statements. For example, [val_loc] is declared as a coercion,
    so that a location [p] of type [loc] can be viewed as the value
    [val_loc p] where an expression of type [val] is expected. Likewise,
    a boolean [b] may be viewed as the value [val_bool b], and an integer
    [n] may be viewed as the value [val_int n]. *)

Coercion val_loc : loc >-> val.
Coercion val_bool : bool >-> val.
Coercion val_int : Z >-> val.

(* ----------------------------------------------------------------- *)
(** *** State *)

(** The language we consider is an imperative language, with primitive
    functions for manipulating the state. Thus, the statement of the
    evaluation rules involve a memory state.

    Recall from [Hprop] that a state is represented as a finite map
    from location to values. Finite maps are presented using the type
    [fmap]. Details of the construction of finite maps are beyond the
    scope of this course; details may be found in the the file
    [LibSepFmap.v]. *)

Definition state : Type := fmap loc val.

(** For technical reasons related to the internal representation of finite
    maps, to enable reading in a state, we need to justify that the grammar
    of values is inhabited. This property is captured by the following
    command, whose details are not relevant for understanding the rest of
    the chapter. *)

Instance Inhab_val : Inhab val.
Proof using. apply (Inhab_of_val val_unit). Qed.

(* ----------------------------------------------------------------- *)
(** *** Substitution *)

(** The semantics of the evaluation of function is described by means
    of a substitution function. The substitution function, written
    [subst y w t], replaces all occurrences of a variable [y] with a
    value [w] inside a term [t].

    The substitution function is always the identity function on values,
    because our language only considers closed values. In other words,
    we define [subst y w (trm_val v) = (trm_val v)].

    The substitution function, when reaching a variable, performs a
    comparison between two variables. To that end, it exploits the
    comparison function [var_eq x y], which produces a boolean value
    indicating whether [x] and [y] denote the same variable. *)

(** "Optional contents": the remaining of this section describes further
    details about the substitution function that may be safely skipped
    over in first reading. *)

(** The substitution operation traverses all other language constructs
    in a structural manner. It takes care of avoiding "variable capture"
    when traversing binders: [subst y w t] does not recurse below the
    scope of binders whose name is equal to [y]. For example, the result
    of [subst y w (trm_let x t1 t2)] is defined as
    [trm_let x (subst y w t1) (if var_eq x y then t2 else (subst y w t2))].

    The auxiliary function [if_y_eq], which appears in the definition of
    [subst] shown below, helps performing the factorizing the relevant
    checks that prevent variable capture. *)

Fixpoint subst (y:var) (w:val) (t:trm) : trm :=
  let aux t := subst y w t in
  let if_y_eq x t1 t2 := if var_eq x y then t1 else t2 in
  match t with
  | trm_val v => trm_val v
  | trm_var x => if_y_eq x (trm_val w) t
  | trm_fun x t1 => trm_fun x (if_y_eq x t1 (aux t1))
  | trm_fix f x t1 => trm_fix f x (if_y_eq f t1 (if_y_eq x t1 (aux t1)))
  | trm_app t1 t2 => trm_app (aux t1) (aux t2)
  | trm_seq t1 t2 => trm_seq  (aux t1) (aux t2)
  | trm_let x t1 t2 => trm_let x (aux t1) (if_y_eq x t2 (aux t2))
  | trm_if t0 t1 t2 => trm_if (aux t0) (aux t1) (aux t2)
  end.

(* ----------------------------------------------------------------- *)
(** *** Implicit Types and Coercions *)

(** To improve the readability of the evaluation rules stated further,
    we take advantage of both implicit types and coercions.

    The implicit types are defined as shown below. For example, the
    first command indicates that variables whose name begins with the
    letter 'b' are, by default, variables of type [bool]. *)

Implicit Types b : bool.
Implicit Types v r : val.
Implicit Types t : trm.
Implicit Types s : state.

(** We next introduce two key coercions. First, we declare
    [trm_val] as a coercion, so that, instead of writing [trm_val v],
    we may write simply [v] wherever a term is expected. *)

Coercion trm_val : val >-> trm.

(** Second, we declare [trm_app] as a "Funclass" coercion. This piece
    of magic enables us to write [t1 t2] as a shorthand for [trm_app t1 t2].
    The idea of associating [trm_app] as the "Funclass" coercion for the
    type [trm] is that if a term [t1] of type [trm] is applied like a
    function to an argument, then [t1] should be interpreted as [trm_app t1]. *)

Coercion trm_app : trm >-> Funclass.

(** Interestingly, the "Funclass" coercion for [trm_app] can be iterated.
    The expression [t1 t2 t3] is parsed by Coq as [(t1 t2) t3]. The first
    application [t1 t2] is interpreted as [trm_app t1 t2]. This expression,
    which itself has type [trm], is applied to [t3]. Hence, it is interpreted
    as [trm_app (trm_app t1 t2) t3], which indeed corresponds to a function
    applied to two arguments. *)

(* ----------------------------------------------------------------- *)
(** *** Big-Step Semantics *)

(** The semantics is presented in big-step style. This presentation makes
    it slightly easier to establish reasoning rules than with small-step
    reduction rules, because both the big-step judgment and a triple
    judgment describe complete execution, relating a term with the value
    that it produces.

    The big-step evaluation judgment, written [eval s t s' v], asserts that,
    starting from state [s], the evaluation of the term [t] terminates in
    a state [s'], producing an output value [v].

    For simplicity, we assume terms to be in "A-normal form": the arguments
    of applications and of conditionals are restricted to variables and value.
    Such a requirement does not limit expressiveness, yet it simplifies the
    statement of the evaluation rules.

    For example, if a source program includes a conditional [trm_if t0 t1 t2],
    then it is required that [t0] be either a variable or a value.
    This is not a real restriction, because [trm_if t0 t1 t2] can always be
    encoded as [let x = t0 in if x then t1 else t2].

    The big-step judgment is inductively defined as follows. *)

Inductive eval : state -> trm -> state -> val -> Prop :=

(** 1. [eval] for values and function definitions.

      A value evaluates to itself.
      A term function evaluates to a value function.
      Likewise for a recursive function. *)

  | eval_val : forall s v,
      eval s (trm_val v) s v
  | eval_fun : forall s x t1,
      eval s (trm_fun x t1) s (val_fun x t1)
  | eval_fix : forall s f x t1,
      eval s (trm_fix f x t1) s (val_fix f x t1)

(** 2. [eval] for function applications.

     The beta reduction rule asserts that [(val_fun x t1) v2]
     evaluates to the same result as [subst x v2 t1].

     In the recursive case, [(val_fix f x t1) v2] evaluates to
     [subst x v2 (subst f v1 t1)], where [v1] denotes the recursive
     function itself, that is, [val_fix f x t1]. *)

  | eval_app_fun : forall s1 s2 v1 v2 x t1 v,
      v1 = val_fun x t1 ->
      eval s1 (subst x v2 t1) s2 v ->
      eval s1 (trm_app v1 v2) s2 v
  | eval_app_fix : forall s1 s2 v1 v2 f x t1 v,
      v1 = val_fix f x t1 ->
      eval s1 (subst x v2 (subst f v1 t1)) s2 v ->
      eval s1 (trm_app v1 v2) s2 v

(** 3. [eval] for structural constructs.

      A sequence [trm_seq t1 t2] first evaluates [t1], taking the
      state from [s1] to [s2], drops the result of [t1], then evaluates
      [t2], taking the state from [s2] to [s3].

      The let-binding [trm_let x t1 t2] is similar, except that the
      variable [x] gets substituted for the result of [t1] inside [t2]. *)

  | eval_seq : forall s1 s2 s3 t1 t2 v1 v,
      eval s1 t1 s2 v1 ->
      eval s2 t2 s3 v ->
      eval s1 (trm_seq t1 t2) s3 v
  | eval_let : forall s1 s2 s3 x t1 t2 v1 r,
      eval s1 t1 s2 v1 ->
      eval s2 (subst x v1 t2) s3 r ->
      eval s1 (trm_let x t1 t2) s3 r

(** 4. [eval] for conditionals.

      A conditional in a source program is assumed to be of the form
      [if t0 then t1 else t2], where [t0] is either a variable or a
      value. If it is a variable, then by the time it reaches an
      evaluation position, the variable must have been substituted
      by a value. Thus, the evaluation rule only considers the form
      [if v0 then t1 else t2]. The value [v0] must be a boolean value,
      otherwise evaluation gets stuck.

      The term [trm_if (val_bool true) t1 t2] behaves like [t1], whereas
      the term [trm_if (val_bool false) t1 t2] behaves like [t2].
      This behavior is described by a single rule, leveraging Coq's "if"
      constructor to factor out the two cases. *)

  | eval_if : forall s1 s2 b v t1 t2,
      eval s1 (if b then t1 else t2) s2 v ->
      eval s1 (trm_if (val_bool b) t1 t2) s2 v

(** 5. [eval] for primitive stateless operations.

      For similar reasons as explained above, the behavior of applied
      primitive functions only need to be described for the case of value
      arguments.

      An arithmetic operation expects integer arguments. The addition
      of [val_int n1] and [val_int n2] produces [val_int (n1 + n2)].

      The division operation, on the same arguments, produces the
      quotient [n1 / n2], under the assumption that the dividor [n2]
      is non-zero. In other words, if a program performs a division
      by zero, then it cannot satisfy the [eval] judgment. *)

  | eval_add : forall s n1 n2,
      eval s (val_add (val_int n1) (val_int n2)) s (val_int (n1 + n2))
  | eval_div : forall s n1 n2,
      n2 <> 0 ->
      eval s (val_div (val_int n1) (val_int n2)) s (val_int (Z.quot n1 n2))

(** 6. [eval] for primitive operations on memory.

      There remains to describe operations that act on the mutable store.

      [val_ref v] allocates a fresh cell with contents [v]. The operation
      returns the location, written [p], of the new cell. This location
      must not be previously in the domain of the store [s].

      [val_get (val_loc p)] reads the value in the store [s] at location [p].
      The location must be bound to a value in the store, else evaluation
      is stuck.

      [val_set (val_loc p) v] updates the store at a location [p] assumed to
      be bound in the store [s]. The operation modifies the store and returns
      the unit value.

      [val_free (val_loc p)] deallocates the cell at location [p]. *)

  | eval_ref : forall s v p,
      ~ Fmap.indom s p ->
      eval s (val_ref v) (Fmap.update s p v) (val_loc p)
  | eval_get : forall s p,
      Fmap.indom s p ->
      eval s (val_get (val_loc p)) s (Fmap.read s p)
  | eval_set : forall s p v,
      Fmap.indom s p ->
      eval s (val_set (val_loc p) v) (Fmap.update s p v) val_unit
  | eval_free : forall s p,
      Fmap.indom s p ->
      eval s (val_free (val_loc p)) (Fmap.remove s p) val_unit.

End SyntaxAndSemantics.

(* ----------------------------------------------------------------- *)
(** *** Loading of Definitions from [Direcŧ] *)

(** Throughout the rest of this file, we rely not on the definitions
    shown above, but on the definitions from [LibSepDirect.v]. The latter
    are slightly more general, yet completely equivalent to the ones
    presented above for the purpose of establishing the reasoning rules
    that we are interested in. *)

(** To reduce the clutter in the statement of lemmas, we associate default
    types to a number of common meta-variables. *)

Implicit Types x f : var.
Implicit Types b : bool.
Implicit Types p : loc.
Implicit Types n : int.
Implicit Types v w r : val.
Implicit Types t : trm.
Implicit Types h : heap.
Implicit Types s : state.
Implicit Types H : hprop.
Implicit Types Q : val->hprop.

(* ================================================================= *)
(** ** Rules for Terms *)

(** We next present reasoning rule for terms. Most of these Separation Logic
    rules have a statement essentially identical to the statement of the
    corresponding Hoare Logic rule. The main difference lies in their
    interpretation: whereas Hoare Logic pre- and post-conditions describe
    the full state, a Separation Logic rule describes only a fraction of
    the mutable state. *)

(* ----------------------------------------------------------------- *)
(** *** Reasoning Rule for Sequences *)

(** Let us begin with the reasoning rule for sequences.
    The Separation Logic reasoning rule for a sequence [t1;t2] is
    essentially the same as that from Hoare logic. The rule is:

      {H} t1 {fun v => H1}     {H1} t2 {Q}
      ------------------------------------
              {H} (t1;t2) {Q}

    The Coq statement corresponding to the above rule is: *)

Parameter triple_seq : forall t1 t2 H Q H1,
  triple t1 H (fun v => H1) ->
  triple t2 H1 Q ->
  triple (trm_seq t1 t2) H Q.

(** The variable [v] denotes the result of the evaluation of [t1]. For
    well-typed programs, this result would always be [val_unit]. Yet,
    because we here consider an untyped language, we do not bother
    adding the constraint [v = val_unit]. Instead, we simply treat the
    result of [t1] as a value irrelevant to the remaining of the
    evaluation. *)

(* ----------------------------------------------------------------- *)
(** *** Reasoning Rule for Let-Bindings *)

(** Next, we present the reasoning rule for let-bindings. Here again,
    there is nothing specific to Separation Logic, the rule would be
    exactly the same in Hoare Logic.

    The reasoning rule for a let binding [let x = t1 in t2] could
    be stated, in informal writing, in the form:

      {H} t1 {Q1}     (forall x, {Q1 x} t2 {Q})
      -----------------------------------------
            {H} (let x = t1 in t2) {Q}

  Yet, such a presentation makes a confusion between the [x] that
  denotes a program variable in [let x = t1 in t2], and the [x]
  that denotes a value when quantified as [forall x].

  The correct statement involves a substitution from the variable
  [x] to a value quantified as [forall (v:val)].

      {H} t1 {Q1}     (forall v, {Q1 v} (subst x v t2) {Q})
      -----------------------------------------------------
                {H} (let x = t1 in t2) {Q}

  The corresponding Coq statement is thus as follows. *)

Parameter triple_let : forall x t1 t2 Q1 H Q,
  triple t1 H Q1 ->
  (forall v1, triple (subst x v1 t2) (Q1 v1) Q) ->
  triple (trm_let x t1 t2) H Q.

(* ----------------------------------------------------------------- *)
(** *** Reasoning Rule for Conditionals *)

(** The rule for a conditional is, again, exactly like in Hoare logic.

      b = true -> {H} t1 {Q}     b = false -> {H} t2 {Q}
      --------------------------------------------------
               {H} (if b then t1 in t2) {Q}

  The corresponding Coq statement appears next.
*)

Parameter triple_if_case : forall b t1 t2 H Q,
  (b = true -> triple t1 H Q) ->
  (b = false -> triple t2 H Q) ->
  triple (trm_if (val_bool b) t1 t2) H Q.

(** Note that the two premises may be factorized into a single one
    using Coq's conditional construct. Such an alternative
    statement is discussed further in this chapter. *)

(* ----------------------------------------------------------------- *)
(** *** Reasoning Rule for Values *)

(** The rule for a value [v] can be written as a triple with an
    empty precondition and a postcondition asserting that the
    result value [r] is equal to [v], in the empty heap. Formally:

     ----------------------------
      {\[]} v {fun r => \[r = v]}

    It is however more convenient in practice to work with a judgment
    whose conclusion is of the form [{H} v {Q}], for an arbitrary
    [H] and [Q]. For this reason, we prever the following rule for
    values.

      H ==> Q v
      ---------
      {H} v {Q}

    It may not be completely obvious at first sight why this alternative
    rule is equivalent to the former. We prove the equivalence further
    in this chapter.

    The Coq statement of the rule for values is thus as follows. *)

Parameter triple_val : forall v H Q,
  H ==> Q v ->
  triple (trm_val v) H Q.

(** Let us prove that the "minimalistic" rule [{\[]} v {fun r => \[r = v]}]
    is equivalent to [triple_val]. *)

(** **** Exercise: 1 star, standard, especially useful (triple_val_minimal)

    Prove that the alternative rule for values derivable from
    [triple_val]. Hint: use the tactic [xsimpl] to conclude the proof. *)

Lemma triple_val_minimal : forall v,
  triple (trm_val v) \[] (fun r => \[r = v]).
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 2 stars, standard, especially useful (triple_val')

    More interestingly, prove that [triple_val] is derivable
    from [triple_val_minimal]. Hint: you will need to exploit
    the appropriate structural rule(s). *)

Lemma triple_val' : forall v H Q,
  H ==> Q v ->
  triple (trm_val v) H Q.
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 4 stars, standard, especially useful (triple_let_val)

    Consider a term of the form [let x = v1 in t2], that is, where the
    argument of the let-binding is already a value. State and prove a
    reasoning rule of the form:

      Lemma triple_let_val : forall x v1 t2 H Q,
        ... ->
        triple (trm_let x v1 t2) H Q.

    Hint: you'll need to guess the intermediate postcondition [Q1] associated
    with the let-binding rule, and exploit the appropriate structural rules. *)

(* FILL IN HERE *)

(** [] *)

(* ----------------------------------------------------------------- *)
(** *** Reasoning Rule for Functions *)

(** In addition to the reasoning rule for values, we need reasoning
    rules for functions and recursive functions that appear as terms
    in the source program (as opposed to appearing as values).

    A function definition [trm_fun x t1], expressed as a subterm in a
    program, evaluates to a value, more precisely to [val_fun x t1].
    Again, we could consider a rule with an empty precondition:

     ------------------------------------------------------
      {\[]} (trm_fun x t1) {fun r => \[r = val_fun x t1]}

   However, we prefer a conclusion of the form [{H} (trm_fun x t1) {Q}].
   We thus consider the following rule, very similar to [triple_val]. *)

Parameter triple_fun : forall x t1 H Q,
  H ==> Q (val_fun x t1) ->
  triple (trm_fun x t1) H Q.

(** The rule for recursive functions is similar. It is presented
    further in the file. *)

(** Last but not least, we need a reasoning rule to reason about a
    function application. Consider an application [trm_app v1 v2].
    Assume [v1] to be a function, that is, to be of the form
    [val_fun x t1]. Then, according to the beta-reduction rule, the
    semantics of [trm_app v1 v2] is the same as that of [subst x v2 t1].
    This reasoning rule is thus:

     v1 = val_fun x t1     {H} (subst x v2 t1) {Q}
     ---------------------------------------------
      {H} (trm_app v1 v2) {Q}

   The corresponding Coq statement is as shown below. *)

Parameter triple_app_fun : forall x v1 v2 t1 H Q,
  v1 = val_fun x t1 ->
  triple (subst x v2 t1) H Q ->
  triple (trm_app v1 v2) H Q.

(** The generalization to the application of recursive functions is
    straightforward. It is discussed further in this chapter. *)

(* ================================================================= *)
(** ** Specification of Primitive Operations *)

(** Before we can tackle verification of actual programs, there remains
    to present the specifications for the primitive operations.
    Let us begin with basic arithmetic operations: addition and division. *)

(* ----------------------------------------------------------------- *)
(** *** Specification of Arithmetic Primitive Operations *)

(** Consider a term of the form [val_add n1 n2], which is short for
    [trm_app (trm_app (trm_val val_add) (val_int n1)) (val_int n2)].
    Indeed, recall that [val_int] is declared as a coercion.

    The addition operation may execute in an empty state. It does not
    modify the state, and returns the value [val_int (n1+n2)].

    In the specification shown below, the precondition is written [\[]]
    and the postcondition binds a return value [r] of type [val]
    specified to be equal to [val_int (n1+n2)]. *)

Parameter triple_add : forall n1 n2,
  triple (val_add n1 n2)
    \[]
    (fun r => \[r = val_int (n1 + n2)]).

(** The specification of the division operation [val_div n1 n2] is similar,
    yet with the extra requirement that the argument [n2] must be nonzero.
    This requirement [n2 <> 0] is a pure fact, which can be asserted as
    part of the precondition, as follows. *)

Parameter triple_div : forall n1 n2,
  triple (val_div n1 n2)
    \[n2 <> 0]
    (fun r => \[r = val_int (Z.quot n1 n2)]).

(** Equivalently, the requirement [n2 <> 0] may be asserted as an
    hypothesis to the front of the triple judgment, in the form of
    a standard Coq hypothesis, as shown below. *)

Parameter triple_div' : forall n1 n2,
  n2 <> 0 ->
  triple (val_div n1 n2)
    \[]
    (fun r => \[r = val_int (Z.quot n1 n2)]).

(** This latter presentation with pure facts such as [n2 <> 0] placed
    to the front of the triple turns out to be more practical to exploit
    in proofs. Hence, we always follow this style of presentation, and
    reserve the precondition for describing pieces of mutable state. *)

(* ----------------------------------------------------------------- *)
(** *** Specification of Primitive Operations Acting on Memory *)

(** There remains to describe the specification of operations on the heap. *)

(** Recall that [val_get] denotes the operation for reading a memory cell.
    A call of the form [val_get v'] executes safely if [v'] is of the
    form [val_loc p] for some location [p], in a state that features
    a memory cell at location [p], storing some contents [v]. Such a state
    is described as [p ~~> v]. The read operation returns a value [r]
    such that [r = v], and the memory state of the operation remains
    unchanged. The specification of [val_get] is thus expressed as follows. *)

Parameter triple_get : forall v p,
  triple (val_get (val_loc p))
    (p ~~> v)
    (fun r => \[r = v] \* (p ~~> v)).

(** Remark: [val_loc] is registered as a coercion, so [val_get (val_loc p)]
    could be written simply as [val_get p], where [p] has type [loc].
    We here chose to write [val_loc] explicitly for clarity. *)

(** Recall that [val_set] denotes the operation for writing a memory cell.
    A call of the form [val_set v' w] executes safely if [v'] is of the
    form [val_loc p] for some location [p], in a state [p ~~> v].
    The write operation updates this state to [p ~~> w], and returns
    the unit value, which can be ignored. Hence, [val_set] is specified
    as follows. *)

Parameter triple_set : forall w p v,
  triple (val_set (val_loc p) w)
    (p ~~> v)
    (fun _ => p ~~> w).

(** Recall that [val_ref] denotes the operation for allocating a cell
    with a given contents. A call to [val_ref v] does not depend on
    the contents of the existing state. It extends the state with a fresh
    singleton cell, at some location [p], assigning it [v] as contents.
    The fresh cell is then described by the heap predicate [p ~~> v].
    The evaluation of [val_ref v] produces the value [val_loc p]. Thus,
    if [r] denotes the result value, we have [r = val_loc p] for some [p].
    In the corresponding specification shown below, observe how the
    location [p] is existentially quantified in the postcondition. *)

Parameter triple_ref : forall v,
  triple (val_ref v)
    \[]
    (fun (r:val) => \exists (p:loc), \[r = val_loc p] \* p ~~> v).

(** Using the notation [funloc p => H] as a shorthand for
    [fun (r:val) => \exists (p:loc), \[r = val_loc p] \* H],
    the specification for [val_ref] becomes more concise. *)

Parameter triple_ref' : forall v,
  triple (val_ref v)
    \[]
    (funloc p => p ~~> v).

(** Recall that [val_free] denotes the operation for deallocating a cell
    at a given address. A call of the form [val_free p] executes safely
    in a state [p ~~> v]. The operation leaves an empty state, and
    asserts that the return value, named [r], is equal to unit. *)

Parameter triple_free : forall p v,
  triple (val_free (val_loc p))
    (p ~~> v)
    (fun _ => \[]).

(* ================================================================= *)
(** ** Review of the Structural Rules *)

(** Let us review the essential structural rules, which were introduced
    in the previous chapters. These structural rules are involved in
    the practical verification proofs carried out further in this chapter. *)

(** The frame rule asserts that the precondition and the postcondition
    can be extended together by an arbitrary heap predicate.
    Recall that the definition of [triple] was set up precisely to
    validate this frame rule, so in a sense in holds "by construction". *)

Parameter triple_frame : forall t H Q H',
  triple t H Q ->
  triple t (H \* H') (Q \*+ H').

(** The consequence rule allows to strengthen the precondition and
    weaken the postcondition. *)

Parameter triple_conseq : forall t H' Q' H Q,
  triple t H' Q' ->
  H ==> H' ->
  Q' ===> Q ->
  triple t H Q.

(** In practice, it is most convenient to exploit a rule that combines
    both frame and consequence into a single rule, as stated next.
    (Note that this "combined structural rule" was proved as an exercise
    in chapter [Himpl].) *)

Parameter triple_conseq_frame : forall H2 H1 Q1 t H Q,
  triple t H1 Q1 ->
  H ==> H1 \* H2 ->
  Q1 \*+ H2 ===> Q ->
  triple t H Q.

(** The two extraction rules enable to extract pure facts and existentially
    quantified variables, from the precondition into the Coq context. *)

Parameter triple_hpure : forall t (P:Prop) H Q,
  (P -> triple t H Q) ->
  triple t (\[P] \* H) Q.

Parameter triple_hexists : forall t (A:Type) (J:A->hprop) Q,
  (forall (x:A), triple t (J x) Q) ->
  triple t (\exists (x:A), J x) Q.

(** **** Exercise: 1 star, standard, optional (triple_hpure')

    The extraction rule [triple_hpure] assumes a precondition of the form
    [\[P] \* H]. The variant rule [triple_hpure'], stated below, assumes
    instead a precondition with only the pure part, i.e., of the form [\[P]].
    Prove that [triple_hpure'] is indeed a corollary of [triple_hpure]. *)

Lemma triple_hpure' : forall t (P:Prop) Q,
  (P -> triple t \[] Q) ->
  triple t \[P] Q.
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(* ================================================================= *)
(** ** Verification Proof in Separation Logic *)

(** We have at hand all the necessary rules for carrying out actual
    verification proofs in Separation Logic. Let's do it! *)

Module ExamplePrograms.
Export ProgramSyntax.

(* ----------------------------------------------------------------- *)
(** *** Proof of [incr] *)

(** First, we consider the verification of the increment function,
    which is written in OCaml syntax as:

OCaml:

   let incr p =
      p := !p + 1

    Recall that, for simplicity, we assume programs to be written in
    "A-normal form", that is, with all intermediate expressions named
    by a let-binding. Thereafter, we thus consider the following
    definition for the [incr].

OCaml:

   let incr p =
      let n = !p in
      let m = n+1 in
      p := m

    Using the construct from our toy programming language, the definition
    of [incr] is written as shown below. *)

Definition incr : val :=
  val_fun "p" (
    trm_let "n" (trm_app val_get (trm_var "p")) (
    trm_let "m" (trm_app (trm_app val_add
                             (trm_var "n")) (val_int 1)) (
    trm_app (trm_app val_set (trm_var "p")) (trm_var "m")))).

(** Alternatively, using notation and coercions, the same program can be
    written as shown below. *)

Definition incr' : val :=
  <{ fun 'p =>
       let 'n = ! 'p in
       let 'm = 'n + 1 in
       'p := 'm }>.

(** Let us check that the two definitions are indeed the same. *)

Lemma incr_eq_incr' :
  incr = incr'.
Proof using. reflexivity. Qed.

(** Recall from the first chapter the specification of the increment function.
    Its precondition requires a singleton state of the form [p ~~> n].
    Its postcondition describes a state of the form [p ~~> (n+1)]. *)

Lemma triple_incr : forall (p:loc) (n:int),
  triple (trm_app incr p)
    (p ~~> n)
    (fun _ => p ~~> (n+1)).

(** We next show a detailed proof for this specification. It exploits:

    - the structural reasoning rules,
    - the reasoning rules for terms,
    - the specification of the primitive functions,
    - the [xsimpl] tactic for simplifying entailments.
*)

Proof using.
  (* initialize the proof *)
  intros. applys triple_app_fun. { reflexivity. } simpl.
  (* reason about [let n = ..] *)
  applys triple_let.
  (* reason about [!p] *)
  { apply triple_get. }
  (* name [n'] the result of [!p] *)
  intros n'. simpl.
  (* substitute away the equality [n' = n] *)
  apply triple_hpure. intros ->.
  (* reason about [let m = ..] *)
  applys triple_let.
  (* apply the frame rule to put aside [p ~~> n] *)
  { applys triple_conseq_frame.
    (* reason about [n+1] in the empty state *)
    { applys triple_add. }
    { xsimpl. }
    { xsimpl. } }
  (* name [m'] the result of [n+1] *)
  intros m'. simpl.
  (* substitute away the equality [m' = m] *)
  apply triple_hpure. intros ->.
  (* reason about [p := m] *)
  { applys triple_set. }
Qed.

(* ----------------------------------------------------------------- *)
(** *** Proof of [succ_using_incr] *)

(** Recall from [Basic] the function [succ_using_incr]. *)

Definition succ_using_incr : val :=
  <{ fun 'n =>
       let 'r = val_ref 'n in
       incr 'r;
       let 'x = ! 'r in
       val_free 'r;
       'x }>.

(** Recall the specification of [succ_using_incr]. *)

Lemma triple_succ_using_incr : forall (n:int),
  triple (trm_app succ_using_incr n)
    \[]
    (fun v => \[v = val_int (n+1)]).

(** **** Exercise: 4 stars, standard, especially useful (triple_succ_using_incr)

    Verify the function [triple_succ_using_incr].
    Hint: follow the pattern of [triple_incr].
    Hint: use [applys triple_seq] for reasoning about a sequence.
    Hint: use [applys triple_val] for reasoning about the final
    return value, namely [x]. *)

Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(* ----------------------------------------------------------------- *)
(** *** Proof of [factorec] *)

Import Basic.Facto.

(** Recall from [Basic] the function [repeat_incr].

OCaml:

    let rec factorec n =
      if n <= 1 then 1 else n * factorec (n-1)
*)

Definition factorec : val :=
  <{ fix 'f 'n =>
       let 'b = ('n <= 1) in
       if 'b
         then 1
         else let 'x = 'n - 1 in
              let 'y = 'f 'x in
              'n * 'y }>.

(** **** Exercise: 4 stars, standard, especially useful (triple_factorec)

    Verify the function [factorec].
    Hint: exploit [triple_app_fix] for reasoning about the recursive function.
    Hint: [triple_hpure'], the corollary of [triple_hpure], is helpful.
    Hint: exploit [triple_le] and [triple_sub] and [triple_mul] to reason about
    the behavior of the primitive operations involved.
    Hint: exploit [applys triple_if. case_if as C.] to reason about the
    conditional; alternatively, if using [triple_if_case], you'll need to use
    the tactic [rew_bool_eq in *] to simplify, e.g., the expression
    [isTrue (m <= 1)) = true]. *)

Lemma triple_factorec : forall n,
  n >= 0 ->
  triple (factorec n)
    \[]
    (fun r => \[r = facto n]).
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

End ExamplePrograms.

(* ================================================================= *)
(** ** What's Next *)

(** The matter of the next chapter is to introduce additional
    technology to streamline the proof process, notably by:

    - automating the application of the frame rule
    - eliminating the need to manipulate program variables
      and substitutions during the verification proof. *)

(** The rest of this chapter is concerned with alternative statements
    for the reasoning rules, and with the proofs of the reasoning rules. *)

(* ################################################################# *)
(** * More Details *)

(* ================================================================= *)
(** ** Alternative Specification Style for Pure Preconditions *)

Module DivSpec.

(** Recall the specification for division. *)

Parameter triple_div : forall n1 n2,
  n2 <> 0 ->
  triple (val_div n1 n2)
    \[]
    (fun r => \[r = val_int (Z.quot n1 n2)]).

(** Equivalently, we could place the requirement [n2 <> 0] in the
    precondition: *)

Parameter triple_div' : forall n1 n2,
  triple (val_div n1 n2)
    \[n2 <> 0]
    (fun r => \[r = val_int (Z.quot n1 n2)]).

(** Let us formally prove that the two presentations are equivalent. *)

(** **** Exercise: 1 star, standard, especially useful (triple_div_from_triple_div')

    Prove [triple_div] by exploiting [triple_div'].
    Hint: the key proof step is [applys triple_conseq] *)

Lemma triple_div_from_triple_div' : forall n1 n2,
  n2 <> 0 ->
  triple (val_div n1 n2)
    \[]
    (fun r => \[r = val_int (Z.quot n1 n2)]).
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 2 stars, standard, especially useful (triple_div'_from_triple_div)

    Prove [triple_div'] by exploiting [triple_div].
    Hint: the first key proof step is [applys triple_hpure].
    Yet some preliminary rewriting is required for this
    tactic to apply.
    Hint: the second key proof step is [applys triple_conseq]. *)

Lemma triple_div'_from_triple_div : forall n1 n2,
  triple (val_div n1 n2)
    \[n2 <> 0]
    (fun r => \[r = val_int (Z.quot n1 n2)]).
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** As we said, placing pure preconditions outside of the triples
    makes it slightly more convenient to exploit specifications.
    For this reason, we adopt the style that precondition only
    contain the description of heap-allocated data structures. *)

End DivSpec.

(* ================================================================= *)
(** ** The Combined let-frame Rule Rule *)

Module LetFrame.

(** Recall the Separation Logic let rule. *)

Parameter triple_let : forall x t1 t2 Q1 H Q,
  triple t1 H Q1 ->
  (forall v1, triple (subst x v1 t2) (Q1 v1) Q) ->
  triple (trm_let x t1 t2) H Q.

(** At first sight, it seems that, to reason about [let x = t1 in t2]
    in a state described by precondition [H], we need to first reason
    about [t1] in that same state. Yet, [t1] may well require only a
    subset of the state [H] to evaluate, and not all of [H].

    The "let-frame" rule combines the rule for let-bindings with the
    frame rule to make it more explicit that the precondition [H]
    may be decomposed in the form [H1 \* H2], where [H1] is the part
    needed by [t1], and [H2] denotes the rest of the state. The part
    of the state covered by [H2] remains unmodified during the evaluation
    of [t1], and appears as part of the precondition of [t2].

    The corresponding statement is as follows. *)

Lemma triple_let_frame : forall x t1 t2 Q1 H H1 H2 Q,
  triple t1 H1 Q1 ->
  H ==> H1 \* H2 ->
  (forall v1, triple (subst x v1 t2) (Q1 v1 \* H2) Q) ->
  triple (trm_let x t1 t2) H Q.

(** **** Exercise: 3 stars, standard, especially useful (triple_let_frame)

    Prove the let-frame rule. *)

Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

End LetFrame.

(* ================================================================= *)
(** ** Proofs for the Rules for Terms *)

Module Proofs.

(** The proofs for the Separation Logic reasoning rules all follow
    a similar pattern: first establish a corresponding rule for
    Hoare triples, then generalize it to a Separation Logic triple.

    To establish a reasoning rule w.r.t. a Hoare triple, we reveal
    the definition expressed in terms of the big-step semantics.

      Definition hoare (t:trm) (H:hprop) (Q:val->hprop) : Prop :=
        forall s, H s ->
        exists s' v, eval s t s' v /\ Q v s'.

    Concretely, we consider a given initial state [s] satisfying the
    precondition, and we have to provide witnesses for the output
    value [v] and output state [s'] such that the reduction holds and
    the postcondition holds.

    Then, to lift the reasoning rule from Hoare logic to Separation
    Logic, we reveal the definition of a Separation Logic triple.

      Definition triple t H Q :=
       forall H', hoare t (H \* H') (Q \*+ H').

    Recall that we already employed this two-step scheme in the
    previous chapter, e.g., to establish the consequence rule
    ([rule_conseq]). *)

(* ----------------------------------------------------------------- *)
(** *** Proof of [triple_val] *)

(** The big-step evaluation rule for values asserts that a value [v]
    evaluates to itself, without modification to the current state [s]. *)

Parameter eval_val : forall s v,
  eval s v s v.

(** The Hoare version of the reasoning rule for values is as follows. *)

Lemma hoare_val : forall v H Q,
  H ==> Q v ->
  hoare (trm_val v) H Q.
Proof using.
(** 1. We unfold the definition of [hoare]. *)
  introv M. intros s K0.
(** 2. We provide the witnesses for the output value and heap.
        These witnesses are dictated by the statement of [eval_val]. *)
  exists s v. splits.
(** 3. We invoke the big-step rule [eval_val] *)
  { applys eval_val. }
(** 4. We establish the postcondition, exploiting the entailment hypothesis. *)
  { applys M. auto. }
Qed.

(** The Separation Logic version of the rule then follows. *)

Lemma triple_val : forall v H Q,
  H ==> Q v ->
  triple (trm_val v) H Q.
Proof using.
(** 1. We unfold the definition of [triple] to reveal a [hoare] judgment. *)
  introv M. intros H'.
(** 2. We invoke the reasoning rule [hoare_val] that was just established. *)
  applys hoare_val.
(** 3. We exploit the assumption and conclude using [xchange]. *)
  xchange M.
Qed.

(* ----------------------------------------------------------------- *)
(** *** Proof of [triple_seq] *)

(** The big-step evaluation rule for a sequence is given next. *)

Parameter eval_seq : forall s1 s2 s3 t1 t2 v1 v,
  eval s1 t1 s2 v1 ->
  eval s2 t2 s3 v ->
  eval s1 (trm_seq t1 t2) s3 v.

(** The Hoare triple version of the reasoning rule is proved as follows.
    This lemma, called [hoare_seq], has the same statement as [triple_seq],
    except with occurrences of [triple] replaced with [hoare]. *)

Lemma hoare_seq : forall t1 t2 H Q H1,
  hoare t1 H (fun v => H1) ->
  hoare t2 H1 Q ->
  hoare (trm_seq t1 t2) H Q.
Proof using.
(** 1. We unfold the definition of [hoare].
  Let [K0] describe the initial state. *)
  introv M1 M2. intros s K0. (* optional: *) unfolds hoare.
(** 2. We exploit the first hypothesis to obtain information about
       the evaluation of the first subterm [t1].
       The state before [t1] executes is described by [K0].
       The state after [t1] executes is described by [K1]. *)
  forwards (s1'&v1&R1&K1): (rm M1) K0.
(** 3. We exploit the second hypothesis to obtain information about
       the evaluation of the first subterm [t2].
       The state before [t2] executes is described by [K1].
       The state after [t2] executes is described by [K2]. *)
  forwards (s2'&v2&R2&K2): (rm M2) K1.
(** 4. We provide witness for the output value and heap.
       They correspond to those produced by the evaluation of [t2]. *)
  exists s2' v2. split.
(** 5. We invoke the big-step rule. *)
  { applys eval_seq R1 R2. }
(** 6. We establish the final postcondition, which is directly
          inherited from the reasoning on [t2]. *)
  { apply K2. }
Qed.

(** The Separation Logic reasoning rule is proved as follows. *)

Lemma triple_seq : forall t1 t2 H Q H1,
  triple t1 H (fun v => H1) ->
  triple t2 H1 Q ->
  triple (trm_seq t1 t2) H Q.
Proof using.
(** 1. We unfold the definition of [triple] to reveal a [hoare] judgment. *)
  introv M1 M2. intros H'. (* optional: *) unfolds triple.
(** 2. We invoke the reasoning rule [hoare_seq] that we just established. *)
  applys hoare_seq.
(** 3. For the hypothesis on the first subterm [t1],
       we can invoke directly our first hypothesis. *)
  { applys M1. }
  { applys M2. }
Qed.

(* ----------------------------------------------------------------- *)
(** *** Proof of [triple_let] *)

(** Recall the big-step evaluation rule for a let-binding. *)

Parameter eval_let : forall s1 s2 s3 x t1 t2 v1 v,
  eval s1 t1 s2 v1 ->
  eval s2 (subst x v1 t2) s3 v ->
  eval s1 (trm_let x t1 t2) s3 v.

(** **** Exercise: 3 stars, standard, especially useful (triple_let)

    Following the same proof scheme as for [triple_seq], establish
    the reasoning rule for [triple_let], whose statement appears
    earlier in this file. Make sure to first state and prove the
    lemma [hoare_let], which has the same statement as [triple_let]
    yet with occurrences of [triple] replaced with [hoare]. *)

(* FILL IN HERE *)

(** [] *)

(* ================================================================= *)
(** ** Proofs for the Arithmetic Primitive Operations *)

(* ----------------------------------------------------------------- *)
(** *** Addition *)

(** Recall the evaluation rule for addition. *)

Parameter eval_add : forall s n1 n2,
  eval s (val_add (val_int n1) (val_int n2)) s (val_int (n1 + n2)).

(** In the proof, we will need to use the following result,
    established in the first chapter. *)

Parameter hstar_hpure_l : forall P H h,
  (\[P] \* H) h = (P /\ H h).

(** As usual, we first establish a Hoare triple. *)

Lemma hoare_add : forall H n1 n2,
  hoare (val_add n1 n2)
    H
    (fun r => \[r = val_int (n1 + n2)] \* H).
Proof using.
  intros. intros s K0. exists s (val_int (n1 + n2)). split.
  { applys eval_add. }
  { rewrite hstar_hpure_l. split.
    { auto. }
    { applys K0. } }
Qed.

(** Deriving [triple_add] is then straightforward. *)

Lemma triple_add : forall n1 n2,
  triple (val_add n1 n2)
    \[]
    (fun r => \[r = val_int (n1 + n2)]).
Proof using.
  intros. intros H'. applys hoare_conseq.
  { applys hoare_add. } { xsimpl. } { xsimpl. auto. }
Qed.

(* ----------------------------------------------------------------- *)
(** *** Division *)

(** Recall the evaluation rule for division. *)

Parameter eval_div' : forall s n1 n2,
  n2 <> 0 ->
  eval s (val_div (val_int n1) (val_int n2)) s (val_int (Z.quot n1 n2)).

(** **** Exercise: 3 stars, standard, optional (triple_div)

    Following the same proof scheme as for [triple_add], establish
    the reasoning rule for [triple_div]. Make sure to first state
    and prove [hoare_div], which is like [triple_div] except with
    [hoare] instead of [triple]. *)

(* FILL IN HERE *)

(** [] *)

(* ================================================================= *)
(** ** Proofs for Primitive Operations Operating on the State *)

(** The proofs for establishing the Separation Logic reasoning rules
    for [ref], [get] and [set] follow a similar proof pattern,
    that is, they go through the proofs of rules for Hoare triples.

    Unlike before, however, the Hoare triples are not directly
    established with respect to the big-step evaluation rules.
    Instead, we start by proving corollaries to the big-step rules
    to reformulate them in a way that give already them a flavor
    of "Separation Logic". Concretely, we reformulate the evaluation
    rules, which are expressed in terms of read and updates in finite
    maps, to be expressed instead entirely in terms of disjoint unions.

    The introduction of these disjoint union operations then
    significantly eases the justification of the separating
    conjunctions that appear in the targeted Separation Logic
    triples.

    In this section, the constructor [hval_val] appears. This
    constructor converts a "value" into a "heap value". For the
    purpose, of this file, the two notion are identical. Yet,
    to allow for generalization to the semantics of allocation by
    blocks, we need to assume that states are finite maps from
    location to heap values. Heap values, of type [hval], can be
    assumed to be defined by the following inductive data type.

    Inductive hval : Type :=
      | hval_val : val -> hval.
*)

(* ----------------------------------------------------------------- *)
(** *** Read in a Reference *)

(** The big-step rule for [get p] requires that [p] be in the
    domain of the current state [s], and asserts that the output
    value is the result of reading in [s] at location [p]. *)

Parameter eval_get : forall v s p,
  Fmap.indom s p ->
  Fmap.read s p = v ->
  eval s (val_get (val_loc p)) s v.

(** We reformulate this rule by isolating from the current state [s]
    the singleton heap made of the cell at location [p], and let [s2]
    denote the rest of the heap. When the singleton heap is described
    as [Fmap.single p v], then [v] is the result value returned by
    [get p]. *)

Lemma eval_get_sep : forall s s2 p v,
  s = Fmap.union (Fmap.single p v) s2 ->
  eval s (val_get (val_loc p)) s v.

(** The proof of this lemma is of little interest. We show it only to
    demonstrate that it relies only a few basic facts related to finite
    maps. *)

Proof using.
  introv ->. forwards Dv: Fmap.indom_single p v.
  applys eval_get.
  { applys* Fmap.indom_union_l. }
  { rewrite* Fmap.read_union_l. rewrite* Fmap.read_single. }
Qed.

(** Our goal is to establish the triple:

    triple (val_get p)
      (p ~~> v)
      (fun r => \[r = v] \* (p ~~> v)).

    Establishing this lemma requires us to reason about propositions
    of the form [(\[P] \* H) h] and [(p ~~> v) h]. To that end,
    recall lemma [hstar_hpure_l], which was already exploited in the
    proof of [triple_add], and recall [hsingle_inv] from [Hprop]. *)

Parameter hsingle_inv: forall p v h,
  (p ~~> v) h ->
  h = Fmap.single p v.

(** We establish the specification of [get] first w.r.t. to
    the [hoare] judgment. *)

Lemma hoare_get : forall H v p,
  hoare (val_get p)
    ((p ~~> v) \* H)
    (fun r => \[r = v] \* (p ~~> v) \* H).
Proof using.
  (* 1. We unfold the definition of [hoare]. *)
  intros. intros s K0.
  (* 2. We provide the witnesses for the reduction,
        as dictated by [eval_get_sep]. *)
  exists s v. split.
  { (* 3. To justify the reduction using [eval_get_sep], we need to
          argue that the state [s] decomposes as a singleton heap
          [Fmap.single p v] and the rest of the state [s2]. This is
          obtained by eliminating the star in hypothesis [K0]. *)
    destruct K0 as (s1&s2&P1&P2&D&U).
    (* 4. Inverting [(p ~~> v) h1] simplifies the goal. *)
    lets E1: hsingle_inv P1. subst s1.
    (* 5. At this point, the goal matches exactly [eval_get_sep]. *)
    applys eval_get_sep U. }
  { (* 6. To establish the postcondition, we check the pure fact
          \[v = v], and check that the state, which has not changed,
          satisfies the same heap predicate as in the precondition. *)
    rewrite hstar_hpure_l. auto. }
Qed.

(** Deriving the Separation Logic triple follows the usual pattern. *)

Lemma triple_get : forall v p,
  triple (val_get p)
    (p ~~> v)
    (fun r => \[r = v] \* (p ~~> v)).
Proof using.
  intros. intros H'. applys hoare_conseq.
  { applys hoare_get. }
  { xsimpl. }
  { xsimpl. auto. }
Qed.

(* ----------------------------------------------------------------- *)
(** *** Allocation of a Reference *)

(** Next, we consider the reasoning rule for operation [ref], which
    involves a proof yet slightly more trickier than that for
    [get] and [set]. *)

(** The big-step evaluation rule for [ref v] extends the initial
    state [s] with an extra binding from [p] to [v], for some
    fresh location [p]. *)

Parameter eval_ref : forall s v p,
  ~ Fmap.indom s p ->
  eval s (val_ref v) (Fmap.update s p v) (val_loc p).

(** Let us reformulate [eval_ref] to replace references to [Fmap.indom]
    and [Fmap.update] with references to [Fmap.single] and [Fmap.disjoint].
    Concretely, [ref v] extends the state from [s1] to [s1 \u s2],
    where [s2] denotes the singleton heap [Fmap.single p v], and with
    the requirement that [Fmap.disjoint s2 s1], to capture freshness. *)

Lemma eval_ref_sep : forall s1 s2 v p,
  s2 = Fmap.single p v ->
  Fmap.disjoint s2 s1 ->
  eval s1 (val_ref v) (Fmap.union s2 s1) (val_loc p).
Proof using.
(** It is not needed to follow through this proof. *)
  introv -> D. forwards Dv: Fmap.indom_single p v.
  rewrite <- Fmap.update_eq_union_single. applys* eval_ref.
  { intros N. applys* Fmap.disjoint_inv_not_indom_both D N. }
Qed.

(** In order to apply the rules [eval_ref] or [eval_ref_sep], we need
    to be able to synthetize fresh locations. The following lemma
    (from [LibSepFmap.v]) captures the existence, for any state [s], of
    a (non-null) location [p] not already bound in [s]. *)

Parameter exists_fresh : forall s,
   exists p, ~ Fmap.indom s p /\ p <> null.

(** We reformulate the lemma above in a way that better matches
    the premise of the lemma [eval_ref_sep], which we need to apply
    for establishing the specification of [ref].

    This reformulation, shown below, asserts that, for any [h],
    there existence a non-null location [p] such that the singleton
    heap [Fmap.single p v] is disjoint from [h]. *)

Lemma single_fresh : forall h v,
  exists p, Fmap.disjoint (Fmap.single p v) h.
Proof using.
(** It is not needed to follow through this proof. *)
  intros. forwards (p&F&N): exists_fresh h.
  exists p. applys* Fmap.disjoint_single_of_not_indom.
Qed.

(** The proof of the Hoare triple for [ref] is as follows. *)

Lemma hoare_ref : forall H v,
  hoare (val_ref v)
    H
    (fun r => (\exists p, \[r = val_loc p] \* p ~~> v) \* H).
Proof using.
  (* 1. We unfold the definition of [hoare]. *)
  intros. intros s1 K0.
  (* 2. We claim the disjointness relation
       [Fmap.disjoint (Fmap.single p v) s1]. *)
  forwards* (p&D): (single_fresh s1 v).
  (* 3. We provide the witnesses for the reduction,
        as dictated by [eval_ref_sep]. *)
  exists ((Fmap.single p v) \u s1) (val_loc p). split.
  { (* 4. We exploit [eval_ref_sep], which has exactly the desired shape! *)
    applys eval_ref_sep D. auto. }
  { (* 5. We establish the postcondition
          [(\exists p, \[r = val_loc p] \* p ~~> v) \* H]
          by providing [p] and the relevant pieces of heap. *)
    applys hstar_intro.
    { exists p. rewrite hstar_hpure_l.
      split. { auto. } { applys~ hsingle_intro. } }
    { applys K0. }
    { applys D. } }
Qed.

(** We then derive the Separation Logic triple as usual. *)

Lemma triple_ref : forall v,
  triple (val_ref v)
    \[]
    (funloc p => p ~~> v).
Proof using.
  intros. intros H'. applys hoare_conseq.
  { applys hoare_ref. }
  { xsimpl. }
  { xsimpl. auto. }
Qed.

End Proofs.

(* ################################################################# *)
(** * Optional Material *)

(* ================================================================= *)
(** ** Reasoning Rules for Recursive Functions *)

(** This reasoning rules for functions immediately generalizes
    to recursive functions. A term describing a recursive
    function is written [trm_fix f x t1], and the corresponding
    value is written [val_fix f x t1]. *)

Parameter triple_fix : forall f x t1 H Q,
  H ==> Q (val_fix f x t1) ->
  triple (trm_fix f x t1) H Q.

(** The reasoning rule that corresponds to beta-reduction for
    a recursive function involves two substitutions: a first
    substitution for recursive occurrences of the function,
    followed with a second substitution for the argument
    provided to the call. *)

Parameter triple_app_fix : forall v1 v2 f x t1 H Q,
  v1 = val_fix f x t1 ->
  triple (subst x v2 (subst f v1 t1)) H Q ->
  triple (trm_app v1 v2) H Q.

(* ----------------------------------------------------------------- *)
(** *** Other Proofs of Reasoning Rules for Terms *)

Module ProofsContinued.

(* ----------------------------------------------------------------- *)
(** *** Proof of [triple_fun] and [triple_fix] *)

(** The proofs for [triple_fun] and [triple_fix] are essentially
    identical to that of [triple_val], so we do not include them
    here. *)

(* ----------------------------------------------------------------- *)
(** *** Proof of [triple_if] *)

(** Recall the reasoning rule for conditionals. Recall that this
    rule is stated by factorizing the premises. *)

Lemma eval_if : forall s1 s2 b v t1 t2,
  eval s1 (if b then t1 else t2) s2 v ->
  eval s1 (trm_if b t1 t2) s2 v.
Proof using.
  intros. case_if; applys eval_if; auto_false.
Qed.

(** The reasoning rule for conditional w.r.t. Hoare triples is as follows. *)

Lemma hoare_if_case : forall b t1 t2 H Q,
  (b = true -> hoare t1 H Q) ->
  (b = false -> hoare t2 H Q) ->
  hoare (trm_if b t1 t2) H Q.
Proof using.
  introv M1 M2. intros s K0. destruct b.
  { forwards* (s1'&v1&R1&K1): (rm M1) K0.
    exists s1' v1. split*. { applys* eval_if. } }
  { forwards* (s1'&v1&R1&K1): (rm M2) K0.
    exists s1' v1. split*. { applys* eval_if. } }
Qed.

(** The corresponding Separation Logic reasoning rule is as follows. *)

Lemma triple_if_case : forall b t1 t2 H Q,
  (b = true -> triple t1 H Q) ->
  (b = false -> triple t2 H Q) ->
  triple (trm_if (val_bool b) t1 t2) H Q.
Proof using.
  unfold triple. introv M1 M2. intros H'.
  applys hoare_if_case; intros Eb.
  { applys* M1. }
  { applys* M2. }
Qed.

(** Observe that the above proofs contain a fair amount of duplication,
    due to the symmetry between the [b = true] and [b = false] branches.

    If we state the reasoning rules using Coq's conditional just like
    it appears in the evaluation rule [eval_if], we can better factorize
    the proof script. *)

Lemma hoare_if : forall (b:bool) t1 t2 H Q,
  hoare (if b then t1 else t2) H Q ->
  hoare (trm_if b t1 t2) H Q.
Proof using.
  introv M1. intros s K0.
  forwards (s'&v&R1&K1): (rm M1) K0.
  exists s' v. split. { applys eval_if R1. } { applys K1. }
Qed.

Lemma triple_if : forall b t1 t2 H Q,
  triple (if b then t1 else t2) H Q ->
  triple (trm_if (val_bool b) t1 t2) H Q.
Proof using.
  unfold triple. introv M1. intros H'. applys hoare_if. applys M1.
Qed.

(* ----------------------------------------------------------------- *)
(** *** Proof of [triple_app_fun] *)

(** The reasoning rule for an application asserts that the
    a pre- and poscondition hold for a beta-redex [(val_fun x t1) v2]
    provided that they hold for the term [subst x v2 t1].

    This result follows directly from the big-step evaluation rule
    for applications. *)

Parameter eval_app_fun : forall s1 s2 v1 v2 x t1 v,
  v1 = val_fun x t1 ->
  eval s1 (subst x v2 t1) s2 v ->
  eval s1 (trm_app v1 v2) s2 v.

(** **** Exercise: 2 stars, standard, optional (hoare_app_fun)

    Prove the lemma [hoare_app_fun]. *)

Lemma hoare_app_fun : forall v1 v2 x t1 H Q,
  v1 = val_fun x t1 ->
  hoare (subst x v2 t1) H Q ->
  hoare (trm_app v1 v2) H Q.
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 2 stars, standard, optional (triple_app_fun)

    Prove the lemma [triple_app_fun]. *)

Lemma triple_app_fun : forall x v1 v2 t1 H Q,
  v1 = val_fun x t1 ->
  triple (subst x v2 t1) H Q ->
  triple (trm_app v1 v2) H Q.
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(* ----------------------------------------------------------------- *)
(** *** Deallocation of a Reference *)

(** Optional contents: this section may be safely skipped.

    Last, we consider the reasoning rule for operation [free].
    We leave this one as exercise. *)

(** Recall the big-step evaluation rule for [free p]. *)

Parameter eval_free : forall s p,
  Fmap.indom s p ->
  eval s (val_set (val_loc p)) (Fmap.remove s p) val_unit.

(** Let us reformulate [eval_free] to replace references to [Fmap.indom]
    and [Fmap.remove] with references to [Fmap.single] and [Fmap.union]
    and [Fmap.disjoint]. The details are not essential, thus omitted. *)

Parameter eval_free_sep : forall s1 s2 v p,
  s1 = Fmap.union (Fmap.single p v) s2 ->
  Fmap.disjoint (Fmap.single p v) s2 ->
  eval s1 (val_free p) s2 val_unit.

(** **** Exercise: 3 stars, standard, optional (hoare_free)

    Prove the Hoare triple for the operation [free].
    Hint: exploit the lemma [eval_free_sep]. *)

Lemma hoare_free : forall H p v,
  hoare (val_free (val_loc p))
    ((p ~~> v) \* H)
    (fun _ =>  H).
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 1 star, standard, optional (triple_free)

    Derive from the Hoare triple for the operation [free]
    the corresponding Separation Logic triple.
    Hint: adapt the proof of lemma [triple_set]. *)

Lemma triple_free : forall p v,
  triple (val_free (val_loc p))
    (p ~~> v)
    (fun _ => \[]).
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(* ----------------------------------------------------------------- *)
(** *** Write in a Reference *)

(** The big-step evaluation rule for [set p v] updates the initial
    state [s] by re-binding the location [p] to the value [v].
    The location [p] must already belong to the domain of [s]. *)

Parameter eval_set : forall m p v,
   Fmap.indom m p ->
   eval m (val_set (val_loc p) v) (Fmap.update m p v) val_unit.

(** As for [get], we first reformulate this lemma, to replace
    references to [Fmap.indom] and [Fmap.update] with references
    to [Fmap.union], [Fmap.single], and [Fmap.disjoint], to
    prepare for the introduction of separating conjunctions. *)

Lemma eval_set_sep : forall s1 s2 h2 p v1 v2,
  s1 = Fmap.union (Fmap.single p v1) h2 ->
  s2 = Fmap.union (Fmap.single p v2) h2 ->
  Fmap.disjoint (Fmap.single p v1) h2 ->
  eval s1 (val_set (val_loc p) v2) s2 val_unit.
Proof using.
(** It is not needed to follow through this proof. *)
  introv -> -> D. forwards Dv: Fmap.indom_single p v1.
  applys_eq eval_set.
  { rewrite* Fmap.update_union_l. fequals.
    rewrite* Fmap.update_single. }
  { applys* Fmap.indom_union_l. }
Qed.

(** The proof of the Hoare rule for [set] makes use of the following
    fact (from [LibSepFmap.v]) about [Fmap.disjoint]: when one of its argument
    is a singleton map, the value stored in that singleton map is irrelevant.

    Check Fmap.disjoint_single_set : forall p v1 v2 h2,
      Fmap.disjoint (Fmap.single p v1) h2 ->
      Fmap.disjoint (Fmap.single p v2) h2.
*)

(** **** Exercise: 5 stars, standard, optional (hoare_set)

    Prove the lemma [hoare_set].
    Hints:
    - exploit the evaluation rule [eval_set_sep] presented above,
    - exploit the lemma [Fmap.disjoint_single_set] presented above,
    - to obtain an elegant proof, prefer invoking the lemmas
      [hsingle_intro], [hsingle_inv], [hstar_intro], and [hstar_inv],
      rather than unfolding the definitions of [hstar] and [hsingle]. *)

Lemma hoare_set : forall H v p v',
  hoare (val_set (val_loc p) v)
    ((p ~~> v') \* H)
    (fun _ => (p ~~> v) \* H).
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** We then derive the Separation Logic triple as usual. *)

Lemma triple_set : forall w p v,
  triple (val_set (val_loc p) w)
    (p ~~> v)
    (fun _ => p ~~> w).
Proof using.
  intros. intros H'. applys hoare_conseq.
  { applys hoare_set. }
  { xsimpl. }
  { xsimpl. }
Qed.

End ProofsContinued.

(* ----------------------------------------------------------------- *)
(** *** Proofs Revisited using the [triple_of_hoare] Lemma *)

Module ProofsFactorization.

(** The proof that, e.g., [triple_add] is a consequence of
   [hoare_add] follows the same pattern as many other similar
   proofs, each time invoking the lemma [hoare_conseq].
   Thus, we could attempt at factorizing this proof pattern.
   The following lemma corresponds to such an attempt. *)

(** **** Exercise: 2 stars, standard, optional (triple_of_hoare)

    Prove the lemma [triple_of_hoare] stated below. *)

Lemma triple_of_hoare : forall t H Q,
  (forall H', exists Q', hoare t (H \* H') Q'
                     /\  Q' ===> Q \*+ H') ->
  triple t H Q.
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 2 stars, standard, optional (triple_add')

    Prove that [triple_add] is a consequence of [hoare_add] by
    exploiting [triple_of_hoare]. *)

Lemma triple_add' : forall n1 n2,
  triple (val_add n1 n2)
    \[]
    (fun r => \[r = val_int (n1 + n2)]).
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

End ProofsFactorization.

(* ----------------------------------------------------------------- *)
(** *** Triple for Terms with Same Semantics *)

Module ProofsSameSemantics.

(** A general principle is that if [t1] has the same semantics
    as [t2] (w.r.t. the big-step evaluation judgment [eval]),
    then [t1] and [t2] satisfy the same triples.

    Let us formalize this principle. *)

(** Two (closed) terms are semantically equivalent, written
    [trm_equiv t1 t2], if two terms, when evaluated in the same
    state, produce the same output. *)

Definition trm_equiv (t1 t2:trm) : Prop :=
  forall s s' v, eval s t1 s' v <-> eval s t2 s' v.

(** Two terms that are equivalent satisfy the same Separation Logic
    triples (and the same Hoare triples).

    Indeed, the definition of a Separation Logic triple directly depends
    on the notion of Hoare triple, and the latter directly depends
    on the semantics captured by the predicate [eval].

    Let us formalize the result in three steps. *)

(** [eval_like t1 t2] asserts that [t2] evaluates like [t1].
    In particular, this relation hold whenever [t2] reduces
    in small-step to [t1]. *)

Definition eval_like (t1 t2:trm) : Prop :=
  forall s s' v, eval s t1 s' v -> eval s t2 s' v.

(** For example [eval_like t (trm_let x t x)] holds, reflecting the
    fact that [let x = t in x] reduces in small-step to [t]. *)

Lemma eval_like_eta_reduction : forall (t:trm) (x:var),
  eval_like t (trm_let x t x).
Proof using.
  introv R. applys eval_let R.
  simpl. rewrite var_eq_spec. case_if. applys eval_val.
Qed.

(** It turns out that the symmetric relation [eval_like (trm_let x t x) t]
    also holds: the term [t] does not exhibit more behaviors than those
    of [let x = t in x]. *)

Lemma eval_like_eta_expansion : forall (t:trm) (x:var),
  eval_like (trm_let x t x) t.
Proof using.
  introv R. inverts R as. introv R1 R2.
  simpl in R2. rewrite var_eq_spec in R2. case_if.
  inverts R2. auto.
Qed.

(** We deduce that a term [t] denotes a program equivalent to
    the program [let x = t in x]. *)

Lemma trm_equiv_eta : forall (t:trm) (x:var),
  trm_equiv t (trm_let x t x).
Proof using.
  intros. intros s s' v. iff M.
  { applys eval_like_eta_reduction M. }
  { applys eval_like_eta_expansion M. }
Qed.

(** If [eval_like t1 t2], then any triple that holds for [t1]
    also holds for [t2]. *)

Lemma hoare_eval_like : forall t1 t2 H Q,
  eval_like t1 t2 ->
  hoare t1 H Q ->
  hoare t2 H Q.
Proof using.
  introv E M1 K0. forwards (s'&v&R1&K1): M1 K0.
  exists s' v. split. { applys E R1. } { applys K1. }
Qed.

Lemma triple_eval_like : forall t1 t2 H Q,
  eval_like t1 t2 ->
  triple t1 H Q ->
  triple t2 H Q.
Proof using.
  introv E M1. intros H'. applys hoare_eval_like E. applys M1.
Qed.

(** It follows that if two terms are equivalent, then they admit
    the same triples. *)

Lemma triple_trm_equiv : forall t1 t2 H Q,
  trm_equiv t1 t2 ->
  triple t1 H Q <-> triple t2 H Q.
Proof using.
  introv E. unfolds trm_equiv. iff M.
  { applys triple_eval_like M. introv R. applys* E. }
  { applys triple_eval_like M. introv R. applys* E. }
Qed.

(** The reasoning rule [triple_eval_like] has a number of practical
    applications. One, show below, is to revisit the proof of [triple_app_fun]
    in a much more succint way, by arguing that [trm_app (val_fun x t1) v2] and
    [subst x v2 t1] are equivalent terms, hence they admit the same behavior. *)

Lemma triple_app_fun : forall x v1 v2 t1 H Q,
  v1 = val_fun x t1 ->
  triple (subst x v2 t1) H Q ->
  triple (trm_app v1 v2) H Q.
Proof using.
  introv E M1. applys triple_eval_like M1.
  introv R. applys eval_app_fun E R.
Qed.

(** Another application is the following rule, which allows to modify the
    parenthesis structure of a sequence. *)

(** **** Exercise: 3 stars, standard, optional (triple_trm_seq_assoc)

    Prove that the term [t1; (t2; t3)] satisfies the same triples as the
    term [(t1;t2); t3]. *)

Lemma triple_trm_seq_assoc : forall t1 t2 t3 H Q,
  triple (trm_seq (trm_seq t1 t2) t3) H Q ->
  triple (trm_seq t1 (trm_seq t2 t3)) H Q.
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** Such a change in the parenthesis structure of a sequence can be helfpul
    to apply the frame rule around [t1;t2], for example. *)

(** Another useful application of the lemma [triple_eval_like] appears in
    chapter [Affine], for proving the equivalence of two versions of the
    garbage collection rule. *)

End ProofsSameSemantics.

(* ================================================================= *)
(** ** Alternative Specification Style for Result Values. *)

Module MatchStyle.

(** Recall the specification for the function [ref]. *)

Parameter triple_ref : forall v,
  triple (val_ref v)
    \[]
    (fun r => \exists p, \[r = val_loc p] \* p ~~> v).

(** Its postcondition could be equivalently stated by using, instead
    of an existential quantifier [\exists], a pattern matching. *)

Parameter triple_ref' : forall v,
  triple (val_ref v)
    \[]
    (fun r => match r with
              | val_loc p => (p ~~> v)
              | _ => \[False]
              end).

(** However, the pattern-matching presentation is less readable and
    would be fairly cumbersome to work with in practice. Thus, we
    systematically prefer using existentials. *)

End MatchStyle.

(* ================================================================= *)
(** ** Historical Notes *)

(** [Gordon 1989] (in Bib.v) presents the first mechanization of Hoare logic in a
    proof assistant, using the HOL tool. Gordon's pioneering work was followed
    by numerous formalizations of Hoare logic, targeting various programming
    languages.

    The original presentation of Separation Logic (1999-2001) consists of a set
    of rules written down on paper. These rules were not formally described in
    a proof assistant. Nevertheless, mechanized presentation of Separation Logic
    emerged a few years later.

    [Yu, Hamid, and Shao 2003] (in Bib.v) present the CAP framework for the
    verification in Coq of assembly-level code. This framework exploits
    separation logic style specifications, with predicate for lists and list
    segments involving the separating conjunction operator.

    In parallel, [Weber 2004] (in Bib.v), advised by Nipkow, developed the first
    mechanization of the rules of Separation Logic for a while language, using
    the Isabelle/HOL tool. His presentation is quite close from the original,
    paper presentation.

    Numerous mechanized presentations of Separation Logic, targeting various
    languages (assembly, C, core-Java, ML, etc.) and using various tools
    (Isabelle/HOL, Coq, PVS, HOL4, HOL). For a detailed list, as of 2020,
    we refer to Section 10.3 from the paper:
    http://www.chargueraud.org/research/2020/seq_seplogic/seq_seplogic.pdf . *)

(* 2021-08-30 20:15 *)
