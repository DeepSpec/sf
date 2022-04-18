(** * Nondet: Triples for Nondeterministic Languages *)

Set Implicit Arguments.
From SLF Require Export LibSepReference.
Close Scope val_scope.
Close Scope trm_scope. (* TODO: scope closed by default *)

Implicit Types f : var.
Implicit Types b : bool.
Implicit Types s : state.
Implicit Types t : trm.
Implicit Types v : val.
Implicit Types n : int.
Implicit Types p : loc.
Implicit Types h : heap.
Implicit Types P : Prop.
Implicit Types H : hprop.
Implicit Types Q : val->hprop.

(* ################################################################# *)
(** * First Pass *)

(** In previous chapters, we have considered a quasi-deterministic language;
    only the addresses of allocated data could vary between two executions
    of a same term starting in a same state.

    In this chapter, we discuss the interpretation of Separation Logic
    triples in the more general case of non-deterministic languages.
    To that end, we extend the language with a new primitive operator
    that produces a random number: the term [val_rand n] non-deterministically
    evaluates to an integer between [0] inclusive and [n] exclusive.

    This chapter is organized as follows:

    - Statement of a big-step semantics for non-deterministic languages
    - Proof of reasoning rules for triples
    - Proof of reasoning rules in weakest-precondition style
    - Bonus section: definition of triples for non-deterministic languages
      with respect to small-step semantics.

    For simplicity, we omit from the semantics the treatment of non-recursive
    functions, which can be encoded using recursive functions; and, likewise,
    omit the treatment of sequences, which can be encoded using let-bindings. *)

(* ================================================================= *)
(** ** Non-Deterministic Big-Step Semantics: the Predicate [evaln] *)

(** Previously, we worked with the big-step judgment [eval s t s' v], which
    relates one input state (and term) with one output state (and value).
    This judgment is well-suited for a deterministic semantics, because one
    input state leads to at most one result. For a non-deterministic semantics,
    however, we need to relate one input with a set of possible results.

    In Coq, a set of output states can be represented as a set of pairs
    made of a state and a value, that is, [(state*val)->Prop]. This type
    is isomorphic to the type [val->state->Prop], which corresponds exactly
    to the type of postconditions [val->hprop]. Thus, we are interested in
    setting up a judgment that relates an "input configuration", described
    by a state and a term, with a postcondition describing the set of possible
    "output configurations".

    The non-deterministic big-step judgment therefore takes the form
    [evaln s t Q], and relates an input state [s] and a term [t] with a
    postcondition [Q]. An output configuration consists of an output state
    [s'] and an output value [v] that, together, satisfy the postcondition [Q],
    in the sense that [Q v s'] holds.

    In the context of program verification, we are not so much interested in
    characterizing exactly the set of all output configurations reachable by
    the program, but mainly interested in showing that all output
    configurations satisfy a desired postcondition [Q]. For this reason, it is
    perfectly fine for the set of configurations described by [Q] to over-
    approximate the set of configurations actually reachable by the program.
    We'll explain later on how to characterize the set of output configurations
    in a precise manner.

    The judgment [evaln s t Q] is defined inductively. It asserts that every
    possible execution starting from configuration [(s,t)] satisfies the
    postcondition [Q]. The definition of [evaln] is adapted from that of [eval].
    Four cases are particularly interesting.

    - Consider the case of a value. The judgment [evaln s t Q] asserts that the
      value [v] in the state [s] satisfies the postcondition [Q]. The premise
      for deriving that judgment is thus that [Q v s] must hold.
    - Consider the case of a let-binding. [let x = t1 in t2]. The first premise
      of the evaluation rule describes the evaluation of the subterm [t1]. It
      takes the form [evaln s t1 Q]. The second premise describes the
      evaluation of the the continuation [subst x v1 t2] in a state [s2], where
      the value [v1] and the state [s2] correspond to a configuration that can
      be produced by [t1]. In other words, [v1] and [s2] are assumed to satisfy
      [Q1 v1 s2].
    - Consider the case of a non-deterministic term: [val_rand n], evaluated in
      a state [s]. The first premise of the rule requires [n > 0]. The second
      premise requires that, for any value [n1] that [val_rand n] may evaluate
      to (that is, such that [0 <= n1 < n]), the configuration made of [n1] and
      [s] satisfies the postcondition [Q], in the sense that [Q n1 s] holds.
    - Consider the case of an allocation: [val_ref v], evaluated in a state [s].
      The premise of the rule asserts that the postcondition [Q] should hold of
      any configuration made of a fresh location [p] and a state [s'] obtained
      as the update of [s] with a binding from [p] to [v]. *)

Inductive evaln : state -> trm -> (val->state->Prop) -> Prop :=
  | evaln_val : forall s v Q,
      Q v s ->
      evaln s (trm_val v) Q
  | evaln_fix : forall s f x t1 Q,
      Q (val_fix f x t1) s ->
      evaln s (trm_fix f x t1) Q
  | evaln_app_fix : forall s v1 v2 f x t1 Q,
      v1 = val_fix f x t1 ->
      evaln s (subst x v2 (subst f v1 t1)) Q ->
      evaln s (trm_app v1 v2) Q
  | evaln_let : forall Q1 s x t1 t2 Q,
      evaln s t1 Q1 ->
      (forall v1 s2, Q1 v1 s2 -> evaln s2 (subst x v1 t2) Q) ->
      evaln s (trm_let x t1 t2) Q
  | evaln_if : forall s b t1 t2 Q,
      evaln s (if b then t1 else t2) Q ->
      evaln s (trm_if (val_bool b) t1 t2) Q
  | evaln_add : forall s n1 n2 Q,
      Q (val_int (n1 + n2)) s ->
      evaln s (val_add (val_int n1) (val_int n2)) Q
  | evaln_rand : forall s n Q,
      n > 0 ->
      (forall n1, 0 <= n1 < n -> Q n1 s) ->
      evaln s (val_rand (val_int n)) Q
  | evaln_ref : forall s v Q,
      (forall p, ~ Fmap.indom s p ->
         Q (val_loc p) (Fmap.update s p v)) ->
      evaln s (val_ref v) Q
  | evaln_get : forall s p Q,
      Fmap.indom s p ->
      Q (Fmap.read s p) s ->
      evaln s (val_get (val_loc p)) Q
  | evaln_set : forall s p v Q,
      Fmap.indom s p ->
      Q val_unit (Fmap.update s p v) ->
      evaln s (val_set (val_loc p) v) Q
  | evaln_free : forall s p Q,
      Fmap.indom s p ->
      Q val_unit (Fmap.remove s p) ->
      evaln s (val_free (val_loc p)) Q.

(** Observe that [evaln s t Q] cannot hold if there exists one possible
    execution of [(s,t)] that runs into an error, i.e., that reaches a
    configuration that is stuck. This property reflects on the fact that
    the judgment [evaln] asserts that every possible execution terminates
    safely. *)

(** Observe also that [evaln] is covariant in the postcondition: if
    [evaln s t Q1] holds, and [Q2] is weaker than [Q1], then [evaln s t Q2]
    also holds. This property reflects on the fact that it is always
    possible to further over-approximate the set of possible results. *)

Lemma evaln_conseq : forall s t Q1 Q2,
  evaln s t Q1 ->
  Q1 ===> Q2 ->
  evaln s t Q2.
Proof using.
  introv M W.
  asserts W': (forall v h, Q1 v h -> Q2 v h). { auto. } clear W.
  induction M; try solve [ constructors* ].
Qed.

(** The judgment [evaln s t Q] can interpreted in at least five different ways:

    - The judgment [evaln] may be viewed as the natural generalization
      of [eval], generalizing from one output to a set of possible output.
    - The judgment [evaln] may be viewed as an inductive definition of a
      weakest-precondition judgment. Interestingly, if we swap the order of
      the arguments to [evaln t Q s], then the partial application [evaln t Q]
      has type [hprop], and its interpretation matches exactly that of a
      weakest precondition for a Hoare triple. We'll formalize this claim
      further on in this chapter, and we'll point out shortly afterwards the
      difference between the rules that define [evaln] and the traditional
      weakest-precondition reasoning rules.
    - The judgment [evaln] may be viewed as a CPS-version of the predicate
      [eval]. Indeed, The output of [eval], made of an output value and an
      output state, are "passed on" to the continuation [Q].
    - The judgment [evaln] may be viewed as a particular form of denotational
      semantics for the language. Each program is interpreted as (i.e., mapped
      to) a set of mathematical objects, which "simply" consists of pairs of
      states and "syntactic" values. In particular, functions are interpreted
      as plain pieces of syntax (not as functions over Scott domains, as
      usually done).
    - The judgment [evaln] may be viewed as a generalized form of a typing
      relation. To make the analogy clear, let us adapt the definition of
      [evaln] in two ways, and focus on the evaluation rule for let-bindings.
      First, let us get rid of the state, i.e., consider a language without
      side-effects, for simplicity.

     evaln t1 Q1 ->
     (forall v1, Q1 v1 -> evaln (subst x v1 t2) Q) ->
     evaln (trm_let x t1 t2) Q

      Second, let us switch from a substitution-based semantics to an
      environment-based semantics---nothing but change of presentation.

     evaln E t1 Q1 ->
     (forall v1, Q1 v1 -> evaln ((x,v1)::E) t2 Q) ->
     evaln E (trm_let x t1 t2) Q

      Now, let's consider a typing property. For example, expressing that a
      term has type [int] amounts to asserting that this term produces a
      value [v] of the form [val_int n] for some [n]. This property may be
      captured by the postcondition [fun v => exists n, v = val_int n].
      Let us compare the previous rule with the traditional typing rule
      shown below.

     typing E t1 Q1 ->
     typing ((x,Q1)::E) t2 Q ->
     typing E (trm_let x t1 t2) Q

      The only difference is that the evaluation rule maps [x] to any value
      [v1] such that [v1] has type [Q1], whereas the typing rule directly
      maps [x] to the type [Q1]. The two presentations are thus essentially
      equivalent. *)

(** In what follows, we discuss the difference between the presentation
    of the judgment [evaln], and the rules that define a weakest
    precondition. We focus on the particular case of a let-binding. *)

(** **** Exercise: 1 star, standard, optional (evaln_let')

    The rule [evaln_let] shares similarities with the statement of
    the weakest-precondition style reasoning rule for let-bindings.
    Prove the following alternative statement, with a wp-style flavor. *)

Lemma evaln_let' : forall s1 x t1 t2 Q,
  evaln s1 t1 (fun v1 s2 => evaln s2 (subst x v1 t2) Q) ->
  evaln s1 (trm_let x t1 t2) Q.
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 2 stars, standard, optional (evaln_let_of_evaln_let')

    Reciprocally, prove that the statement considered in the inductive
    definition of [evaln] is derivable from [evaln_let']. More precisely,
    prove the statement below by using [evaln_let'] and [evaln_conseq]. *)

Lemma evaln_let_of_evaln_let' : forall Q1 s1 x t1 t2 Q,
  evaln s1 t1 Q1 ->
  (forall v1 s2, Q1 v1 s2 -> evaln s2 (subst x v1 t2) Q) ->
  evaln s1 (trm_let x t1 t2) Q.
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** One way wonder whether we could have used the wp-style formulation
    of the semantics of let-bindings directly in the definition of [evaln].
    The answer is negative. Doing so would lead to an invalid inductive
    definition, involving a "non strictly positive occurrence". To check it
    out, uncomment the definition below to observe Coq's complaint.

  Inductive evaln' : state -> trm -> (val->state->Prop) -> Prop :=
    | evaln'_let : forall Q1 s1 x t1 t2 Q,
       evaln' s1 t1 (fun v1 s2 => evaln' s2 (subst x v1 t2) Q) ->
       evaln' s1 (trm_let x t1 t2) Q.
*)

(* ================================================================= *)
(** ** Interpretation of [evaln] w.r.t. [eval] *)

(** Given that [evaln] describes "all possible executions" and that
    [eval] describes "one possible execution", there must be formal
    relationships between the two predicates. These relationships are
    investigated next.

    Recall the big-step evaluation judgment [eval]. It is the same
    as before, only extended with evaluation rule for the random
    number generator, namely [eval_rand]. *)

Inductive eval : state -> trm -> state -> val -> Prop :=
  | eval_val : forall s v,
      eval s (trm_val v) s v
  | eval_fix : forall s f x t1,
      eval s (trm_fix f x t1) s (val_fix f x t1)
  | eval_app_fix : forall s1 s2 v1 v2 f x t1 v,
      v1 = val_fix f x t1 ->
      eval s1 (subst x v2 (subst f v1 t1)) s2 v ->
      eval s1 (trm_app v1 v2) s2 v
  | eval_let : forall s1 s2 s3 x t1 t2 v1 r,
      eval s1 t1 s2 v1 ->
      eval s2 (subst x v1 t2) s3 r ->
      eval s1 (trm_let x t1 t2) s3 r
  | eval_if : forall s1 s2 b v t1 t2,
      eval s1 (if b then t1 else t2) s2 v ->
      eval s1 (trm_if (val_bool b) t1 t2) s2 v
  | eval_add : forall s n1 n2,
      eval s (val_add (val_int n1) (val_int n2)) s (val_int (n1 + n2))
  | eval_rand : forall s n n1,
      0 <= n1 < n ->
      eval s (val_rand (val_int n)) s (val_int n1)
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

(** The judgment [evaln s t Q] asserts that any possible execution of the
    program [(t,s)] terminates on an output satisfying the postcondition [Q].
    Thus, if one particular execution terminates on the output [(s',v)],
    as described by the judgment [eval s t s' v], it must be the case
    that [Q v s'] holds. This result is formalized by the following lemma. *)

(** **** Exercise: 3 stars, standard, optional (evaln_inv_eval)

    Assume [evaln s t Q] to hold. Prove that the postcondition [Q] holds of
    any output that [(s,t)] may evaluate to according to the judgment [eval]. *)

Lemma evaln_inv_eval : forall s t v s' Q,
  evaln s t Q ->
  eval s t s' v ->
  Q v s'.
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** The judgment [evaln s t Q] asserts that any possible execution of the
    program [(t,s)] terminates on an output satisfying the postcondition [Q].
    This judgment implies, in particular, that there exists at least one
    such execution, described by a judgment of the form [eval s t s' v],
    where [v] and [s'] satisfy the postcondition [Q]. This second result is
    formalized by the following lemma. *)

(** **** Exercise: 4 stars, standard, especially useful (evaln_inv_exists_eval)

    Assume [evaln s t Q] to hold. Prove that there exists an output
    [(s',v)] that [(s,t)] may evaluate to according to the judgment
    [eval], and that this output satisfies [Q].

    Hint: the proof may be carried out either with or without leveraging
    the lemma [evaln_inv_eval], proved above.

    Hint: for the case [eval_ref], use the following line to assert the
    existence of a fresh location:
    [forwards* (p&D&N): (exists_fresh null s).]. *)

Lemma evaln_inv_exists_eval : forall s t Q,
  evaln s t Q ->
  exists s' v, eval s t s' v /\ Q v s'.
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** The judgment [evaln s t Q] associates with a program configuration
    [(s,t)] an over-approximation of its possible output configurations,
    described by [Q]. For the purpose of defining of Hoare triple, working
    with over-approximation is perfectly fine. In other contexts, however,
    it might be interesting to characterize exactly the set of output
    configurations.

    The set of results to which a program [(s,t)] may evaluate is
    precisely characterized by the predicate [fun v s' => eval s t s' v].
    Let [post s t] denote exactly that predicate. *)

Definition post (s:state) (t:trm) : val->hprop :=
  fun v s' => eval s t s' v.

(** The judgment [evaln s t (post s t)] essentially captures the safety
    of the program [(s,t)]: it asserts that all possible executions
    terminate without error.

    Let us prove that [post s t] corresponds to the smallest possible
    post-condition for [evaln]. In other words, assuming that [evaln s t Q]
    holds for some [Q], we can prove that [evaln s t (post s t)] holds,
    and that the entailment [post s t ===> Q] holds. This entailment
    captures the fact that [post s t] denotes a smaller set of results
    than [Q]. Note that [evaln s t (post s t)] does not hold for a program
    for which one particular execution may diverge or get stuck. *)

(** **** Exercise: 5 stars, standard, especially useful (evaln_post_of_evaln)

    Prove the fact that if [evaln s t Q] holds for some [Q], then it
    holds for the smallest postcondition, namely [post s t].
    Hint: in the let-binding case, you'll need to either exploit
    [evaln_inv_eval] or to provide an explicit intermediate postcondition
    for the subterm [t1] that revers to [Q1]. *)

Lemma evaln_post_of_evaln : forall s t Q,
  evaln s t Q ->
  evaln s t (post s t).
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 2 stars, standard, especially useful (evaln_inv_post_qimpl)

    Prove the fact that if [evaln s t Q] holds, then [post s t ===> Q],
    i.e. the smallest-possible postcondition entails the postcondition [Q].
    Hint: the proof is only one line long. *)

Lemma evaln_inv_post_qimpl : forall s t Q,
  evaln s t Q ->
  post s t ===> Q.
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(* ================================================================= *)
(** ** Triples for Non-Deterministic Big-Step Semantics *)

(** A Hoare triple, written [hoaren t H Q], asserts that, for any input state
    [s] satisfying the precondition [H], all executions of [t] in that state
    [s] terminate and produce an output satisfying the postcondition [Q]. *)

Definition hoaren (t:trm) (H:hprop) (Q:val->hprop) : Prop :=
  forall (s:state), H s -> evaln s t Q.

(** A Separation Logic triple, written [triplen t H Q], asserts that the term
    [t] satisfies a Hoare triple with precondition [H \* H'] and postcondition
    [Q \* H'], for any heap predicate [H'] describing the "rest of the word".
    Compared with the definition of [triple], we simply replaced [hoare] with
    [hoaren]. *)

Definition triplen (t:trm) (H:hprop) (Q:val->hprop) : Prop :=
  forall (H':hprop), hoaren t (H \* H') (Q \*+ H').

(* ================================================================= *)
(** ** Triple-Style Reasoning Rules for a Non-Deterministic Semantics. *)

(** To derive reasoning rules for triples, we proceed in two steps, just as in
    the previous chapters: first, we establish rules for [hoaren], then we
    derive rules for [triplen]. For the first part, the proofs are very similar
    to those form previous chapters. For the second part, the proofs are
    exactly the same as in the previous chapters. *)

(** Structural rules *)

Lemma hoaren_conseq : forall t H' Q' H Q,
  hoaren t H' Q' ->
  H ==> H' ->
  Q' ===> Q ->
  hoaren t H Q.
Proof using.
  unfolds hoaren. introv M MH MQ HF. applys* evaln_conseq.
Qed.

Lemma hoaren_hexists : forall t (A:Type) (J:A->hprop) Q,
  (forall x, hoaren t (J x) Q) ->
  hoaren t (hexists J) Q.
Proof using. introv M. intros h (x&Hh). applys M Hh. Qed.

Lemma hoaren_hpure : forall t (P:Prop) H Q,
  (P -> hoaren t H Q) ->
  hoaren t (\[P] \* H) Q.
Proof using.
  introv M. intros h (h1&h2&M1&M2&D&U). destruct M1 as (M1&HP).
  lets E: hempty_inv HP. subst. rewrite Fmap.union_empty_l. applys~ M.
Qed.

(** Rules for term constructs *)

Lemma hoaren_val : forall v H Q,
  H ==> Q v ->
  hoaren (trm_val v) H Q.
Proof using. introv M. intros h K. applys* evaln_val. Qed.

Lemma hoaren_fix : forall f x t1 H Q,
  H ==> Q (val_fix f x t1) ->
  hoaren (trm_fix f x t1) H Q.
Proof using. introv M. intros h K. applys* evaln_fix. Qed.

Lemma hoaren_app_fix : forall v1 v2 f x t1 H Q,
  v1 = val_fix f x t1 ->
  hoaren (subst x v2 (subst f v1 t1)) H Q ->
  hoaren (trm_app v1 v2) H Q.
Proof using. introv E M. intros h K. applys* evaln_app_fix. Qed.

Lemma hoaren_let : forall x t1 t2 H Q Q1,
  hoaren t1 H Q1 ->
  (forall v1, hoaren (subst x v1 t2) (Q1 v1) Q) ->
  hoaren (trm_let x t1 t2) H Q.
Proof using. introv M1 M2. intros h K. applys* evaln_let. Qed.

Lemma hoaren_if : forall (b:bool) t1 t2 H Q,
  hoaren (if b then t1 else t2) H Q ->
  hoaren (trm_if b t1 t2) H Q.
Proof using. introv M. intros h K. applys* evaln_if. Qed.

(** Rules for primitive operations *)

Lemma hoaren_add : forall H n1 n2,
  hoaren (val_add n1 n2)
    H
    (fun r => \[r = val_int (n1 + n2)] \* H).
Proof using.
  intros. intros h K. applys* evaln_add. rewrite* hstar_hpure_l.
Qed.

Lemma hoaren_rand : forall n,
  n > 0 ->
  hoaren (val_rand n)
    \[]
    (fun r => \exists n1, \[0 <= n1 < n] \* \[r = val_int n1]).
Proof using.
  introv N. intros h K. applys* evaln_rand.
  lets ->: hempty_inv K.
  intros n1 H1. applys* hexists_intro n1. rewrite* hstar_hpure_l.
  split*. applys* hpure_intro.
Qed.

Lemma hoaren_ref : forall H v,
  hoaren (val_ref v)
    H
    (fun r => (\exists p, \[r = val_loc p] \* p ~~> v) \* H).
Proof using.
  intros. intros s1 K. applys evaln_ref. intros p D.
  unfolds update. applys hstar_intro K.
  { applys hexists_intro p. rewrite hstar_hpure_l.
    split*. applys hsingle_intro. }
  { applys* disjoint_single_of_not_indom. }
Qed.

Lemma hoaren_get : forall H v p,
  hoaren (val_get p)
    ((p ~~> v) \* H)
    (fun r => \[r = v] \* (p ~~> v) \* H).
Proof using.
  intros. intros s K.
  lets (h1&h2&P1&P2&D&->): hstar_inv (rm K).
  lets E1: hsingle_inv P1. lets I1: indom_single p v.
  applys evaln_get.
  { applys* Fmap.indom_union_l. subst. applys indom_single. }
  { rewrite hstar_hpure_l. split.
    { subst h1. rewrite* Fmap.read_union_l. rewrite* Fmap.read_single. }
    { applys* hstar_intro. } }
Qed.

Lemma hoaren_set : forall H w p v,
  hoaren (val_set (val_loc p) v)
    ((p ~~> w) \* H)
    (fun r => \[r = val_unit] \* (p ~~> v) \* H).
Proof using.
  intros. intros s1 K.
  lets (h1&h2&P1&P2&D&->): hstar_inv (rm K).
  lets E1: hsingle_inv P1. lets I1: indom_single p v.
  applys evaln_set.
  { applys* Fmap.indom_union_l. subst. applys indom_single. }
  { rewrite hstar_hpure_l. split*.
    { subst h1. rewrite* Fmap.update_union_l. rewrite* update_single.
      applys hstar_intro.
      { applys* hsingle_intro. }
      { auto. }
      { applys Fmap.disjoint_single_set D. }
      { auto. applys indom_single. } } }
Qed.

Lemma hoaren_free : forall H p v,
  hoaren (val_free (val_loc p))
    ((p ~~> v) \* H)
    (fun r => \[r = val_unit] \* H).
Proof using.
  intros. intros s1 K.
  lets (h1&h2&P1&P2&D&->): hstar_inv (rm K).
  lets E1: hsingle_inv P1. lets I1: indom_single p v.
  applys evaln_free.
  { applys* Fmap.indom_union_l. subst. applys indom_single. }
  { rewrite hstar_hpure_l. split*.
    { subst h1. rewrite* Fmap.remove_union_single_l.
      { intros Dl. applys* Fmap.disjoint_inv_not_indom_both D Dl. } } }
Qed.

(** The proofs of reasoning rules for [triplens] are exactly the same as in
    the chapter [Rules]. For example, we show below the proof of the
    reasoning rule for let-bindings. *)

Lemma triplen_let : forall x t1 t2 H Q Q1,
  triplen t1 H Q1 ->
  (forall v1, triplen (subst x v1 t2) (Q1 v1) Q) ->
  triplen (trm_let x t1 t2) H Q.
Proof using.
  introv M1 M2. intros HF. applys hoaren_let.
  { applys M1. }
  { intros v. applys hoaren_conseq M2; xsimpl. }
Qed.

(** Statements and proofs of reasoning rules for other term constructs
    can be directly adapted from those in the file [LibSepReference]. *)

(* ################################################################# *)
(** * More Details *)

(* ================================================================= *)
(** ** Weakest-Precondition Style Presentation. *)

(** In chapter [WPsem], we discussed several possible definitions of the
    weakest-precondition operator, namely [wp], in Separation Logic. In this
    chapter, we present yet another possible definition, based on the judgment
    [evaln].

    Consider the judgment [evaln s t Q]. Assume the arguments were reordered,
    yielding the judgment [evaln t Q s]. Consider now the partial application
    [evaln t Q]. This partial application has type [state->Prop], that is,
    [hprop]. This predicate [evaln t Q] denotes a predicate that characterizes
    the set of input states [s] in which the evaluation (or, rather, any
    possible evaluation) of the term [t] produces an output satisfying [Q].
    It thus corresponds exactly to the notion of weakest precondition for Hoare
    Logic.

    The judgment [hoarewpn t Q], defined below, simply reorder the arguments
    of [evaln] so as to produce this weakest-precondition operator. Note that
    this is a Hoare Logic style predicate, which talks about the full state. *)

Definition hoarewpn (t:trm) (Q:val->hprop) : hprop :=
  fun s => evaln s t Q.

(** On top of [hoarewpn], we can define the Separation Logic version of weakest
    precondition, written [wpn t Q]. At a high level, [wpn] extends [hoarewpn]
    with a description of "the rest of the world". More precisely, [wpn t Q]
    describes a heap predicate, that, if extended with a heap predicate [H]
    describing the rest of the world, yields the weakest precondition with
    respect to the postcondition [Q \*+ H], that is, [Q] extended with [H]. *)

Definition wpn (t:trm) (Q:val->hprop) : hprop :=
  \forall H, H \-* (hoarewpn t (Q \*+ H)).

(** This definition is associated with the following introduction rule,
    which reads as follows: to prove [H ==> wpn t Q], which asserts that
    [t] admits [H] as precondition and [Q] as postcondition, it suffices
    to prove that, for any [H'] describing the rest of the world, the
    entailment [H \* H'==> hoarewpn t (Q \*+ H')] holds, asserting that
    the term [t] admits, in Hoare logic, the precondition [H \* H'] and
    the postcondition [Q \*+ H']. *)

Lemma wpn_of_hoarewpn : forall H t Q,
  (forall H', H \* H' ==> hoarewpn t (Q \*+ H')) ->
  H ==> wpn t Q.
Proof using.
  introv M. unfolds wpn. applys himpl_hforall_r. intros H'.
  applys himpl_hwand_r. rewrite hstar_comm. applys M.
Qed.

(** **** Exercise: 4 stars, standard, especially useful (wpn_equiv)

    Prove the standard equivalence [(H ==> wp t Q) <-> (triple t H Q)]
    to relate the predicates [wpn] and [triplen].
    Hint: using lemma [wpn_of_hoarewpn] can be helpful. *)

Lemma wpn_equiv : forall H t Q,
  (H ==> wpn t Q) <-> (triplen t H Q).
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** Remark: as mentioned in the chapter [WPsem], it is possible to define
    the predicate [triplen t H Q] as [H ==> wpn t Q], that is, to define
    [triplen] as a notion derived from [hoarewpn] and [wpn]. *)

(* ================================================================= *)
(** ** Hoare Logic WP-Style Rules for a Non-Deterministic Semantics. *)

(** Given that the semantics expressed by the predicate [evaln] has a weakest-
    precondition flavor, there are good chances that deriving weakest-
    precondition style reasoning rules from [evaln] could be even easier than
    deriving the rules for [triplen]. Thus, let us investigate whether this is
    indeed the case, by stating and proving reasoning rules for the judgments
    [hoarewpn] and [wpn]. We begin with rules for [hoarewpn]. *)

(** Structural rules *)

Lemma hoarewpn_conseq : forall t Q1 Q2,
  Q1 ===> Q2 ->
  (hoarewpn t Q1) ==> (hoarewpn t Q2).
Proof using.
  introv W. unfold hoarewpn. intros h K. applys evaln_conseq K W.
Qed.

(** Rules for term constructs *)

Lemma hoarewpn_val : forall v Q,
  Q v ==> hoarewpn (trm_val v) Q.
Proof using.
  unfold hoarewpn. intros. intros h K. applys* evaln_val.
Qed.

Lemma hoarewpn_fix : forall f x t Q,
  Q (val_fix f x t) ==> hoarewpn (trm_fix f x t) Q.
Proof using.
  unfold hoarewpn. intros. intros h K. applys* evaln_fix.
Qed.

Lemma hoarewpn_app_fix : forall f x v1 v2 t1 Q,
  v1 = val_fix f x t1 ->
  hoarewpn (subst x v2 (subst f v1 t1)) Q ==> hoarewpn (trm_app v1 v2) Q.
Proof using.
  unfold hoarewpn. intros. intros h K. applys* evaln_app_fix.
Qed.

Lemma hoarewpn_let : forall x t1 t2 Q,
      hoarewpn t1 (fun v => hoarewpn (subst x v t2) Q)
  ==> hoarewpn (trm_let x t1 t2) Q.
Proof using.
  unfold hoarewpn. intros. intros h K. applys* evaln_let.
Qed.

Lemma hoarewpn_if : forall b t1 t2 Q,
  hoarewpn (if b then t1 else t2) Q ==> hoarewpn (trm_if b t1 t2) Q.
Proof using.
  unfold hoarewpn. intros. intros h K. applys* evaln_if.
Qed.

(** Rules for primitives. We state their specifications following the
    presentation described near the end of chapter [Wand]. *)

Lemma hoarewpn_add : forall Q n1 n2,
  (Q (val_int (n1 + n2))) ==> hoarewpn (val_add (val_int n1) (val_int n2)) Q.
Proof using.
  unfolds hoarewpn. intros. intros h K. applys* evaln_add.
Qed.

Lemma hoarewpn_rand : forall Q n,
  n > 0 ->
      (\forall n1, \[0 <= n1 < n] \-* Q (val_int n1))
  ==> hoarewpn (val_rand (val_int n)) Q.
Proof using.
  unfolds hoarewpn. introv N. xsimpl. intros h K.
  applys* evaln_rand. intros n1 H1. lets K': hforall_inv K n1.
  rewrite* hwand_hpure_l in K'.
Qed.

Lemma hoarewpn_ref : forall Q v,
  (\forall p, (p ~~> v) \-* Q (val_loc p)) ==> hoarewpn (val_ref v) Q.
Proof using.
  unfolds hoarewpn. intros. intros h K. applys* evaln_ref. intros p D.
  lets K': hforall_inv (rm K) p.
  applys hwand_inv (single p v) K'.
  { applys hsingle_intro. }
  { applys* disjoint_single_of_not_indom. }
Qed.

Lemma hoarewpn_get : forall v p Q,
  (p ~~> v) \* (p ~~> v \-* Q v) ==> hoarewpn (val_get p) Q.
Proof using.
  unfolds hoarewpn. intros. intros h K.
  lets (h1&h2&P1&P2&D&->): hstar_inv (rm K).
  forwards*: hwand_inv h1 P2.
  lets E1: hsingle_inv P1. lets I1: indom_single p v.
  applys evaln_get.
  { applys* Fmap.indom_union_l. subst. applys indom_single. }
  { subst h1. rewrite* Fmap.read_union_l. rewrite* Fmap.read_single. }
Qed.

Lemma hoarewpn_set : forall v w p Q,
  (p ~~> v) \* (p ~~> w \-* Q val_unit) ==> hoarewpn (val_set p w) Q.
Proof using.
  unfolds hoarewpn. intros. intros h K.
  lets (h1&h2&P1&P2&D&->): hstar_inv (rm K).
  lets E1: hsingle_inv P1. lets I1: indom_single p v.
  forwards: hwand_inv (single p w) P2.
  { applys hsingle_intro. }
  { subst h1. applys Fmap.disjoint_single_set D. }
    { applys evaln_set.
    { applys* Fmap.indom_union_l. subst. applys indom_single. }
    { subst h1. rewrite* Fmap.update_union_l. rewrite* update_single. } }
Qed.

Lemma hoarewpn_free : forall v p Q,
  (p ~~> v) \* (Q val_unit) ==> hoarewpn (val_free p) Q.
Proof using.
  unfolds hoarewpn. intros. intros h K.
  lets (h1&h2&P1&P2&D&->): hstar_inv (rm K).
  lets E1: hsingle_inv P1. lets I1: indom_single p v.
  applys_eq evaln_free.
  { applys* Fmap.indom_union_l. subst. applys indom_single. }
  { subst h1. rewrite~ Fmap.remove_union_single_l.
    intros Dl. applys* Fmap.disjoint_inv_not_indom_both D Dl. }
Qed.

(* ================================================================= *)
(** ** Separation Logic WP-Style Rules for a Non-Deterministic Semantics. *)

(** In the previous section, we established reasoning rules for [hoarewpn].
    Based on these rules, we are ready to derive reasoning rules for [wpn]. *)

(** Structural rules *)

Lemma wpn_conseq_frame : forall t H Q1 Q2,
  Q1 \*+ H ===> Q2 ->
  (wpn t Q1) \* H ==> (wpn t Q2).
Proof using.
  introv M. unfold wpn. xsimpl.
  intros H'. xchange (hforall_specialize (H \* H')).
  applys hoarewpn_conseq. xchange M.
Qed.

Lemma wpn_ramified_trans : forall t H Q1 Q2,
  H ==> (wpn t Q1) \* (Q1 \--* Q2) ->
  H ==> (wpn t Q2).
Proof using.
  introv M. xchange M. applys wpn_conseq_frame. applys qwand_cancel.
Qed.

(** Rules for term constructs *)

Lemma wpn_val : forall v Q,
  Q v ==> wpn (trm_val v) Q.
Proof using.
  intros. unfold wpn. xsimpl. intros H'.
  xchange (>> hoarewpn_val (Q \*+ H')).
Qed.

Lemma wpn_fix : forall f x t Q,
  Q (val_fix f x t) ==> wpn (trm_fix f x t) Q.
Proof using.
  intros. unfold wpn. xsimpl. intros H'.
  xchange (>> hoarewpn_fix (Q \*+ H')).
Qed.

Lemma wpn_app_fix : forall f x v1 v2 t1 Q,
  v1 = val_fix f x t1 ->
  wpn (subst x v2 (subst f v1 t1)) Q ==> wpn (trm_app v1 v2) Q.
Proof using.
  intros. unfold wpn. xsimpl. intros H'.
  xchange (hforall_specialize H').
  applys* hoarewpn_app_fix.
Qed.

(** **** Exercise: 4 stars, standard, especially useful (wpn_let)

    Derive the reasoning rule [wpn_let] from [hoarewpn_let]. *)

Lemma wpn_let : forall x t1 t2 Q,
  wpn t1 (fun v => wpn (subst x v t2) Q) ==> wpn (trm_let x t1 t2) Q.
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

Lemma wpn_if : forall b t1 t2 Q,
  wpn (if b then t1 else t2) Q ==> wpn (trm_if b t1 t2) Q.
Proof using.
  intros. unfold wpn. xsimpl. intros H'.
  xchange (hforall_specialize H').
  applys hoarewpn_if.
Qed.

(** Rules for primitives. *)

Lemma wpn_add : forall Q n1 n2,
  (Q (val_int (n1 + n2))) ==> wpn (val_add (val_int n1) (val_int n2)) Q.
Proof using.
  intros. unfold wpn. xsimpl. intros H'.
  xchange (>> hoarewpn_add (Q \*+ H')).
Qed.

Lemma wpn_rand : forall Q n,
  n > 0 ->
      (\forall n1, \[0 <= n1 < n] \-* Q (val_int n1))
  ==> wpn (val_rand (val_int n)) Q.
Proof using.
  introv N. unfold wpn. xsimpl. intros H'.
  applys himpl_trans; [| applys* hoarewpn_rand ].
  xsimpl. intros n1. xchange (hforall_specialize n1).
  intros H1. rewrite* hwand_hpure_l.
Qed.

Lemma wpn_ref : forall Q v,
  (\forall p, (p ~~> v) \-* Q (val_loc p)) ==> wpn (val_ref v) Q.
Proof using.
  intros. unfold wpn. xsimpl. intros H'.
  applys himpl_trans; [| applys hoarewpn_ref ].
  xsimpl. intros p. xchange (hforall_specialize p).
Qed.

Lemma wpn_get : forall v p Q,
  (p ~~> v) \* (p ~~> v \-* Q v) ==> wpn (val_get p) Q.
Proof using.
  intros. unfold wpn.
  applys himpl_hforall_r. intros H'. applys himpl_hwand_r.
  rewrite hstar_comm.
  applys himpl_trans; [| applys hoarewpn_get v ]. simpl.
  rewrite hstar_assoc. applys himpl_frame_r.
  xsimpl.
Qed.

Lemma wpn_set : forall v w p Q,
  (p ~~> v) \* (p ~~> w \-* Q val_unit) ==> wpn (val_set p w) Q.
Proof using.
  intros. unfold wpn.
  applys himpl_hforall_r. intros H'. applys himpl_hwand_r.
  rewrite hstar_comm.
  applys himpl_trans; [| applys hoarewpn_set v ]. simpl.
  rewrite hstar_assoc. applys himpl_frame_r.
  xsimpl.
Qed.

Lemma wpn_free : forall v p Q,
  (p ~~> v) \* (Q val_unit) ==> wpn (val_free p) Q.
Proof using.
  intros. unfold wpn.
  applys himpl_hforall_r. intros H'. applys himpl_hwand_r.
  applys himpl_trans; [| applys hoarewpn_free v ]. xsimpl.
Qed.

(** Rules for primitives, alternative presentation using triples. *)

Lemma triplen_add : forall n1 n2,
  triplen (val_add n1 n2)
    \[]
    (fun r => \[r = val_int (n1 + n2)]).
Proof using.
  intros. rewrite <- wpn_equiv.
  applys himpl_trans; [| applys wpn_add ]. xsimpl*.
Qed.

Lemma triplen_rand : forall n,
  n > 0 ->
  triplen (val_rand n)
    \[]
    (fun r => \exists n1, \[0 <= n1 < n] \* \[r = val_int n1]).
Proof using.
  introv N. rewrite <- wpn_equiv.
  applys himpl_trans; [| applys* wpn_rand ]. xsimpl*.
Qed.

Lemma triplen_ref : forall v,
  triplen (val_ref v)
    \[]
    (fun r => \exists p, \[r = val_loc p] \* p ~~> v).
Proof using.
  intros. rewrite <- wpn_equiv.
  applys himpl_trans; [| applys wpn_ref ]. xsimpl*.
Qed.

Lemma triplen_get : forall v p,
  triplen (val_get p)
    (p ~~> v)
    (fun r => \[r = v] \* (p ~~> v)).
Proof using.
  intros. rewrite <- wpn_equiv.
  applys himpl_trans; [| applys wpn_get ]. xsimpl*.
Qed.

Lemma triplen_set : forall w p v,
  triplen (val_set (val_loc p) v)
    (p ~~> w)
    (fun _ => p ~~> v).
Proof using.
  intros. rewrite <- wpn_equiv.
  applys himpl_trans; [| applys wpn_set ]. xsimpl*.
Qed.

Lemma triplen_free : forall p v,
  triplen (val_free (val_loc p))
    (p ~~> v)
    (fun _ => \[]).
Proof using.
  intros. rewrite <- wpn_equiv.
  applys himpl_trans; [| applys wpn_free ]. xsimpl*.
Qed.

(** **** Exercise: 4 stars, standard, optional (wpn_rand_of_triplen_rand)

    The proof of lemma [triplen_rand] shows that a triple-based specification
    of [val_rand] is derivable from a wp-style specification. In this
    exercise, we aim to prove the reciprocal. Concretely, prove the following
    specification by exploiting [triplen_rand].
    Hint: make use of [wpn_equiv]. *)

Lemma wpn_rand_of_triplen_rand : forall n Q,
  n > 0 ->
      (\forall n1, \[0 <= n1 < n] \-* Q (val_int n1))
  ==> wpn (val_rand (val_int n)) Q.
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(* ################################################################# *)
(** * Optional Material *)

(** So far, this chapter has focused on handling non-determinism in the context
    of using a big-step semantics. In this bonus section, we investigate the
    treatment of non-determinism using a small-step semantics. Moreover, we
    establish equivalence proofs relating (non-deterministic) small-step and
    big-step semantics. *)


(* ================================================================= *)
(** ** Interpretation of [evaln] w.r.t. [eval] and [terminates] *)

(** The predicate [terminates s t] asserts that all executions of the
    configuration [t/s] terminate---none of them diverges or get
    stuck. Its definition is a simplified version of [evaln] where all
    occurences of [Q] are removed. In the rule for let-bindings,
    namely [terminates_let], the quantification over the configuration
    [v1/s2] is done by refering to the big-step judgment [eval]. *)

Inductive terminates : state -> trm -> Prop :=
  | terminates_val : forall s v,
      terminates s (trm_val v)
  | terminates_fix : forall s f x t1,
      terminates s (trm_fix f x t1)
  | terminates_app_fix : forall s v1 v2 f x t1,
      v1 = val_fix f x t1 ->
      terminates s (subst x v2 (subst f v1 t1)) ->
      terminates s (trm_app v1 v2)
  | terminates_let : forall s x t1 t2,
      terminates s t1 ->
      (forall v1 s2, eval s t1 s2 v1 -> terminates s2 (subst x v1 t2)) ->
      terminates s (trm_let x t1 t2)
  | terminates_if : forall s b t1 t2,
      terminates s (if b then t1 else t2) ->
      terminates s (trm_if (val_bool b) t1 t2)
  | terminates_add : forall s n1 n2,
      terminates s (val_add (val_int n1) (val_int n2))
  | terminates_rand : forall s n,
      n > 0 ->
      terminates s (val_rand (val_int n))
  | terminates_ref : forall s v,
      terminates s (val_ref v)
  | terminates_get : forall s p,
      Fmap.indom s p ->
      terminates s (val_get (val_loc p))
  | terminates_set : forall s p v,
      Fmap.indom s p ->
      terminates s (val_set (val_loc p) v)
  | terminates_free : forall s p,
      Fmap.indom s p ->
      terminates s (val_free (val_loc p)).

Section EvalnTerminates.
Hint Constructors eval evaln.

(** **** Exercise: 5 stars, standard, especially useful (evaln_iff_terminates_and_post)

    Prove that [evaln s t Q] is equivalent to the conjunction of
    [terminates s t] and to a partial correctness result asserting that
    if an evaluation of [t/s] terminates on some result then this result
    satisfies [Q]. *)

Lemma evaln_iff_terminates_and_post : forall s t Q,
  evaln s t Q <-> (terminates s t /\ (forall v s', eval s t s' v -> Q v s')).
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** Let [Any] denotes the postcondition that accepts any result. *)

Definition Any : val->state->Prop :=
  fun v s => True.

Hint Unfold Any.

(** **** Exercise: 2 stars, standard, especially useful (terminates_iff_evaln_any)

    Prove that [terminates s t] is equivalent to [evaln s t Any].
    Hint: exploit [evaln_iff_terminates_and_post]. *)

Lemma terminates_iff_evaln_any : forall s t,
  terminates s t <-> evaln s t Any.
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

End EvalnTerminates.

(* ================================================================= *)
(** ** Small-Step Evaluation Relation *)

(** The judgment [step s t s' t'] describes the small-step reduction relation:
    it asserts that the program configuration [(s,t)] can take one reduction
    step towards the program configuration [(s',t')]. Its definition, shown
    below, is standard. *)

Inductive step : state -> trm -> state -> trm -> Prop :=

  (* Unique context rule *)
  | step_let_ctx : forall s1 s2 x t1 t1' t2,
      step s1 t1 s2 t1' ->
      step s1 (trm_let x t1 t2) s2 (trm_let x t1' t2)

  (* Beta reductions *)
  | step_fix : forall s f x t1,
      step s (trm_fix f x t1) s (val_fix f x t1)
  | step_app_fix : forall s v1 v2 f x t1,
      v1 = val_fix f x t1 ->
      step s (trm_app v1 v2) s (subst x v2 (subst f v1 t1))
  | step_if : forall s b t1 t2,
      step s (trm_if (val_bool b) t1 t2) s (if b then t1 else t2)
  | step_let : forall s x t2 v1,
      step s (trm_let x v1 t2) s (subst x v1 t2)

  (* Primitive operations *)
  | step_add : forall s n1 n2,
      step s (val_add (val_int n1) (val_int n2)) s (val_int (n1 + n2))
  | step_rand : forall s n n1,
      0 <= n1 < n ->
      step s (val_rand (val_int n)) s (val_int n1)
  | step_ref : forall s v p,
      ~ Fmap.indom s p ->
      step s (val_ref v) (Fmap.update s p v) (val_loc p)
  | step_get : forall s p,
      Fmap.indom s p ->
      step s (val_get (val_loc p)) s (Fmap.read s p)
  | step_set : forall s p v,
      Fmap.indom s p ->
      step s (val_set (val_loc p) v) (Fmap.update s p v) val_unit
  | step_free : forall s p,
      Fmap.indom s p ->
      step s (val_free (val_loc p)) (Fmap.remove s p) val_unit.

(** Consider a configuration [(s,t)], where [t] is not a value. If this
    configuration cannot take any reduction step, it is said to be "stuck". *)

(** The judgment [evals s t s' t'] corresponds to the reflexive-transitive
    closure of [step]. Concretely, this judgment asserts that the configuration
    [(s,t)] can reduce in zero, one, or several evals to [(s',t')]. *)

Inductive evals : state -> trm -> state -> trm -> Prop :=
  | evals_refl : forall s t,
      evals s t s t
  | evals_step : forall s1 s2 s3 t1 t2 t3,
      step s1 t1 s2 t2 ->
      evals s2 t2 s3 t3 ->
      evals s1 t1 s3 t3.

(* ================================================================= *)
(** ** Small-Step Characterization of [evalns]: Attempts *)

(** For a non-determinstic language, [evals s t s' t'] asserts that there
    exists one possible evaluation from [(s,t)] to [(s',t')]. This judgment
    says nothing about all other possible evaluations.

    On the contrary, the predicate [evaln s t Q], introduced earlier in
    this chapter, says something about all possible evaluations. More precisely,
    [evaln s t Q] asserts that all possible evaluations of [(s,t)] reach a
    final configuration satisfying the postcondition [Q].

    We are thus interested in defining a judgment of the form [evalns s t Q],
    that is logically equivalent to [evaln s t Q], but whose definition is
    based on the small-step semantics. *)

(** In the particular case of a deterministic semantics, we could define
    [evalns s t Q] in terms of the transitive evaluation relation [evals]
    as follows. *)

Definition evalns_attempt_1 (s:state) (t:trm) (Q:val->hprop) : Prop :=
  exists v s', evals s t s' (trm_val v) /\ Q v s'.

(** Quiz: Before reading further, try to devise a definition of [evalns s t Q]
    expressed in terms for the judgment [evals] that applies to the general case
    of non-deterministic semantics. *)

(** Let's check out several candidate definitions for the judgment [evalns]. *)

(** The definition [evalns_attempt_2 s t Q] asserts that any execution starting
    from configuration [(s,t)] and ending on a final configuration [(s',v)] is
    such that the final configuration satisfies the postcondition [Q]. Yet,
    this definition fails to rule out the possibility of executions that get
    stuck. Thus, it is only applicable for semantics that include
    error-propagation rules, and for which there are no stuck terms. *)

Definition evalns_attempt_2 (s:state) (t:trm) (Q:val->hprop) : Prop :=
  forall v s', evals s t s' (trm_val v) -> Q v s'.

(** The definition [evalns_attempt_3 s t Q] asserts that any execution starting
    from configuration [(s,t)] and reaching a state [(s',t')] is such that
    either [t'] is a value [v] and [(s',v)] satisfies the postcondition [Q],
    or [(s',t')] can take a step. Yet, this definition fails to capture the
    fact that all execution of [t] should terminate. Thus, it is only useful
    for capturing partial correctness properties. *)

Definition evalns_attempt_3 (s:state) (t:trm) (Q:val->hprop) : Prop :=
  forall s2 t2, evals s t s2 t2 ->
       (exists v2, t2 = trm_val v2 /\ Q v2 s2)
    \/ (exists s3 t3, step s2 t2 s3 t3).

(** The definition [evalns_attempt_4 s t Q] asserts that every execution prefix
    starting from [(s,t)] may be completed into an execution that does terminate
    on a configuration that satisfies the postcondition [Q]. *)

Definition evalns_attempt_4 (s:state) (t:trm) (Q:val->hprop) : Prop :=
  forall s2 t2, evals s t s2 t2 ->
  exists v3 s3, evals s2 t2 s3 (trm_val v3) /\ Q v3 s3.

(** Quiz: Why is [evalns_attempt_4] not equivalent to [evaln]? Can you find a
    counter-example program for which the property "all possible evaluations
    reach a final configuration satisfying the postcondition" does not hold? *)

(** Solution follows.

    Consider the following program, which does satisfy [evalns_attempt_4]
    yet whose execution may diverge.

OCaml:

     let rec f () =
       if (val_rand 2) = 0 then () else f ()

   Consider an execution that has already performed a number of recursive
   calls. This execution may terminate in a finite number of evaluation
   evals. Indeed, the next call to [val_rand] may return zero. However, not
   all executions terminate. Indeed, the execution path where all calls to
   [val_rand] return [1], the program runs forever. *)

(** The key challenge is to capture the property that "every possible execution
    terminates". To that end, let's consider yet another approach, based on the
    idea of bounding the number of execution steps.

    The judgment [nbevals n s t s' t'], defined below, asserts that the
    configuration [(s,t)] may reduce in exactly [n] steps to [(s',t')].
    Its definition follows that of the judgment [evals], only with an
    extra argument for counting the number of steps. *)

Inductive nbevals : nat -> state -> trm -> state -> trm -> Prop :=
  | nbevals_refl : forall s t,
      nbevals 0 s t s t
  | nbevals_step : forall (n:nat) s1 s2 s3 t1 t2 t3,
      step s1 t1 s2 t2 ->
      nbevals n s2 t2 s3 t3 ->
      nbevals (S n) s1 t1 s3 t3.

(** Using the judgment [nbevals], we are able to bound the length of all
    executions. The judgment [steps_at_most nmax s t], defined below,
    asserts that there does not exist any execution starting from [(s,t)]
    that exceeds [nmax] reduction steps. *)

Definition steps_at_most (nmax:nat) (s:state) (t:trm) : Prop :=
  forall (n:nat) s2 t2, n > nmax -> ~ (nbevals n s t s2 t2).

(** The judgment [evalns_attempt_5 s t Q] corresponds to the conjunction
    of the judgment [evalns_attempt_3 s t Q], which asserts partial
    correctness, and of the judgment [exists nmax, steps_at_most nmax s t],
    which asserts that there exists an upper bound to the length of all
    possible executions. *)

Definition evalns_attempt_5 (s:state) (t:trm) (Q:val->hprop) : Prop :=
     (evalns_attempt_3 s t Q)
  /\ (exists nmax, steps_at_most nmax s t).

(** Is the definition of [evalns_attempt_5] satisfying? Not quite. First, this
    definition is fairly complex, and not so easy to work with. Second, and
    perhaps most importantly, this definition does not apply to all programming
    languages. It applies only to semantics for which each configuration admits
    at most a finite number of possible transitions.

    If we view the possible executions of a program as a tree, with each branch
    corresponding to a possible execution, then definition [evalns_attempt_5]
    only properly captures the notion of total correctness for "finitely
    branching trees", in which every node has a finite number of branches.

    Concretely, the definition [evalns_attempt_5] would rule out legitimate
    programs in a language that includes an "unbounded" sources of non-
    determinism. For example, consider a random number generator that applies
    to the unit argument and may return any integer value in [Z]. Such an
    operator could be formalized as follows. *)

Parameter val_unbounded_rand : val.

Parameter evaln_unbounded_rand : forall s Q,
  (forall n1, Q n1 s) ->
  evaln s (val_unbounded_rand val_unit) Q.

(** Quiz: devise a counter-example program such that (1) every possible
    execution of this program does terminate, and (2) this program does not
    satisfy [evalns_attempt_5] because there does not exist an upper bound on
    the length of all executions. *)

(** Solution: Consider the following program.

OCaml:

     let rec f n =
       if n > 0 then f (n-1) else () in
     f (unbounded_rand())

    The number of execution evals can be arbitrary. Yet, any given
    program execution terminates.

    Arguably, a stand-alone piece of hardware does not feature such "unbounded"
    source of non-determinism, because each transition at the hardware level
    involves the manipulation of at most a finite number of bits. However, as
    soon as I/O is involved, unbounded non-determinism may arise. For example,
    a language that features an [input_string] method allowing the user to
    input strings of arbitrary size is a language with a source of unbounded
    non-determinism. *)

(** Remark: the fact that [evalns_attempt_5] only properly captures total
    correctness for finitely branching trees is related to a result known
    as König's lemma. This result from graph theory, in the particular case
    of trees, asserts that "every infinite tree contains either a vertex of
    infinite degree or an infinite path", or equivalently, asserts that "a
    finitely branching tree is infinite iff it has an infinite path".

    The contraposed statement asserts that a finitely branching tree
    (corresponding to executions in a language with bounded determinism) is
    finite (i.e., admits a bound on the depth) iff it has no infinite path
    (i.e., if all executions terminate). *)

(** In summary:

    - [evalns_attempt_1] applies only to deterministic semantics.
    - [evalns_attempt_2] applies only to complete semantics, i.e.,
      semantics without stuck terms.
    - [evalns_attempt_3] captures partial correctness only, and says
      nothing about termination.
    - [evalns_attempt_4] also fails to properly capture termination.
    - [evalns_attempt_5] captures total correctness only for semantics
      that feature only bounded sources of non-determinism, i.e., with
      a finite number of possible transitions from each configuration.

    Our attempts to define a judgment [evalns s t Q] in terms of [evals] or in
    terms of its depth-indexed variant [nbevals] have failed. It thus appears
    necessary to search instead for a definition of [evalns] expressed directly
    in terms of the one-step reduction relation [step]. *)

(* ================================================================= *)
(** ** Small-Step Characterization of [evaln]: A Solution *)

(** In what follows, we present an inductive definition for [evalns s t Q].
    To begin with, let us consider the particular case of a deterministic
    language.

    The predicate [evalds s t Q] asserts that the (deterministic) evaluation
    starting from configuration [(s,t)] produces an output satisfying the
    predicate [Q]. It is defined inductively as follows.

    - Base case: [evalds s v Q] holds if the postcondition holds of this
      current state, that is, [Q v s] holds.
    - Step case: [evalds s t Q] holds if [(s,t)] one-step reduces to the
      configuration [(s',t')] and [evalds s' t' Q] holds. *)

Inductive evalds : state->trm->(val->hprop)->Prop :=
  | evalds_val : forall s v Q,
      Q v s ->
      evalds s v Q
  | evalds_step : forall s t s' t' Q,
      step s t s' t' ->
      evalds s' t' Q ->
      evalds s t Q.

(** Let us now generalize the inductive definition of [evalds] to the general
    case of non-deterministic semantics.

    - Base case: it does not change, that is, [evalns s v Q] requires [Q s v].

    - Step case: this case needs to be refined to account for all possible
      evaluations, and not just the unique possible evaluation. There are two
      requirements. First, [evalns s t Q] requires that the configuration
      [(s,t)] is not stuck, that is, it requires the existence of at least one
      possible reduction step. Second, [evalns s t Q] requires that, for any
      configuration [(s',t')] that [(s,t)] might reduce to, the property
      [evalns s' t' Q] holds.

    The definition of [evalns] may thus be formalized as shown below. *)

Inductive evalns : state->trm->(val->hprop)->Prop :=
  | evalns_val : forall s v Q,
      Q v s ->
      evalns s v Q
  | evalns_step : forall s t Q,
      (exists s' t', step s t s' t') ->
      (forall s' t', step s t s' t' -> evalns s' t' Q) ->
      evalns s t Q.

(** Observe how this definition allows for [evalns s t Q] to hold even
    for the program such as the counter-example considered for definition
    [evalns_attempt_5], i.e., the program that performs [unbounded_rand()]
    recursive calls. The judgment [evalns] holds for this program, although
    there exists no bound on the depth of the corresponding derivation. This
    possibility stems from the fact that the [forall s' t'] quantification in
    constructor [evalns_step] introduces an infinite branching factor in the
    derivation tree, for a language that includes the primitive operation
    [unbounded_rand]. *)

(** **** Exercise: 2 stars, standard, optional (evalns_val_inv)

    Prove the following inversion lemma, which asserts that
    [evalns s v Q] implies [Q s v]. *)

Lemma evalns_val_inv : forall s v Q,
  evalns s v Q ->
  Q v s.
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** In the remaining of this chapter, we present:
    - a definition of Separation Logic triples based on [evalns]; the
      corresponding judgment is named [triplens]
    - the proof of the reasoning rules associated with [triplens];
    - a formal proof of equivalence between [evalns] and [evaln], relating the
      small-step-based definition to the big-step-based definition introduced
      in the first part of this chapter. *)

(* ================================================================= *)
(** ** Triples for Small-Step Semantics *)

(** The judgment [hoaren t H Q] defines Hoare triples in terms of the small-
    step-based judgment [evalns]. It mimics the definition of [hoaren], which
    was used for defining triples with respect to the big-step judgment
    [evaln]. *)

Definition hoarens (t:trm) (H:hprop) (Q:val->hprop) : Prop :=
  forall (s:state), H s -> evalns s t Q.

(** The judgment [triplens] is the counterpart of [triplen], introducing
    Separation Logic triples defined w.r.t. [hoarens]. *)

Definition triplens (t:trm) (H:hprop) (Q:val->hprop) : Prop :=
  forall (H':hprop), hoarens t (H \* H') (Q \*+ H').

(** There is nothing new in deriving rules for [triplens] from rules for
    [hoarens]. Thus, in what follows, we'll focus on the novel aspects, which
    consists of deriving reasoning rules for [evalns] and for [hoarens], with
    respect to the small-step semantics captured by the relation [step]. *)

(* ================================================================= *)
(** ** Reasoning Rules for [seval] *)

(** First, we establish reasoning rules for [evalns]. *)

(** The structural rules for [evalns] asserts that [evalns s t Q] is
    covariant in the postcondition [Q]. *)

Lemma evalns_conseq : forall s t Q Q',
  evalns s t Q' ->
  Q' ===> Q ->
  evalns s t Q.
Proof using.
  introv M WQ. induction M.
  { applys evalns_val. applys* WQ. }
  { rename H1 into IH.
    applys evalns_step.
    { auto. }
    { introv HR. applys* IH. } }
Qed.

(** The rules for term constructs are established next. Note that there is
    no rule stated here for the case of values, because such a rule is
    already provided by the constructor [evalns_val]. *)

Lemma evalns_fix : forall s f x t1 Q,
  Q (val_fix f x t1) s ->
  evalns s (trm_fix f x t1) Q.
Proof using.
  introv M. applys evalns_step.
  { do 2 esplit. constructor. }
  { introv R. inverts R. { applys evalns_val. applys M. } }
Qed.

Lemma evalns_app_fix : forall s f x v1 v2 t1 Q,
  v1 = val_fix f x t1 ->
  evalns s (subst x v2 (subst f v1 t1)) Q ->
  evalns s (trm_app v1 v2) Q.
Proof using.
  introv E M. applys evalns_step.
  { do 2 esplit. constructors*. }
  { introv R. invert R; try solve [intros; false].
    introv -> -> -> -> -> R. inverts E. applys M. }
Qed.

(** **** Exercise: 5 stars, standard, especially useful (evalns_let)

    Prove the big-step reasoning rule for let-bindings for [evalns]. *)

Lemma evalns_let : forall s x t1 t2 Q1 Q,
  evalns s t1 Q1 ->
  (forall s1 v1, Q1 v1 s1 -> evalns s1 (subst x v1 t2) Q) ->
  evalns s (trm_let x t1 t2) Q.
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

Lemma evalns_if : forall s b t1 t2 Q,
  evalns s (if b then t1 else t2) Q ->
  evalns s (trm_if b t1 t2) Q.
Proof using.
  introv M. applys evalns_step.
  { do 2 esplit. constructors*. }
  { introv R. inverts R; tryfalse. { applys M. } }
Qed.

(* ================================================================= *)
(** ** Reasoning Rules for [hoarens] *)

(** Let's now prove reasoning rules for the Hoare triples judgment
    [hoarens]. *)

(** The consequence rule exploits the covariance result for [evalns]. *)

Lemma hoarens_conseq : forall t H' Q' H Q,
  hoarens t H' Q' ->
  H ==> H' ->
  Q' ===> Q ->
  hoarens t H Q.
Proof using.
  introv M MH MQ HF. applys evalns_conseq M MQ. applys* MH.
Qed.

(** The other two structural rules, which operate on the precondition, admit
    exactly the same proofs as in the previous chapters. *)

Lemma hoarens_hexists : forall t (A:Type) (J:A->hprop) Q,
  (forall x, hoarens t (J x) Q) ->
  hoarens t (hexists J) Q.
Proof using. introv M. intros h (x&Hh). applys M Hh. Qed.

Lemma hoarens_hpure : forall t (P:Prop) H Q,
  (P -> hoarens t H Q) ->
  hoarens t (\[P] \* H) Q.
Proof using.
  introv M. intros h (h1&h2&M1&M2&D&U). destruct M1 as (M1&HP).
  lets E: hempty_inv HP. subst. rewrite Fmap.union_empty_l. applys~ M.
Qed.

(** The reasoning rules for terms follow directly from the reasoning rules
    established for [evalns]. *)

Lemma hoarens_val : forall v H Q,
  H ==> Q v ->
  hoarens (trm_val v) H Q.
Proof using. introv M. intros h K. applys* evalns_val. Qed.

Lemma hoarens_fix : forall f x t1 H Q,
  H ==> Q (val_fix f x t1) ->
  hoarens (trm_fix f x t1) H Q.
Proof using. introv M. intros h K. applys* evalns_fix. Qed.

Lemma hoarens_app_fix : forall v1 v2 f x t1 H Q,
  v1 = val_fix f x t1 ->
  hoarens (subst x v2 (subst f v1 t1)) H Q ->
  hoarens (trm_app v1 v2) H Q.
Proof using. introv E M. intros h K. applys* evalns_app_fix. Qed.

Lemma hoarens_let : forall x t1 t2 H Q Q1,
  hoarens t1 H Q1 ->
  (forall v1, hoarens (subst x v1 t2) (Q1 v1) Q) ->
  hoarens (trm_let x t1 t2) H Q.
Proof using.
  introv M1 M2. intros h K. applys* evalns_let.
  { introv K'. applys* M2. }
Qed.

Lemma hoarens_if : forall (b:bool) t1 t2 H Q,
  hoarens (if b then t1 else t2) H Q ->
  hoarens (trm_if b t1 t2) H Q.
Proof using. introv M1. intros h K. applys* evalns_if. Qed.

(** The evaluation rules for primitive operations are proved in a way that is
    extremely similar to the proofs used for the big-step case, i.e., to the
    proofs establishing the reasoning rules for [hoaren]. *)

Lemma hoarens_add : forall H n1 n2,
  hoarens (val_add n1 n2)
    H
    (fun r => \[r = val_int (n1 + n2)] \* H).
Proof using.
  intros. intros s K. applys evalns_step.
  { do 2 esplit. constructors*. }
  { introv R. inverts R. applys evalns_val. rewrite~ hstar_hpure_l. }
Qed.

Lemma hoarens_rand : forall n,
  n > 0 ->
  hoarens (val_rand n)
    \[]
    (fun r => \exists n1, \[0 <= n1 < n] \* \[r = val_int n1]).
Proof using.
  introv N. intros s K. lets ->: hempty_inv K. applys evalns_step.
  { do 2 esplit. applys* step_rand 0. math. }
  { introv R. inverts R; tryfalse.
    applys evalns_val. applys hexists_intro n1. rewrite~ hstar_hpure_l.
    split~. applys* hpure_intro. }
Qed.

Lemma hoarens_ref : forall H v,
  hoarens (val_ref v)
    H
    (fun r => (\exists p, \[r = val_loc p] \* p ~~> v) \* H).
Proof using.
  intros. intros s K. applys evalns_step.
  { forwards~ (p&D&N): (exists_fresh null s).
    esplit. exists (val_loc p). applys* step_ref. }
  { introv R. inverts R; tryfalse. applys evalns_val.
    unfold update. applys~ hstar_intro.
    { exists p. rewrite~ hstar_hpure_l. split~. { applys~ hsingle_intro. } }
    { applys* disjoint_single_of_not_indom. } }
Qed.

Lemma hoarens_get : forall H v p,
  hoarens (val_get p)
    ((p ~~> v) \* H)
    (fun r => \[r = v] \* (p ~~> v) \* H).
Proof using.
  intros. intros s K. destruct K as (s1&s2&P1&P2&D&U).
  lets E1: hsingle_inv P1. subst s s1. applys evalns_step.
  { do 2 esplit. applys* step_get. applys indom_union_l. applys indom_single. }
  { introv R. inverts R; tryfalse. applys evalns_val.
    rewrite~ hstar_hpure_l. split~.
    { rewrite read_union_l. { rewrite* read_single. } { applys indom_single. } }
    { applys* hstar_intro. } }
Qed.

Lemma hoarens_set : forall H w p v,
  hoarens (val_set (val_loc p) v)
    ((p ~~> w) \* H)
    (fun r => \[r = val_unit] \* (p ~~> v) \* H).
Proof using.
  intros. intros s K. destruct K as (s1&s2&P1&P2&D&U).
  lets E1: hsingle_inv P1. subst s s1. applys evalns_step.
  { do 2 esplit. applys* step_set. applys indom_union_l. applys indom_single. }
  { introv R. inverts R; tryfalse. applys evalns_val.
    rewrite hstar_hpure_l. split~.
    { rewrite update_union_l; [| applys indom_single ].
      rewrite update_single. applys~ hstar_intro.
      { applys~ hsingle_intro. }
      { applys* disjoint_single_set. } } }
Qed.

Lemma hoarens_free : forall H p v,
  hoarens (val_free (val_loc p))
    ((p ~~> v) \* H)
    (fun r => \[r = val_unit] \* H).
Proof using.
  intros. intros s K. destruct K as (s1&s2&P1&P2&D&U).
  lets E1: hsingle_inv P1. subst s s1. applys evalns_step.
  { do 2 esplit. applys* step_free. applys indom_union_l. applys indom_single. }
  { introv R. inverts R; tryfalse. applys evalns_val.
    rewrite hstar_hpure_l. split~.
    { rewrite remove_union_single_l. { auto. }
      intros N'. applys disjoint_inv_not_indom_both D N'.
      applys indom_single. } }
Qed.

(** From there, reasoning rules for [triplens] can be derived from the rules
    for [hoarens] exactly like in previous chapters, i.e., using exactly the
    same proofs as for deriving rules for [triple] from rules for [hoare]. *)

(* ================================================================= *)
(** ** Equivalence Between Non-Deterministic Small-Step and Big-Step Sem. *)

(** We end this chapter with the proof of equivalence between [hoarens] and
    [hoaren], establishing a formal relationship between triples defined with
    respect to a small-step semantics and those defined with respect to a
    big-step semantics. *)

(** We start by establishing the equivalence between [evalns] and [evaln].
    We focus first on the direction from [evalns] to [evaln]. *)

(** We begin with a key lemma: if a configuration [(s1,t1)] takes a step to
    [(s2,t2)], then this first configuration admits the same postconditions
    as the second configuration. *)

Lemma evaln_of_step_and_evaln : forall s1 t1 Q,
  (exists s2 t2, step s1 t1 s2 t2) ->
  (forall s2 t2, step s1 t1 s2 t2 -> evaln s2 t2 Q) ->
  evaln s1 t1 Q.
Proof using.
  introv (s2&t2&R1) RS. gen Q. induction R1; intros.
  { applys evaln_let (fun v1 s2 => evaln s2 (subst x v1 t2) Q).
    { applys IHR1. intros s1b t1b Kb.
      forwards M: RS. { applys step_let_ctx Kb. }
      { inverts M as M1 M2. applys evaln_conseq M1. applys M2. } }
    { intros v1 s' K. applys K. } }
  { applys evaln_fix. forwards M: RS. { applys step_fix. }
    { inverts* M. } }
  { applys* evaln_app_fix. forwards M: RS. { applys* step_app_fix. }
    { applys M. } }
  { applys* evaln_if. forwards M: RS. { applys* step_if. } { applys M. } }
  { applys evaln_let (fun v' s' => v' = v1 /\ s' = s).
    { applys* evaln_val. }
    { intros ? ? (->&->). forwards M: RS. { applys* step_let. }
      { applys M. } } }
  { applys* evaln_add. forwards M: RS. { applys* step_add. }
    { inverts* M. } }
  { applys* evaln_rand.
    { math. }
    { intros n2 N2. forwards M: RS. { applys* step_rand n2. }
      { inverts* M. } } }
  { applys evaln_ref. intros p' D.
    forwards M: RS p'. { applys* step_ref. } { inverts* M. } }
  { applys* evaln_get. forwards M: RS. { applys* step_get. }
    { inverts* M. } }
  { applys* evaln_set. forwards M: RS. { applys* step_set. }
    { inverts* M. } }
  { applys* evaln_free. forwards M: RS. { applys* step_free. }
    { inverts* M. } }
Qed.

(** By exploiting the above lemma over all the evals of an execution, we obtain
    the fact that [evalns] implies [evaln]. *)

Lemma evaln_of_evalns : forall s t Q,
  evalns s t Q ->
  evaln s t Q.
Proof using.
  introv M. induction M.
  { applys* evaln_val. }
  { applys* evaln_of_step_and_evaln. }
Qed.

(** Let's now turn to the second direction, from [evaln] to [evalns].
    The proof is carried out by induction on the big-step relation. *)

Lemma evalns_of_evaln : forall s t Q,
  evaln s t Q ->
  evalns s t Q.
Proof using.
  introv M. induction M.
  { applys* evalns_val. }
  { applys evalns_step.
    { do 2 esplit. applys step_fix. }
    { introv K. inverts K. applys* evalns_val. } }
  { rename H into E. applys evalns_step.
    { do 2 esplit. applys* step_app_fix. }
    { introv K. invert K; try solve [ intros; false ].
      introv -> -> -> -> -> R. inverts E. applys IHM. } }
  { rename M into M1, H into M2, IHM into IHM1, H0 into IHM2.
    tests C: (exists v1, t1 = trm_val v1).
    { destruct C as (v1&->). applys evalns_step.
      { do 2 esplit. applys* step_let. }
      { introv K. inverts K as K1 K2.
        { inverts K1. }
        { inverts IHM1 as K3 K4.
          { applys* IHM2. }
          { destruct K3 as (?&?&K5). inverts K5. } } } }
    { applys evalns_step.
      { inverts IHM1 as K3 K4.
        { false* C. }
        { destruct K3 as (?&?&K5). do 2 esplit. applys* step_let_ctx. } }
      { introv K. inverts K as K'; [|false* C].
        inverts IHM1 as K5 K6; [false* C|].
        specializes K6 K'. applys* evalns_let. } } }
  { applys evalns_step.
    { do 2 esplit. applys* step_if. }
    { introv K. inverts K. applys IHM. } }
  { applys evalns_step.
    { do 2 esplit. applys* step_add. }
    { introv K. inverts K. applys* evalns_val. } }
  { applys evalns_step.
    { do 2 esplit. applys* step_rand 0. math. }
    { introv K. inverts K; tryfalse. applys* evalns_val. } }
  { applys evalns_step.
    { forwards~ (p&D&N): (exists_fresh null s).
      do 2 esplit. applys* step_ref. }
    { introv K. inverts K; tryfalse. applys* evalns_val. } }
  { applys evalns_step.
    { do 2 esplit. applys* step_get. }
    { introv K. inverts K; tryfalse. applys* evalns_val. } }
  { applys evalns_step.
    { do 2 esplit. applys* step_set. }
    { introv K. inverts K; tryfalse. applys* evalns_val. } }
  { applys evalns_step.
    { do 2 esplit. applys* step_free. }
    { introv K. inverts K; tryfalse. applys* evalns_val. } }
Qed.

(** Combining the two directions, we obtain the desired equivalence between
    the big-step and the small-step characterization of total correctness. *)

Lemma evalns_eq_evalns :
  evalns = evaln.
Proof using.
  extens. intros s t Q. iff M.
  { applys* evaln_of_evalns. }
  { applys* evalns_of_evaln. }
Qed.

(** As immediate corollary, we obtain the equivalence between the big-step and
    the small-step characterization of Hoare triples, for the general case of
    a non-deterministic language. *)

Lemma phoare_eq_hoarens :
  hoarens = hoaren.
Proof using. unfold hoarens, hoaren. rewrite* evalns_eq_evalns. Qed.

(* ================================================================= *)
(** ** Historical Notes *)

(** At a very low-level, one may view a piece of hardware as being totally
    deterministic: at each tick of the processor's clock, every hardware
    component makes a transition according to non-ambiguous rules. Yet,
    complex hardware architectures are not so deterministic. For example,
    on a multicore hardware, which of two concurrent writes reaches the
    memory first is, from the perspective of a program, essentially random.
    At a higher-level, interactions with the outside world, such as user
    input, can be seen as sources of non-determinism in a program semantics.

    Non-deterministic semantics may be harder to reason about than
    deterministic semantics. To tame that complexity, a semantics may be
    "determinized" by parameterizing it with a trace of events, each event
    reflecting one "choice" that was made during the execution. Reasoning
    about a determinized semantics equipped with traces may, depending on
    the context, be easier or carry more information than reasoning about
    a non-deterministic semantics. Reasoning about traces is, however,
    beyond the scope of this course.

    Non-determinism is most often described using a small-step semantics.
    Capturing the semantics of triples for a non-deterministic languages
    using a big-step judgment, as done in this chapter with the predicate
    [evaln], appears to be a novel approach, as of Jan. 2021. *)

(* 2022-04-18 20:12 *)
