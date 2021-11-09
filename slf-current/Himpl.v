(** * Himpl: Heap Entailment *)

(**

Foundations of Separation Logic

Chapter: "Himpl".

Author: Arthur Charguéraud.
License: CC-by 4.0.

*)

Set Implicit Arguments.
From SLF Require LibSepReference.
From SLF Require Export Hprop.

(** Implicit Types *)

Implicit Types P : Prop.
Implicit Types H : hprop.
Implicit Types Q : val->hprop.

(* ################################################################# *)
(** * First Pass *)

(** In the previous chapter, we have introduced the key heap predicate
    operators, and we have defined the notion of Separation Logic triple.

    Before we can state and prove reasoning rules for establishing triples,
    we need to introduce the "entailment relation". This relation,
    written [H1 ==> H2], asserts that any heap that satisfies [H1] also
    satisfies [H2].

    We also need to extend the entailment relation to postconditions.
    We write [Q1 ===> Q2] to asserts that, for any result value [v],
    the entailment [Q1 v ==> Q2 v] holds.

    The two entailment relations appear in the statement of the rule of
    consequence, which admits the same statement in Separation Logic
    as in Hoare logic. It asserts that precondition can be strengthened
    and postcondition can be weakened in a specification triple.

    Lemma triple_conseq : forall t H Q H' Q',
      triple t H' Q' ->
      H ==> H' ->
      Q' ===> Q ->
      triple t H Q.

   This chapter presents:
   - the formal definition of the entailment relations,
   - the fundamental properties of the Separation Logic operators:
     these properties are expressed either as entailments, or as
     equalities, which denote symmetric entailments,
   - the 4 structural rules of Separation Logic: the rule of consequence,
     the frame rule (which can be combined with the rule of consequence),
     and the extractions rules for pure facts and for quantifiers,
   - the tactics [xsimpl] and [xchange] that are critically useful
     for manipulating entailments in practice,
   - (optional) details on how to prove the fundamental properties
     and the structural rules.

*)

(* ================================================================= *)
(** ** Definition of Entailment *)

(** The "entailment relationship" [H1 ==> H2] asserts that any
    heap [h] that satisfies the heap predicate [H1] also satisfies
    the heap predicate [H2]. *)

Definition himpl (H1 H2:hprop) : Prop :=
  forall (h:heap), H1 h -> H2 h.

Notation "H1 ==> H2" := (himpl H1 H2) (at level 55).

(** [H1 ==> H2] captures the fact that [H1] is a stronger precondition
    than [H2], in the sense that it is more restrictive. *)

(** As we show next, the entailment relation is reflexive, transitive,
    and antisymmetric. It thus forms an order relation on heap predicates. *)

Lemma himpl_refl : forall H,
  H ==> H.
Proof using. intros h. hnf. auto. Qed.

Lemma himpl_trans : forall H2 H1 H3,
  (H1 ==> H2) ->
  (H2 ==> H3) ->
  (H1 ==> H3).
Proof using. introv M1 M2. intros h H1h. eauto. Qed.

(** **** Exercise: 1 star, standard, especially useful (himpl_antisym)

    Prove the antisymmetry of entailment result shown below
    using extensionality for heap predicates, as captured by
    lemma [predicate_extensionality] (or lemma [hprop_eq])
    introduced in the previous chapter ([Hprop]). *)

Lemma himpl_antisym : forall H1 H2,
  (H1 ==> H2) ->
  (H2 ==> H1) ->
  H1 = H2.
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** Remark: as the proof scripts show, the fact that entailment on [hprop]
    constitutes an order relation is a direct consequence of the fact that
    implication on [Prop], that is, [->], is an order relation on [Prop]
    (when assuming the propositional extensionality axiom). *)

(** The lemma [himpl_antisym] may, for example, be used to establish
    commutativity of separating conjunction: [(H1 \* H2) = (H2 \* H1)]
    by proving that each side entails the other side, that is, by proving
    [(H1 \* H2) ==> (H2 \* H1)] and [(H2 \* H1) ==> (H1 \* H2)]. *)

(* ================================================================= *)
(** ** Entailment for Postconditions *)

(** The entailment [==>] relates heap predicates. It is used to capture
    that a precondition "entails" another one. We need a similar
    judgment to assert that a postcondition "entails" another one.

    For that purpose, we introduce [Q1 ===> Q2], which asserts that
    for any value [v], the heap predicate [Q1 v] entails [Q2 v]. *)

Definition qimpl (Q1 Q2:val->hprop) : Prop :=
  forall (v:val), Q1 v ==> Q2 v.

Notation "Q1 ===> Q2" := (qimpl Q1 Q2) (at level 55).

(** Remark: equivalently, [Q1 ===> Q2] holds if for any value [v] and
    any heap [h], the proposition [Q1 v h] implies [Q2 v h]. *)

(** Entailment on postconditions also forms an order relation:
    it is reflexive, transitive, and antisymmetric. *)

Lemma qimpl_refl : forall Q,
  Q ===> Q.
Proof using. intros Q v. applys himpl_refl. Qed.

Lemma qimpl_trans : forall Q2 Q1 Q3,
  (Q1 ===> Q2) ->
  (Q2 ===> Q3) ->
  (Q1 ===> Q3).
Proof using. introv M1 M2. intros v. applys himpl_trans; eauto. Qed.

Lemma qimpl_antisym : forall Q1 Q2,
  (Q1 ===> Q2) ->
  (Q2 ===> Q1) ->
  (Q1 = Q2).
Proof using.
  introv M1 M2. apply functional_extensionality.
  intros v. applys himpl_antisym; eauto.
Qed.

(* ================================================================= *)
(** ** Fundamental Properties of Separation Logic Operators *)

(** The 5 fundamental properties of Separation Logic operators are
    described next. Many other properties are derivable from those. *)

(** (1) The star operator is associative. *)

Parameter hstar_assoc : forall H1 H2 H3,
  (H1 \* H2) \* H3 = H1 \* (H2 \* H3).

(** (2) The star operator is commutative. *)

Parameter hstar_comm : forall H1 H2,
   H1 \* H2 = H2 \* H1.

(** (3) The empty heap predicate is a neutral for the star.
    Because star is commutative, it is equivalent to state that
    [hempty] is a left or a right neutral for [hstar].
    We chose, arbitrarily, to state the left-neutral property. *)

Parameter hstar_hempty_l : forall H,
  \[] \* H = H.

(** (4) Existentials can be "extruded" out of stars, that is:
     [(\exists x, J x) \* H] is equivalent to [\exists x, (J x \* H)]. *)

Parameter hstar_hexists : forall A (J:A->hprop) H,
  (\exists x, J x) \* H = \exists x, (J x \* H).

(** (5) The star operator is "monotone" with respect to entailment, meaning
    that if [H1 ==> H1'] then [(H1 \* H2) ==> (H1' \* H2)].

    Viewed the other way around, if we have to prove the entailment relation
    [(H1 \* H2) ==> (H1' \* H2)], we can "cancel out" [H2] on both sides.
    In this view, the monotonicity property is a sort of "frame rule for
    the entailment relation".

    Here again, due to commutativity of star, it only suffices to state
    the left version of the monotonicity property. *)

Parameter himpl_frame_l : forall H2 H1 H1',
  H1 ==> H1' ->
  (H1 \* H2) ==> (H1' \* H2).

(** **** Exercise: 1 star, standard, especially useful (hstar_comm_assoc)

    The commutativity and associativity results combine into one result
    that is sometimes convenient to exploit in proofs. *)

Lemma hstar_comm_assoc : forall H1 H2 H3,
  H1 \* H2 \* H3 = H2 \* H1 \* H3.
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 1 star, standard, especially useful (himpl_frame_r)

    The monotonicity property of the star operator w.r.t. entailment can
    also be stated in a symmetric fashion, as shown next. Prove this result.
    Hint: exploit the transitivity of entailment ([himpl_trans]) and the
    asymmetric monotonicity result ([himpl_frame_l]). *)

Lemma himpl_frame_r : forall H1 H2 H2',
  H2 ==> H2' ->
  (H1 \* H2) ==> (H1 \* H2').
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 1 star, standard, especially useful (himpl_frame_lr)

    The monotonicity property of the star operator w.r.t. entailment can
    also be stated in a symmetric fashion, as shown next. Prove this result.
    Hint: exploit the transitivity of entailment ([himpl_trans]) and the
    asymmetric monotonicity result ([himpl_frame_l]). *)

Lemma himpl_frame_lr : forall H1 H1' H2 H2',
  H1 ==> H1' ->
  H2 ==> H2' ->
  (H1 \* H2) ==> (H1' \* H2').
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(* ================================================================= *)
(** ** Introduction and Elimination Rules w.r.t. Entailments *)

(** The rules for introducing and eliminating pure facts and existential
    quantifiers in entailments are essential. They are presented next. *)

(** Consider an entailment of the form [H ==> (\[P] \* H')]. To establish
    this entailment, one must prove that [P] is true, and that [H] entails
    [H']. *)

(** **** Exercise: 2 stars, standard, especially useful (himpl_hstar_hpure_r).

    Prove the rule [himpl_hstar_hpure_r].
    Hint: recall from [Hprop] the lemma [hstar_hpure_l], which asserts
    the equality [(\[P] \* H) h = (P /\ H h)]. *)

Lemma himpl_hstar_hpure_r : forall P H H',
  P ->
  (H ==> H') ->
  H ==> (\[P] \* H').
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** Reciprocally, consider an entailment of the form [(\[P] \* H) ==> H'].
    To establish this entailment, one must prove that [H] entails [H'] under
    the assumption that [P] is true.

    Indeed, the former proposition asserts that if a heap [h] satisfies [H]
    and that [P] is true, then [h] satisfies [H'], while the latter asserts
    that if [P] is true, then if a heap [h] satisfies [H] it also
    satisfies [H'].

    The "extraction rule for pure facts in the left of an entailment"
    captures the property that the pure fact [\[P]] can be extracted into
    the Coq context. It is stated as follows. *)

(** **** Exercise: 2 stars, standard, especially useful (himpl_hstar_hpure_l).

    Prove the rule [himpl_hstar_hpure_l]. *)

Lemma himpl_hstar_hpure_l : forall (P:Prop) (H H':hprop),
  (P -> H ==> H') ->
  (\[P] \* H) ==> H'.
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** Consider an entailment of the form [H ==> (\exists x, J x)], where [x]
    has some type [A] and [J] has type [A->hprop]. To establish this
    entailment, one must exhibit a value for [x] for which [H] entails [J x]. *)

(** **** Exercise: 2 stars, standard, especially useful (himpl_hexists_r).

    Prove the rule [himpl_hexists_r]. *)

Lemma himpl_hexists_r : forall A (x:A) H J,
  (H ==> J x) ->
  H ==> (\exists x, J x).
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** Reciprocally, consider an entailment [(\exists x, (J x)) ==> H].
    To establish this entailment, one has to prove that, whatever the
    value of [x], the predicate [J x] entails [H].

    Indeed the former proposition asserts that if a heap [h]
    satisfies [J x] for some [x], then [h] satisfies [H'], while
    the latter asserts that if, for some [x], the predicate [h]
    satisfies [J x], then [h] satisfies [H'].

    Observe how the existential quantifier on the left of the
    entailment becomes an universal quantifier outside of the arrow.

    The "extraction rule for existentials in the left of an entailment"
    captures the property that existentials can be extracted into
    the Coq context. It is stated as follows. *)

(** **** Exercise: 2 stars, standard, especially useful (himpl_hexists_l).

    Prove the rule [himpl_hexists_l]. *)

Lemma himpl_hexists_l : forall (A:Type) (H:hprop) (J:A->hprop),
  (forall x, J x ==> H) ->
  (\exists x, J x) ==> H.
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(* ================================================================= *)
(** ** Extracting Information from Heap Predicates *)

(** We next present an example showing how entailments can be used to
    state lemmas allowing to extract information from particular heap
    predicates. We show that from a heap predicate of the form
    [(p ~~> v1) \* (p ~~> v2)] describes two "disjoint" cells that
    are both "at location [p]", one can extract a contradiction.

    Indeed, such a state cannot exist. The underlying contraction is
    formally captured by the following entailment relation, which
    concludes [False]. *)

Lemma hstar_hsingle_same_loc : forall (p:loc) (v1 v2:val),
  (p ~~> v1) \* (p ~~> v2) ==> \[False].

(** The proof of this result exploits a result on finite maps.
    Essentially, the domain of a single singleton map that binds
    a location [p] to some value is the singleton set [\{p}], thus
    such a singleton map cannot be disjoint from another singleton
    map that binds the same location [p].

    Check disjoint_single_single_same_inv : forall (p:loc) (v1 v2:val),
      Fmap.disjoint (Fmap.single p v1) (Fmap.single p v2) ->
      False.
*)

(** Using this lemma, we can prove [hstar_hsingle_same_loc]
    by unfolding the definition of [hstar] to reveal the
    contradiction on the disjointness assumption. *)

Proof using.
  intros. unfold hsingle. intros h (h1&h2&E1&E2&D&E). false.
  subst. applys Fmap.disjoint_single_single_same_inv D.
Qed.

(** More generally, a heap predicate of the form [H \* H] is generally
    suspicious in Separation Logic. In (the simplest variant of) Separation
    Logic, such a predicate can only be satisfied if [H] covers no memory
    cell at all, that is, if [H] is a pure predicate of the form [\[P]]
    for some proposition [P]. *)

(* ================================================================= *)
(** ** Consequence, Frame, and their Combination *)

(** The rule of consequence in Separation Logic is similar to that
    in Hoare logic. *)

Parameter triple_conseq : forall t H Q H' Q',
  triple t H' Q' ->
  H ==> H' ->
  Q' ===> Q ->
  triple t H Q.

(** Recall the frame rule introduced in the previous chapter. *)

Parameter triple_frame : forall t H Q H',
  triple t H Q ->
  triple t (H \* H') (Q \*+ H').

(** Observe that, stated as such, it is very unlikely for the frame rule
    to be applicable in practice, because the precondition must be exactly
    of the form [H \* H'] and the postcondition exactly of the form
    [Q \*+ H'], for some [H']. For example, the frame rule would not apply
    to a proof obligation of the form [triple t (H' \* H) (Q \*+ H')],
    simply because [H' \* H] does not match [H \* H'].

    This limitation of the frame rule can be addressed by combining the frame
    rule with the rule of consequence into a single rule, called the
    "consequence-frame rule". This rule, shown below, enables deriving
    a triple from another triple, without any restriction on the exact
    shape of the precondition and postcondition of the two triples involved. *)

Lemma triple_conseq_frame : forall H2 H1 Q1 t H Q,
  triple t H1 Q1 ->
  H ==> H1 \* H2 ->
  Q1 \*+ H2 ===> Q ->
  triple t H Q.

(** **** Exercise: 1 star, standard, especially useful (triple_conseq_frame)

    Prove the combined consequence-frame rule. *)

Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(* ================================================================= *)
(** ** The Extraction Rules for Triples *)

(** A judgment of the form [triple t (\[P] \* H) Q] is equivalent
    to [P -> triple t H Q]. This structural rule is called [triple_hpure]
    and formalized as shown below. It captures the extraction of the
    pure facts out of the precondition of a triple, in a similar way
    as [himpl_hstar_hpure_l] for entailments. *)

Parameter triple_hpure : forall t (P:Prop) H Q,
  (P -> triple t H Q) ->
  triple t (\[P] \* H) Q.

(** A judgment of the form [triple t (\exists x, J x) Q] is equivalent
    to [forall x, triple t (J x) Q]. This structural rule is called
    [triple_hexists] and formalized as shown below. It captures the
    extraction of an existential quantifier out of the precondition
    of a triple, in a similar way as [himpl_hexists_l] for entailments. *)

Parameter triple_hexists : forall t (A:Type) (J:A->hprop) Q,
  (forall x, triple t (J x) Q) ->
  triple t (\exists x, J x) Q.

(* ################################################################# *)
(** * More Details *)

Module XsimplTactic.
Import LibSepReference.
Notation "'hprop''" := (Hprop.hprop).

(* ================================================================= *)
(** ** Identifying True and False Entailments *)

Module CaseStudy.

Implicit Types p q : loc.
Implicit Types n m : int.

End CaseStudy.

(* ================================================================= *)
(** ** Proving Entailments by Hand *)

Module EntailmentProofs.
Implicit Types p : loc.
Implicit Types n : int.

(** Proving an entailment by hand is generally a tedious task. This is why
    most Separation Logic based framework include an automated tactic for
    simplifying entailments. In this course, the relevant tactic is named
    [xsimpl]. Further in this chapter, we describe by means of examples the
    behavior of this tactic. But in order to best appreciate what the tactic
    provides and best understand how it works, it is very useful to complete
    a few proofs by hand. *)

(** **** Exercise: 3 stars, standard, optional (himpl_example_1)

    Prove the example entailment below.
    Hint: exploit [hstar_comm], [hstar_assoc], or [hstar_comm_assoc]
    which combines the two, and exploit [himpl_frame_l] or [himpl_frame_r]
    to cancel out matching pieces. *)

Lemma himpl_example_1 : forall p1 p2 p3 p4,
      p1 ~~> 6 \* p2 ~~> 7 \* p3 ~~> 8 \* p4 ~~> 9
  ==> p4 ~~> 9 \* p3 ~~> 8 \* p2 ~~> 7 \* p1 ~~> 6.
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 3 stars, standard, optional (himpl_example_2)

    Prove the example entailment below.
    Hint: use [himpl_hstar_hpure_r] to extract pure facts, once they
    appear at the head of the left-hand side of the entailment. *)

Lemma himpl_example_2 : forall p1 p2 p3 n,
      p1 ~~> 6 \* \[n > 0] \* p2 ~~> 7 \* \[n < 0]
  ==> p3 ~~> 8.
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 3 stars, standard, optional (himpl_example_3)

    Prove the example entailment below.
    Hint: use lemmas among [himpl_hexists_r], [himpl_hexists_l],
    [himpl_hstar_hpure_r] and [himpl_hstar_hpure_r] to deal with
    pure facts and quantifiers. *)

Lemma himpl_example_3 : forall p,
      \exists n, p ~~> n \* \[n > 0]
  ==> \exists n, \[n > 1] \* p ~~> (n-1).
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

End EntailmentProofs.

(* ================================================================= *)
(** ** The [xsimpl] Tactic *)

(** Performing manual simplifications of entailments by hand is
    an extremely tedious task. Fortunately, it can be automated
    using specialized Coq tactic. This tactic, called [xsimpl],
    applies to an entailment and implements a 3-step process:

    1. extract pure facts and existential quantifiers from the LHS,
    2. cancel out equal predicates occurring both in the LHS and RHS,
    3. generate subgoals for the pure facts occurring in the RHS, and
       instantiate the existential quantifiers from the RHS
       (using either unification variables or user-provided hints).

    These steps are detailed and illustrated next.

    The tactic [xpull] is a degraded version of [xsimpl] that only
    performs the first step. We will also illustrate its usage. *)

(* ----------------------------------------------------------------- *)
(** *** [xsimpl] to Extract Pure Facts and Quantifiers in LHS *)

(** The first feature of [xsimpl] is its ability to extract the
    pure facts and the existential quantifiers from the left-hand
    side out into the Coq context.

    In the example below, the pure fact [n > 0] appears in the LHS.
    After calling [xsimpl], this pure fact is turned into an hypothesis,
    which may be introduced with a name into the Coq context. *)

Lemma xsimpl_demo_lhs_hpure : forall H1 H2 H3 H4 (n:int),
  H1 \* H2 \* \[n > 0] \* H3 ==> H4.
Proof using.
  intros. xsimpl. intros Hn.
Abort.

(** In case the LHS includes a contradiction, such as the pure fact
    [False], the goal gets solved immediately by [xsimpl]. *)

Lemma xsimpl_demo_lhs_hpure : forall H1 H2 H3 H4,
  H1 \* H2 \* \[False] \* H3 ==> H4.
Proof using.
  intros. xsimpl.
Qed.

(** The [xsimpl] tactic also extracts existential quantifier from the LHS.
    It turns them into universally quantified variables outside of the
    entailment relation, as illustrated through the following example. *)

Lemma xsimpl_demo_lhs_hexists : forall H1 H2 H3 H4 (p:loc),
  H1 \* \exists (n:int), (p ~~> n \* H2) \* H3 ==> H4.
Proof using.
  intros. xsimpl. intros n.
Abort.

(** A call to [xsimpl], or to its degraded version [xpull], extract at once
    all the pure facts and quantifiers from the LHS, as illustrated next. *)

Lemma xsimpl_demo_lhs_several : forall H1 H2 H3 H4 (p q:loc),
  H1 \* \exists (n:int), (p ~~> n \* \[n > 0] \* H2) \* \[p <> q] \* H3 ==> H4.
Proof using.
  intros.
  xsimpl. (* or [xpull] *)
  intros n Hn Hp.
Abort.

(* ----------------------------------------------------------------- *)
(** *** [xsimpl] to Cancel Out Heap Predicates from LHS and RHS *)

(** The second feature of [xsimpl] is its ability to cancel out similar
    heap predicates that occur on both sides of an entailment.

    In the example below, [H2] occurs on both sides, so it is canceled
    out by [xsimpl]. *)

Lemma xsimpl_demo_cancel_one : forall H1 H2 H3 H4 H5 H6 H7,
  H1 \* H2 \* H3 \* H4 ==> H5 \* H6 \* H2 \* H7.
Proof using.
  intros. xsimpl.
Abort.

(** [xsimpl] actually cancels out at once all the heap predicates that it
    can spot appearing on both sides. In the example below, [H2], [H3],
    and [H4] are canceled out. *)

Lemma xsimpl_demo_cancel_many : forall H1 H2 H3 H4 H5,
  H1 \* H2 \* H3 \* H4 ==> H4 \* H3 \* H5 \* H2.
Proof using.
  intros. xsimpl.
Abort.

(** If all the pieces of heap predicate get canceled out, the remaining
    proof obligation is [\[] ==> \[]]. In this case, [xsimpl] automatically
    solves the goal by invoking the reflexivity property of entailment. *)

Lemma xsimpl_demo_cancel_all : forall H1 H2 H3 H4,
  H1 \* H2 \* H3 \* H4 ==> H4 \* H3 \* H1 \* H2.
Proof using.
  intros. xsimpl.
Qed.

(* ----------------------------------------------------------------- *)
(** *** [xsimpl] to Instantiate Pure Facts and Quantifiers in RHS *)

(** The third feature of [xsimpl] is its ability to extract pure facts
    from the RHS as separate subgoals, and to instantiate existential
    quantifiers from the RHS.

    Let us first illustrate how it deals with pure facts. In the example
    below, the fact [n > 0] gets spawned in a separated subgoal. *)

Lemma xsimpl_demo_rhs_hpure : forall H1 H2 H3 (n:int),
  H1 ==> H2 \* \[n > 0] \* H3.
Proof using.
  intros. xsimpl.
Abort.

(** When it encounters an existential quantifier in the RHS, the [xsimpl]
    tactic introduces a unification variable denoted by a question mark,
    that is, an "evar", in Coq terminology. In the example below, the [xsimpl]
    tactic turns [\exists n, .. p ~~> n ..] into [.. p ~~> ?x ..]. *)

Lemma xsimpl_demo_rhs_hexists : forall H1 H2 H3 H4 (p:loc),
  H1 ==> H2 \* \exists (n:int), (p ~~> n \* H3) \* H4.
Proof using.
  intros. xsimpl.
Abort.

(** The "evar" often gets subsequently instantiated as a result of
    a cancellation step. For example, in the example below, [xsimpl]
    instantiates the existentially quantified variable [n] as [?x],
    then cancels out [p ~~> ?x] from the LHS against [p ~~> 3] on
    the right-hand-side, thereby unifying [?x] with [3]. *)

Lemma xsimpl_demo_rhs_hexists_unify : forall H1 H2 H3 H4 (p:loc),
  H1 \* (p ~~> 3) ==> H2 \* \exists (n:int), (p ~~> n \* H3) \* H4.
Proof using.
  intros. xsimpl.
Abort.

(** The instantiation of the evar [?x] can be observed if there is
    another occurrence of the same variable in the entailment.
    In the next example, which refines the previous one, observe how
    [n > 0] becomes [3 > 0]. *)

Lemma xsimpl_demo_rhs_hexists_unify_view : forall H1 H2 H4 (p:loc),
  H1 \* (p ~~> 3) ==> H2 \* \exists (n:int), (p ~~> n \* \[n > 0]) \* H4.
Proof using.
  intros. xsimpl.
Abort.

(** (Advanced.) In some cases, it is desirable to provide an explicit value
    for instantiating an existential quantifier that occurs in the RHS.
    The [xsimpl] tactic accepts arguments, which will be used to instantiate
    the existentials (on a first-match basis). The syntax is [xsimpl v1 .. vn],
    or [xsimpl (>> v1 .. vn)] in the case [n > 3]. *)

Lemma xsimpl_demo_rhs_hints : forall H1 (p q:loc),
  H1 ==> \exists (n m:int), (p ~~> n \* q ~~> m).
Proof using.
  intros. xsimpl 3 4.
Abort.

(** (Advanced.) If two existential quantifiers quantify variables of the same
    type, it is possible to provide a value for only the second quantifier
    by passing as first argument to [xsimpl] the special value [__].
    The following example shows how, on LHS of the form [\exists n m, ...],
    the tactic [xsimpl __ 4] instantiates [m] with [4] while leaving [n]
    as an unresolved evar. *)

Lemma xsimpl_demo_rhs_hints_evar : forall H1 (p q:loc),
  H1 ==> \exists (n m:int), (p ~~> n \* q ~~> m).
Proof using.
  intros. xsimpl __ 4.
Abort.

(* ----------------------------------------------------------------- *)
(** *** [xsimpl] on Entailments Between Postconditions *)

(** The tactic [xsimpl] also applies on goals of the form [Q1 ===> Q2].

    For such goals, it unfolds the definition of [===>] to reveal an
    entailment of the form [==>], then invokes the [xsimpl] tactic. *)

Lemma qimpl_example_1 : forall (Q1 Q2:val->hprop) (H2 H3:hprop),
  Q1 \*+ H2 ===> Q2 \*+ H2 \*+ H3.
Proof using. intros. xsimpl. intros r. Abort.

(* ----------------------------------------------------------------- *)
(** *** Example of Entailment Proofs using [xsimpl] *)

Lemma himpl_example_1 : forall (p:loc),
  p ~~> 3 ==>
  \exists (n:int), p ~~> n.
Proof using. xsimpl. Qed.

Lemma himpl_example_2 : forall (p q:loc),
  p ~~> 3 \* q ~~> 3 ==>
  \exists (n:int), p ~~> n \* q ~~> n.
Proof using. xsimpl. Qed.

Lemma himpl_example_4 : forall (p:loc),
  \exists (n:int), p ~~> n ==>
  \exists (m:int), p ~~> (m + 1).
Proof using.
  intros. (* observe that [xsimpl] here does not work well. *)
  xpull. intros n. xsimpl (n-1).
  replace (n-1+1) with n. { auto. } { math. }
  (* variant for the last line:
  applys_eq himpl_refl. fequal. math. *)
Qed.

Lemma himpl_example_5 : forall (H:hprop),
  \[False] ==> H.
Proof using. xsimpl. Qed.

(* ================================================================= *)
(** ** The [xchange] Tactic *)

(** The tactic [xchange] is to entailment what [rewrite] is to equality.

    Assume an entailment goal of the form [H1 \* H2 \* H3 ==> H4].
    Assume an entailment assumption [M], say [H2 ==> H2'].
    Then [xchange M] turns the goal into [H1 \* H2' \* H3 ==> H4],
    effectively replacing [H2] with [H2']. *)

Lemma xchange_demo_base : forall H1 H2 H2' H3 H4,
  H2 ==> H2' ->
  H1 \* H2 \* H3 ==> H4.
Proof using.
  introv M. xchange M.
  (* Note that freshly produced items appear to the front *)
Abort.

(** The tactic [xchange] can also take as argument equalities.
    The tactic [xchange M] exploits the left-to-right direction of an
    equality [M], whereas [xchange <- M] exploits the right-to-left
    direction . *)

Lemma xchange_demo_eq : forall H1 H2 H3 H4 H5,
  H1 \* H3 = H5 ->
  H1 \* H2 \* H3 ==> H4.
Proof using.
  introv M. xchange M.
  xchange <- M.
Abort.

(** The tactic [xchange M] does accept a lemma or hypothesis [M]
    featuring universal quantifiers, as long as its conclusion
    is an equality or an entailment. In such case, [xchange M]
    instantiates [M] before attemting to perform a replacement. *)

Lemma xchange_demo_inst : forall H1 (J J':int->hprop) H3 H4,
  (forall n, J n = J' (n+1)) ->
  H1 \* J 3 \* H3 ==> H4.
Proof using.
  introv M. xchange M.
  (* Note that freshly produced items appear to the front *)
Abort.

(** How does the [xchange] tactic work? Consider a goal of the form [H ==> H']
    and assume [xchange] is invoked with an hypothesis of type [H1 ==> H1']
    as argument. The tactic [xchange] should attempt to decompose [H] as the
    star of [H1] and the rest of [H], call it [H2]. If it succeeds, then the
    goal [H ==> H'] can be rewritten as [H1 \* H2 ==> H']. To exploit the
    hypothesis [H1 ==> H1'], the tactic should replace the goal with the
    entailment [H1' \* H2 ==> H']. The lemma shown below captures this piece
    of reasoning implemented by the tactic [xchange]. *)

(** **** Exercise: 2 stars, standard, especially useful (xchange_lemma)

    Prove, without using the tactic [xchange], the following lemma which
    captures the internal working of [xchange]. *)

Lemma xchange_lemma : forall H1 H1' H H' H2,
  H1 ==> H1' ->
  H ==> H1 \* H2 ->
  H1' \* H2 ==> H' ->
  H ==> H'.
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

End XsimplTactic.

(* ################################################################# *)
(** * Optional Material *)

(* ================================================================= *)
(** ** Proofs for the Separation Algebra *)

Module FundamentalProofs.

(** We next show the details of the proofs establishing the fundamental
    properties of the Separation Logic operators.

    Note that all these results must be proved without help of the tactic
    [xsimpl], because the implementation of the tactic [xsimpl] itself
    depends on these fundamental properties.

    We begin with the frame property, which is the simplest to prove. *)

(** **** Exercise: 1 star, standard, especially useful (himpl_frame_l)

    Prove the frame property for entailment.
    Hint: unfold the definition of [hstar]. *)

Lemma himpl_frame_l : forall H2 H1 H1',
  H1 ==> H1' ->
  (H1 \* H2) ==> (H1' \* H2).
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 1 star, standard, especially useful (himpl_frame_r)

    Prove the lemma [himpl_frame_r], symmetric to [himpl_frame_l]. *)

Lemma himpl_frame_r : forall H1 H2 H2',
  H2 ==> H2' ->
  (H1 \* H2) ==> (H1 \* H2').
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** The second simplest result is the extrusion property for existentials.
    To begin with, we exploit the antisymmetry of entailment to turn
    the equality into a conjunction of two entailments. Then, it is simply
    a matter of unfolding the definitions of [hexists], [hstar] and [==>].

    By default, Coq does not display any of the parentheses written in
    the statement below, making the proof obligation somewhat confusing.
    ---This is a small price to pay in exchange for maximal flexibility
    in allowing the parsing of unparenthesized expressions such as
    [H1 \* \exists x, H2] and [\exists x, H1 \* H2].

    As a result, for this proof and the subsequent ones form this section,
    you should consider activating the display of parentheses. In CoqIDE,
    use the "View" menu, check "Display Parentheses". Alternatively, use
    the command "Set Printing Parentheses", or even "Set Printing All". *)

Lemma hstar_hexists : forall A (J:A->hprop) H,
  (\exists x, J x) \* H = \exists x, (J x \* H).
Proof using.
  intros. applys himpl_antisym.
  { intros h (h1&h2&M1&M2&D&U). destruct M1 as (x&M1). exists* x h1 h2. }
  { intros h (x&M). destruct M as (h1&h2&M1&M2&D&U). exists h1 h2.
    splits~. exists* x. }
Qed.

(** There remains to establish the commutativity and associativity of the star
    operator, and the fact that the empty heap predicate is its neutral element.
    To establish these properties, we need to exploit a few basic facts about
    finite maps. We introduce them as we go along. *)

(** To prove the commutativity of the star operator, i.e. [H1 \* H2 = H2 \* H1],
    it is sufficient to prove the entailement in one direction, e.g.,
    [H1 \* H2 ==> H2 \* H1]. Indeed, the other other direction is symmetrical.
    The symmetry argument is captured by the following lemma, which we will
    exploit in the proof of [hstar_comm]. *)

Lemma hprop_op_comm : forall (op:hprop->hprop->hprop),
  (forall H1 H2, op H1 H2 ==> op H2 H1) ->
  (forall H1 H2, op H1 H2 = op H2 H1).
Proof using. introv M. intros. applys himpl_antisym; applys M. Qed.

(** To prove commutativity of star, we need to exploit the fact that the union
    of two finite maps with disjoint domains commutes. This fact is captured
    by the following lemma.

    Check Fmap.union_comm_of_disjoint : forall h1 h2,
      Fmap.disjoint h1 h2 ->
      h1 \u h2 = h2 \u h1.

    The commutativity result is then proved as follows. Observe the use of
    the lemma [hprop_op_comm], which allows establishing the entailment in
    only one of the two directions.
*)

Lemma hstar_comm : forall H1 H2,
   H1 \* H2 = H2 \* H1.
Proof using.
  applys hprop_op_comm. intros. intros h (h1&h2&M1&M2&D&U). exists h2 h1.
  subst. splits~. { rewrite Fmap.union_comm_of_disjoint; auto. }
Qed.

(** **** Exercise: 3 stars, standard, especially useful (hstar_hempty_l)

    Prove that the empty heap predicate is a neutral element for the star.
    You will need to exploit the fact that the union with an empty map is
    the identity, as captured by lemma [Fmap.union_empty_l].

  Check Fmap.union_empty_l : forall h,
    Fmap.empty \u h = h.
*)

Lemma hstar_hempty_l : forall H,
  \[] \* H = H.
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** The lemma showing that [hempty] is a right neutral can be derived
    from the previous result ([hempty] is a left neutral) and commutativity. *)

Lemma hstar_hempty_r : forall H,
  H \* \[] = H.
Proof using.
  intros. rewrite hstar_comm. rewrite hstar_hempty_l. auto.
Qed.

(** Associativity of star is the most tedious result to derive.
    We need to exploit the associativity of union on finite maps,
    as well as lemmas about the disjointness of a map with the
    result of the union of two maps.

  Check Fmap.union_assoc : forall h1 h2 h3,
    (h1 \u h2) \u h3 = h1 \u (h2 \u h3).

  Check Fmap.disjoint_union_eq_l : forall h1 h2 h3,
      Fmap.disjoint (h2 \u h3) h1
    = (Fmap.disjoint h1 h2 /\ Fmap.disjoint h1 h3).

  Check Fmap.disjoint_union_eq_r : forall h1 h2 h3,
     Fmap.disjoint h1 (h2 \u h3)
   = (Fmap.disjoint h1 h2 /\ Fmap.disjoint h1 h3).
*)

(** **** Exercise: 1 star, standard, optional (hstar_assoc)

    Complete the right-to-left part of the proof of associativity of the
    star operator. *)

Lemma hstar_assoc : forall H1 H2 H3,
  (H1 \* H2) \* H3 = H1 \* (H2 \* H3).
Proof using.
  intros. applys himpl_antisym.
  { intros h (h'&h3&M1&M2&D&U). destruct M1 as (h1&h2&M3&M4&D'&U').
    subst h'. rewrite Fmap.disjoint_union_eq_l in D.
    exists h1 (h2 \u h3). splits.
    { applys M3. }
    { exists* h2 h3. }
    { rewrite* @Fmap.disjoint_union_eq_r. }
    { rewrite* @Fmap.union_assoc in U. } }
(* FILL IN HERE *) Admitted.

(** [] *)

End FundamentalProofs.

(* ================================================================= *)
(** ** Proof of the Consequence Rule *)

Module ProveConsequenceRules.

(** Recall the statement of the rule of consequence. *)

Lemma triple_conseq' : forall t H Q H' Q',
  triple t H' Q' ->
  H ==> H' ->
  Q' ===> Q ->
  triple t H Q.

(** A direct proof of [triple_conseq] goes through the low-level
    interpretation of Separation Logic triples in terms of heaps. *)

Proof using.
  (* No need to follow through this low-level proof. *)
  introv M WH WQ. rewrite triple_iff_triple_lowlevel in *.
  intros h1 h2 D HH. forwards (v&h1'&D'&R&HQ): M D. applys WH HH.
  exists v h1'. splits~. applys WQ HQ.
Qed.

(** An alternative proof consists of first establishing the consequence
    rule for the [hoare] judgment, then derive its generalization to
    the [triple] judgment of Separation Logic. *)

(** **** Exercise: 3 stars, standard, especially useful (hoare_conseq)

    Prove the consequence rule for Hoare triples. *)

Lemma hoare_conseq : forall t H Q H' Q',
  hoare t H' Q' ->
  H ==> H' ->
  Q' ===> Q ->
  hoare t H Q.
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 2 stars, standard, especially useful (triple_conseq)

    Prove the consequence rule by leveraging the lemma [hoare_conseq].
    Hint: unfold the definition of [triple], apply the lemma [hoare_conseq]
    with the appropriate arguments, then exploit [himpl_frame_l]
    to prove the entailment relations. *)

Lemma triple_conseq : forall t H Q H' Q',
  triple t H' Q' ->
  H ==> H' ->
  Q' ===> Q ->
  triple t H Q.
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

End ProveConsequenceRules.

(* ================================================================= *)
(** ** Proof of the Extraction Rules for Triples *)

Module ProveExtractionRules.

(** Recall the extraction rule for pure facts. *)

Parameter triple_hpure' : forall t (P:Prop) H Q,
  (P -> triple t H Q) ->
  triple t (\[P] \* H) Q.

(** To prove this lemma, we first the establish corresponding
    result on [hoare], then derive its version for [triple]. *)

Lemma hoare_hpure : forall t (P:Prop) H Q,
  (P -> hoare t H Q) ->
  hoare t (\[P] \* H) Q.
Proof using.
  introv M. intros h (h1&h2&M1&M2&D&U). destruct M1 as (M1&HP).
  subst. rewrite Fmap.union_empty_l. applys M HP M2.
Qed.

Lemma triple_hpure : forall t (P:Prop) H Q,
  (P -> triple t H Q) ->
  triple t (\[P] \* H) Q.
Proof using.
  introv M. unfold triple. intros H'.
  rewrite hstar_assoc. applys hoare_hpure.
  intros HP. applys M HP.
Qed.

(** Similarly, the extraction rule for existentials for
    [triple] can be derived from that for [hoare]. *)

(** **** Exercise: 2 stars, standard, especially useful (triple_hexists)

    Prove the extraction rule [triple_hexists].
    Hint: start by stating and proving the corresponding
    lemma for [hoare] triples. *)

Lemma hoare_hexists : forall t (A:Type) (J:A->hprop) Q,
  (forall x, hoare t (J x) Q) ->
  hoare t (\exists x, J x) Q.
Proof using. introv M. intros h (x&Hh). applys M Hh. Qed.

Lemma triple_hexists : forall t (A:Type) (J:A->hprop) Q,
  (forall x, triple t (J x) Q) ->
  triple t (\exists x, J x) Q.
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** Remark: the rules for extracting existentials out of entailments
    and out of preconditions can be stated in a slightly more concise
    way by exploiting the combinator [hexists] rather than its associated
    notation [\exists x, H], which stands for [hexists (fun x => H)].

    These formulation, shown below, tend to behave slightly better with
    respect to Coq unification, hence we use them in the CFML framework. *)

Parameter hstar_hexists' : forall A (J:A->hprop) H,
  (hexists J) \* H = hexists (J \*+ H).

Parameter triple_hexists' : forall t (A:Type) (J:A->hprop) Q,
  (forall x, triple t (J x) Q) ->
  triple t (hexists J) Q.

(** Remark: in chapter [Hprop], we observed that [\[P]] can be
    encoded as [\exists (p:P), \[]]. When this encoding is used,
    the rule [triple_hpure] turns out to be a particular instance
    of the rule [triple_hexists], as we prove next. *)

Parameter hpure_encoding : forall P,
  \[P] = (\exists (p:P), \[]).

Lemma triple_hpure_from_triple_hexists : forall t (P:Prop) H Q,
  (P -> triple t H Q) ->
  triple t (\[P] \* H) Q.
Proof using.
  introv M. rewrite hpure_encoding.
  rewrite hstar_hexists. (* disable notation printing to see the effect *)
  applys triple_hexists. (* [forall (p:P), ...] is the same as [P -> ...] *)
  rewrite hstar_hempty_l. applys M.
Qed.

End ProveExtractionRules.

(* ----------------------------------------------------------------- *)
(** *** Rules for Naming Heaps *)

(** Thereafter, we write [= h] for [fun h' => h' = h], that is,
    the heap predicate that only accepts heaps exactly equal to [h]. *)

(** **** Exercise: 3 stars, standard, optional (hexists_named_eq)

    Prove that a heap predicate [H] is equivalent to the heap
    predicate which asserts that the heap is, for a heap [h]
    such that [H h], exactly equal to [H].

    Hint: use [hstar_hpure_l] and [hexists_intro], as well as
    the extraction rules [himpl_hexists_l] and [himpl_hstar_hpure_l]. *)

Lemma hexists_named_eq : forall H,
  H = (\exists h, \[H h] \* (= h)).
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 1 star, standard, optional (hoare_named_heap)

    Prove that the proposition [hoare t H Q] is equivalent to:
    for any heap [h] satisfying the precondition [H], the Hoare
    triple whose precondition requires the input heap to be exactly
    equal to [h], and whose postcondition is [Q] holds. *)

Lemma hoare_named_heap : forall t H Q,
  (forall h, H h -> hoare t (= h) Q) ->
  hoare t H Q.
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 3 stars, standard, optional (triple_named_heap)

    Prove the counterpart of [hoare_named_heap] for Separation
    Logic triples.

    It is possible to exploit the lemma [hoare_named_heap], yet
    there exists a simpler, more direct proof that exploits
    the lemma [hexists_name_eq], which is stated above. *)

Lemma triple_named_heap : forall t H Q,
  (forall h, H h -> triple t (= h) Q) ->
  triple t H Q.
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(* ================================================================= *)
(** ** Alternative Structural Rule for Existentials *)

Module AlternativeExistentialRule.

(** Traditional papers on Separation Logic do not include [triple_hexists],
    but instead a rule called [triple_hexists2] that includes an existential
    quantifier both in the precondition and the postcondition.

    As we show next, in the presence of the consequence rule,
    the two rules are equivalent.

    The formulation of [triple_hexists] is not only more concise, it is
    also better suited for practical applications. *)

Lemma triple_hexists2 : forall A (Hof:A->hprop) (Qof:A->val->hprop) t,
  (forall x, triple t (Hof x) (Qof x)) ->
  triple t (\exists x, Hof x) (fun v => \exists x, Qof x v).
Proof using.
  introv M.
  applys triple_hexists. intros x.
  applys triple_conseq (M x).
  { applys himpl_refl. }
  { intros v. applys himpl_hexists_r x. applys himpl_refl. }
Qed.

Lemma triple_hexists_of_triple_hexists2 : forall t (A:Type) (Hof:A->hprop) Q,
  (forall x, triple t (Hof x) Q) ->
  triple t (\exists x, Hof x) Q.
Proof using.
  introv M.
  applys triple_conseq (\exists x, Hof x) (fun (v:val) => \exists (x:A), Q v).
  { applys triple_hexists2. intros x. applys M. }
  { applys himpl_refl. }
  { intros v. applys himpl_hexists_l. intros _. applys himpl_refl. }
Qed.

End AlternativeExistentialRule.

(* ================================================================= *)
(** ** Historical Notes *)

(** Nearly every project that aims for practical program verification using
    Separation Logic features, in one way or another, some amount of tooling
    for automatically simplifying Separation Logic assertion.

    The tactic used here, [xsimpl], was developed for the CFML tool.
    Its specification may be found in Appendix K from the paper:
    http://www.chargueraud.org/research/2020/seq_seplogic/seq_seplogic.pdf
    though it makes sense to wait until chapter [Wand] for reading it. *)

(* 2021-11-09 19:56 *)
