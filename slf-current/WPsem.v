(** * WPsem: Semantics of Weakest Preconditions *)

Set Implicit Arguments.
From SLF Require Export Rules.

Implicit Types f : var.
Implicit Types b : bool.
Implicit Types v : val.
Implicit Types h : heap.
Implicit Types P : Prop.
Implicit Types H : hprop.
Implicit Types Q : val->hprop.

(* ################################################################# *)
(** * First Pass *)

(** In previous chapters, we have introduced the notion of
    Separation Logic triple, written [triple t H Q].

    In this chapter, we introduce the notion of "weakest precondition"
    for Separation Logic triples, written [wp t Q].

    The intention is for [wp t Q] to be a heap predicate (of type [hprop])
    such that [H ==> wp t Q] if and only if [triple t H Q] holds.

    The benefits of introducing weakest preconditions is two-fold:

    - the use of [wp] greatly reduces the number of structural rules
      required, and thus reduces accordingly the number of tactics
      required for carrying out proofs in practice;
    - the predicate [wp] will serve as guidelines for setting up in the
      next chapter a "characteristic formula generator", which is the
      key ingredient at the heart of the implementation of the CFML tool.

    This chapter presents:

    - the notion of weakest precondition, as captured by [wp],
    - the reformulation of structural rules in [wp]-style,
    - the reformulation of reasoning rules in [wp]-style,
    - (optional) alternative, equivalent definitions for [wp],
      and alternative proofs for deriving [wp]-style reasoning rules. *)

(* ================================================================= *)
(** ** Notion of Weakest Precondition *)

(** We next introduce a function [wp], called "weakest precondition".
    Given a term [t] and a postcondition [Q], the expression [wp t Q]
    denotes a heap predicate [wp t Q] such that, for any heap predicate
    [H], the entailment [H ==> wp t Q] is equivalent to [triple t H Q].

    The notion of [wp] usually sounds fairly mysterious at first sight.
    It will make more sense when we describe the properties of [wp]. *)

Parameter wp : trm -> (val->hprop) -> hprop.

Parameter wp_equiv : forall t H Q,
  (H ==> wp t Q) <-> (triple t H Q).

(** The [wp t Q] is called "weakest precondition" for two reasons:
    because (1) it is a precondition, and (2) it is the weakest one,
    as we explain next.

    First, [wp t Q] is always a "valid precondition" for a
    triple associated with the term [t] and the postcondition [Q]. *)

Lemma wp_pre : forall t Q,
  triple t (wp t Q) Q.
Proof using. intros. rewrite <- wp_equiv. applys himpl_refl. Qed.

(** Second, [wp t Q] is the "weakest" of all valid preconditions
    for the term [t] and the postcondition [Q], in the sense that
    any other valid precondition [H], i.e. satisfying [triple t H Q],
    is such that [H] entails [wp t Q]. *)

Lemma wp_weakest : forall t H Q,
  triple t H Q ->
  H ==> wp t Q.
Proof using. introv M. rewrite wp_equiv. applys M. Qed.

(** In other words, [wp t Q] is the "smallest" [H] satisfying
    [triple t H Q] with respect to the order on heap predicates
    induced by the entailment relation [==>]. *)

(** There are several equivalent ways to define [wp], as we show
    in the optional contents of this chapter. It turns out that
    the equivalence [(H ==> wp t Q) <-> (triple t H Q)] fully
    characterizes the predicate [wp], and that it is all we need
    to carry out formal reasoning.

    For this reason, we postpone to further on in this chapter the
    description of alternative, direct definitions for [wp]. *)

(* ================================================================= *)
(** ** Structural Rules in Weakest-Precondition Style *)

(** We next present reformulations of the frame rule and of the rule
    of consequence in "weakest-precondition style". *)

(* ----------------------------------------------------------------- *)
(** *** The Frame Rule *)

(** The frame rule for [wp] asserts that [(wp t Q) \* H] entails
    [wp t (Q \*+ H)]. This statement can be read as follows:
    if you own both a piece of state satisfying [H] and a piece of state
    in which the execution of [t] produces (a result and an output value
    satisfying) [Q], then you own a piece of state in which the execution
    of [t] produces [Q \*+ H], that is, produces both [Q] and [H]. *)

Lemma wp_frame : forall t H Q,
  (wp t Q) \* H ==> wp t (Q \*+ H).

(** The lemma is proved by exploiting the frame rule for triples
    and the equivalence that characterizes [wp]. *)

Proof using.
  intros. rewrite wp_equiv.
  applys triple_frame. rewrite* <- wp_equiv.
Qed.

(** The connection with the frame might not be totally obvious.
    Recall the frame rule for triples.

    triple t H1 Q ->
    triple t (H1 \* H) (Q \*+ H)

    Let us replace the form [triple t H Q] with the form
    [H ==> wp t Q]. We obtain the following statement. *)

Lemma wp_frame_trans : forall t H1 Q H,
  H1 ==> wp t Q ->
  (H1 \* H) ==> wp t (Q \*+ H).

(** If we exploit transitivity of entailment to eliminate [H1], then we
    obtain exactly [wp_frame], as illustrated by the proof script below. *)

Proof using. introv M. xchange M. applys* wp_frame. Qed.

(* ----------------------------------------------------------------- *)
(** *** The Rule of Consequence *)

(** The rule of consequence for [wp] materializes as a covariance
    property: it asserts that [wp t Q] is covariant in [Q].
    In other words, if one weakens [Q], then one weakens [wp t Q].
    The corresponding formal statement appears next. *)

Lemma wp_conseq : forall t Q1 Q2,
  Q1 ===> Q2 ->
  wp t Q1 ==> wp t Q2.
Proof using.
  introv M. rewrite wp_equiv. applys* triple_conseq (wp t Q1) M. applys wp_pre.
Qed.

(** The connection with the rule of consequence is, again, not
    totally obvious. Recall the rule of consequence for triples.

    triple t H1 Q1 ->
    H2 ==> H1 ->
    Q1 ===> Q2 ->
    triple t H2 Q2

    Let us replace the form [triple t H Q] with the form [H ==> wp t Q].
    We obtain the following statement: *)

Lemma wp_conseq_trans : forall t H1 H2 Q1 Q2,
  H1 ==> wp t Q1 ->
  H2 ==> H1 ->
  Q1 ===> Q2 ->
  H2 ==> wp t Q2.

(** If we exploit transitivity of entailment to eliminate [H1] and [H2],
    then we obtain exactly [wp_conseq], as illustrated below. *)

Proof using.
  introv M WH WQ. xchange WH. xchange M. applys wp_conseq WQ.
Qed.

(* ----------------------------------------------------------------- *)
(** *** The Extraction Rules *)

(** The extraction rules [triple_hpure] and [triple_hexists]
    have no specific counterpart with the [wp] presentation.
    Indeed, in a weakest-precondition style presentation, the
    extraction rules for triples correspond exactly to the
    extraction rules for entailment.

    To see why, consider for example the rule [triple_hpure]. *)

Parameter triple_hpure : forall t (P:Prop) H Q,
  (P -> triple t H Q) ->
  triple t (\[P] \* H) Q.

(** Replacing the form [triple t H Q] with [H ==> wp t Q] yields
    the following statement. *)

Lemma triple_hpure_with_wp : forall t H Q (P:Prop),
  (P -> (H ==> wp t Q)) ->
  (\[P] \* H) ==> wp t Q.

(** The above implication is just a special case of the extraction
    lemma for pure facts on the left on an entailment, named
    [himpl_hstar_hpure_l], and whose statement is as follows.

    (P -> (H ==> H')) ->
    (\[P] \* H) ==> H'.

    Instantiating [H'] with [wp t Q] proves [triple_hpure_with_wp].
*)

Proof using. introv M. applys himpl_hstar_hpure_l M. Qed.

(** A similar reasoning applies to the extraction rule for existentials. *)

(* ================================================================= *)
(** ** Reasoning Rules for Terms, in Weakest-Precondition Style *)

(* ----------------------------------------------------------------- *)
(** *** Rule for Values *)

(** Recall the rule [triple_val] which gives a reasoning rule for
    establishing a triple for a value [v]. *)

Parameter triple_val : forall v H Q,
  H ==> Q v ->
  triple (trm_val v) H Q.

(** If we rewrite this rule in [wp] style, we obtain the rule below.

    H ==> Q v ->
    H ==> wp (trm_val v) Q.

    By exploiting transitivity of entailment, we can eliminate [H].
    We obtain the following statement, which reads as follows:
    if you own a state satisfying [Q v], then you own a state
    from which the evaluation of the value [v] produces [Q].
*)

Lemma wp_val : forall v Q,
  Q v ==> wp (trm_val v) Q.
Proof using.
  intros. rewrite wp_equiv. applys* triple_val.
Qed.

(** We can verify that, when migrating to the [wp] presentation, we have
    not lost any expressiveness. To that end, we prove that [triple_val] is
    derivable from [wp_val]. *)

Lemma triple_val_derived_from_wp_val : forall v H Q,
  H ==> Q v ->
  triple (trm_val v) H Q.
Proof using. introv M. rewrite <- wp_equiv. xchange M. applys wp_val. Qed.

(* ----------------------------------------------------------------- *)
(** *** Rule for Sequence *)

(** Recall the reasoning rule for a sequence [trm_seq t1 t2]. *)

Parameter triple_seq : forall t1 t2 H Q H1,
  triple t1 H (fun v => H1) ->
  triple t2 H1 Q ->
  triple (trm_seq t1 t2) H Q.

(** Replacing [triple t H Q] with [H ==> wp t Q] throughout the rule
    gives the statement below.

      H ==> (wp t1) (fun v => H1) ->
      H1 ==> (wp t2) Q ->
      H ==> wp (trm_seq t1 t2) Q.

    This entailment holds for any [H] and [H1]. Let us specialize it to
    [H1 := (wp t2) Q] and [H := (wp t1) (fun v => (wp t2) Q)].

    This leads us to the following statement, which reads as follows:
    if you own a state from which the evaluation of [t1] produces a
    state from which the evaluation of [t2] produces the postcondition
    [Q], then you own a state from which the evaluation of the sequence
    [t1;t2] produces [Q]. *)

Lemma wp_seq : forall t1 t2 Q,
  wp t1 (fun v => wp t2 Q) ==> wp (trm_seq t1 t2) Q.
Proof using.
  intros. rewrite wp_equiv. applys triple_seq.
  { rewrite* <- wp_equiv. }
  { rewrite* <- wp_equiv. }
Qed.

(** **** Exercise: 2 stars, standard, optional (triple_seq_from_wp_seq)

    Check that [wp_seq] is just as expressive as [triple_seq],
    by proving that [triple_seq] is derivable from [wp_seq]
    and from the structural rules for [wp] and/or the structural
    rules for [triple]. *)

Lemma triple_seq_from_wp_seq : forall t1 t2 H Q H1,
  triple t1 H (fun v => H1) ->
  triple t2 H1 Q ->
  triple (trm_seq t1 t2) H Q.
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(* ################################################################# *)
(** * More Details *)

(* ================================================================= *)
(** ** Other Reasoning Rules for Terms *)

(* ----------------------------------------------------------------- *)
(** *** Rule for Functions *)

(** Recall the reasoning rule for a term [trm_fun x t1],
    which evaluates to the value [val_fun x t1]. *)

Parameter triple_fun : forall x t1 H Q,
  H ==> Q (val_fun x t1) ->
  triple (trm_fun x t1) H Q.

(** The rule for functions follow exactly the same pattern as for values. *)

Lemma wp_fun : forall x t Q,
  Q (val_fun x t) ==> wp (trm_fun x t) Q.
Proof using. intros. rewrite wp_equiv. applys* triple_fun. Qed.

(** A similar rule holds for the evaluation of a recursive function. *)

Lemma wp_fix : forall f x t Q,
  Q (val_fix f x t) ==> wp (trm_fix f x t) Q.
Proof using. intros. rewrite wp_equiv. applys* triple_fix. Qed.

(* ----------------------------------------------------------------- *)
(** *** Rule for Conditionals *)

(** Recall the reasoning rule for a term [triple_if b t1 t2]. *)

Parameter triple_if : forall b t1 t2 H Q,
  triple (if b then t1 else t2) H Q ->
  triple (trm_if (val_bool b) t1 t2) H Q.

(** Replacing [triple] using [wp] entailments yields:

    H ==> wp (if b then t1 else t2) Q ->
    H ==> wp (trm_if (val_bool b) t1 t2) Q.

    which simplifies by transitivity to:

    wp (if b then t1 else t2) Q ==> wp (trm_if (val_bool b) t1 t2) Q.

    This statement corresponds to the wp-style reasoning rule
    for conditionals. The proof appears next.
*)

Lemma wp_if : forall b t1 t2 Q,
  wp (if b then t1 else t2) Q ==> wp (trm_if (val_bool b) t1 t2) Q.
Proof using.
  intros. rewrite wp_equiv. applys triple_if. rewrite* <- wp_equiv.
Qed.

(* ----------------------------------------------------------------- *)
(** *** Rule for Let-Bindings *)

(** Recall the reasoning rule for a term [trm_let x t1 t2]. *)

Parameter triple_let : forall x t1 t2 Q1 H Q,
  triple t1 H Q1 ->
  (forall v1, triple (subst x v1 t2) (Q1 v1) Q) ->
  triple (trm_let x t1 t2) H Q.

(** The rule of [trm_let x t1 t2] is very similar to that for
    [trm_seq], the only difference being the substitution of
    [x] by [v] in [t2], where [v] denotes the result of [t1]. *)

Lemma wp_let : forall x t1 t2 Q,
  wp t1 (fun v1 => wp (subst x v1 t2) Q) ==> wp (trm_let x t1 t2) Q.
Proof using.
  intros. rewrite wp_equiv. applys triple_let.
  { rewrite* <- wp_equiv. }
  { intros v. rewrite* <- wp_equiv. }
Qed.

(* ----------------------------------------------------------------- *)
(** *** Rule For Function Applications *)

(** Recall the reasoning rule for an application [(val_fun x t1) v2]. *)

Parameter triple_app_fun : forall x v1 v2 t1 H Q,
  v1 = val_fun x t1 ->
  triple (subst x v2 t1) H Q ->
  triple (trm_app v1 v2) H Q.

(** The corresponding [wp] rule is stated and proved next. *)

Lemma wp_app_fun : forall x v1 v2 t1 Q,
  v1 = val_fun x t1 ->
  wp (subst x v2 t1) Q ==> wp (trm_app v1 v2) Q.
Proof using.
  introv EQ1. rewrite wp_equiv. applys* triple_app_fun.
  rewrite* <- wp_equiv.
Qed.

(** A similar rule holds for the application of a recursive function. *)

(* ################################################################# *)
(** * Optional Material *)

(* ================================================================= *)
(** ** A Concrete Definition for Weakest Precondition *)

Module WpHighLevel.

(** The lemma [wp_equiv] captures the characteristic property of [wp],
    that is, [ (H ==> wp t Q) <-> (triple t H Q) ].

    However, it does not give evidence that there exists a predicate [wp]
    satisfying this equivalence. We next present one possible definition.

    The idea is to define [wp t Q] as the predicate
    [\exists H, H \* \[triple t H Q]], which, reading litterally, is
    satisfied by "any" heap predicate [H] which is a valid precondition
    for a triple for the term [t] and the postcondition [Q]. *)

Definition wp (t:trm) (Q:val->hprop) : hprop :=
  \exists (H:hprop), H \* \[triple t H Q].

(** First, let us prove that [wp t Q] is itself a valid precondition,
    in the sense that [triple t (wp t Q) Q] always holds (as asserted
    by the lemma [wp_pre]).

    To establish this fact, we have to prove:
    [triple t (\exists H, H \* \[triple t H Q]) Q].

    Applying the extraction rule for existentials gives:
    [forall H, triple t (H \* \[triple t H Q]) Q].

    Applying the extraction rule for pure facts gives:
    [forall H, (triple t H Q) -> (triple t H Q)], which is true. *)

(** Second, let us demonstrate that the heap predicate [wp t Q]
    is entailed by any precondition [H] that satisfies [triple t H Q],
    as asserted by the lemma [wp_weakest].

    Assume [triple t H Q]. Let us prove [H ==> wp t Q], that is
    [H ==> \exists H, H \* \[triple t H Q]]. Instantiating the
    [H] on the right-hand side as the [H] from the left-hand side
    suffices to satisfy the entailment. *)

(** Recall that the properties [wp_pre] and [wp_weakest] were derivable
    from the characteristic equivalence [triple t H Q <-> H ==> wp Q].
    Thus, to formalize the proofs of [wp_pre] and [wp_weakest], all we
    have to do is to establish that equivalence. *)

(** **** Exercise: 2 stars, standard, especially useful (wp_equiv)

    Prove that the definition [wp_high] satisfies the
    characteristic equivalence for weakest preconditions. *)

Lemma wp_equiv : forall t H Q,
  (H ==> wp t Q) <-> (triple t H Q).
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

End WpHighLevel.

(* ================================================================= *)
(** ** Equivalence Between all Definitions Of [wp] *)

(** We next prove that the equivalence [(triple t H Q) <-> (H ==> wp t Q)]
    defines a unique predicate [wp]. In other words, all possible
    definitions of [wp] are equivalent to each another.
    Thus, it really does not matter which concrete definition
    of [wp] we consider: they are all equivalent.

    Concretely, assume two predicates [wp1] and [wp2] to both satisfy
    the characteristic equivalence. We prove that they are equal. *)

Lemma wp_unique : forall wp1 wp2,
  (forall t H Q, (triple t H Q) <-> (H ==> wp1 t Q)) ->
  (forall t H Q, (triple t H Q) <-> (H ==> wp2 t Q)) ->
  wp1 = wp2.
Proof using.
  introv M1 M2. applys fun_ext_2. intros t Q. applys himpl_antisym.
  { rewrite <- M2. rewrite M1. auto. }
  { rewrite <- M1. rewrite M2. auto. }
Qed.

(** Recall that both [wp_pre] and [wp_weakest] are derivable from
    [wp_equiv]. Let us also that, reciprocally, [wp_equiv] is derivable
    from the conjunction of [wp_pre] and [wp_weakest].

    In other words, the property of "being the weakest precondition"
    also uniquely characterizes the definition of [wp]. *)

Lemma wp_from_weakest_pre : forall wp',
  (forall t Q, triple t (wp' t Q) Q) ->  (* [wp_pre] *)
  (forall t H Q, triple t H Q -> H ==> wp' t Q) ->  (* [wp_weakest] *)
  (forall t H Q, H ==> wp' t Q <-> triple t H Q). (* [wp_equiv] *)
Proof using.
  introv M1 M2. iff M.
  { applys triple_conseq M1 M. auto. }
  { applys M2. auto. }
Qed.

(* ================================================================= *)
(** ** An Alternative Definition for Weakest Precondition *)

Module WpLowLevel.

(** The concrete definition for [wp] given above is expressed
    in terms of Separation Logic combinators. In contrast to
    this "high level" definition, there exists a more "low level"
    definition, expressed directly as a function over heaps.

    In that alternative definition, the heap predicate [wp t Q]
    is defined as a predicate that holds of a heap [h]
    if and only if the execution of [t] starting in exactly
    the heap [h] produces the post-condition [Q].

    Technically, [wp t Q] can be defined as:
    [fun (h:heap) => triple t (fun h' => h' = h) Q].
    In other words, the precondition requires the input heap
    to be exactly [h]. *)

Definition wp (t:trm) (Q:val->hprop) : hprop :=
  fun (h:heap) => triple t (fun h' => (h' = h)) Q.

(** **** Exercise: 4 stars, standard, optional (wp_equiv_wp_low)

    Prove this alternative definition of [wp] also satisfies the
    characteristic equivalence [H ==> wp Q <-> triple t H Q].
    Hint: exploit the lemma [triple_named_heap] which was
    established as an exercise in the appendix of the chapter
    [Himpl].) *)

Lemma wp_equiv_wp_low : forall t H Q,
  (H ==> wp t Q) <-> (triple t H Q).
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

End WpLowLevel.

(* ================================================================= *)
(** ** Extraction Rule for Existentials *)

(** Recall the extraction rule for existentials. *)

Parameter triple_hexists : forall t (A:Type) (J:A->hprop) Q,
  (forall x, triple t (J x) Q) ->
  triple t (\exists x, J x) Q.

(** Replacing [triple t H Q] with [H ==> wp t Q] yields the
    lemma stated below. *)

(** **** Exercise: 1 star, standard, optional (triple_hexists_in_wp)

    Prove the extraction rule for existentials in [wp] style. *)

Lemma triple_hexists_in_wp : forall t Q A (J:A->hprop),
  (forall x, (J x ==> wp t Q)) ->
  (\exists x, J x) ==> wp t Q.

Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** In other words, in the [wp] presentation, we do not need
    a specific extraction rule for existentials, because the
    extraction rule for entailment already does the job. *)

(* ================================================================= *)
(** ** Combined Structural Rule *)

(** Recall the combined consequence-frame rule for [triple]. *)

Parameter triple_conseq_frame : forall H2 H1 Q1 t H Q,
  triple t H1 Q1 ->
  H ==> H1 \* H2 ->
  Q1 \*+ H2 ===> Q ->
  triple t H Q.

(** Let us reformulate this rule using [wp], replacing the
    form [triple t H Q] with the form [H ==> wp t Q]. *)

(** **** Exercise: 2 stars, standard, especially useful (wp_conseq_frame_trans)

    Prove the combined structural rule in [wp] style.
    Hint: exploit [wp_conseq_trans] and [wp_frame]. *)

Lemma wp_conseq_frame_trans : forall t H H1 H2 Q1 Q,
  H1 ==> wp t Q1 ->
  H ==> H1 \* H2 ->
  Q1 \*+ H2 ===> Q ->
  H ==> wp t Q.
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** The combined structural rule for [wp] can actually be stated
    in a more concise way, as follows. The rule reads as follows:
    if you own a state from which the execution of [t] produces
    (a result and a state satisfying) [Q1] and you own [H], and
    if you can trade the combination of [Q1] and [H] against [Q2],
    the you own a piece of state from which the execution of [t]
    produces [Q2]. *)

(** **** Exercise: 2 stars, standard, especially useful (wp_conseq_frame)

    Prove the concise version of the combined structural rule
    in [wp] style. Many proofs are possible. *)

Lemma wp_conseq_frame : forall t H Q1 Q2,
  Q1 \*+ H ===> Q2 ->
  (wp t Q1) \* H ==> (wp t Q2).
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(* ================================================================= *)
(** ** Alternative Statement of the Rule for Conditionals *)

Module WpIfAlt.

(** We have established the following rule for reasoning about
    conditionals using [wp]. *)

Parameter wp_if : forall b t1 t2 Q,
  wp (if b then t1 else t2) Q ==> wp (trm_if b t1 t2) Q.

(** Equivalently, the rule may be stated with the conditional around
    the calls to [wp t1 Q] and [wp t2 Q]. *)

(** **** Exercise: 1 star, standard, optional (wp_if')

    Prove the alternative statement of rule [wp_if],
    either from [wp_if] or directly from [triple_if]. *)

Lemma wp_if' : forall b t1 t2 Q,
  (if b then (wp t1 Q) else (wp t2 Q)) ==> wp (trm_if b t1 t2) Q.
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

End WpIfAlt.

(* ================================================================= *)
(** ** Definition of [wp] Directly from [hoare] *)

(** Let's take a step back and look at our construction of
    Separation Logic so far.

    1. We defined Hoare triples ([hoare]) with respect to the big-step
       judgment ([eval]).

    2. We defined Separation Logic triples ([triple]) in terms of
       Hoare triples ([hoare]), through the definition:
       \[forall H', hoare t (H \* H') (Q \*+ H')].

    3. We then defined Separation Logic weakest-preconditions ([wp])
       in terms of Separation Logic triples ([triple]).

    Through the construction, we established reasoning rules, first
    for Hoare triples ([hoare]), then for Separation Logic triples
    ([triple]), and finally for weakest-preconditions ([wp]).

    One question that naturally arises is whether there is a more direct
    route to deriving reasoning rules for weakest preconditions.
    In other words, can we obtain the same end result through simpler
    proofs? *)

(** The notion of Hoare triple is a key abstraction that enables conduction
    further proofs without manipulating heaps (of type [heap]) explicitly.
    Experiments suggest that it is beneficial to introduce the Hoare
    logic layer. In other words, it is counterproductive to try an prove
    Separation Logic reasoning rules, whether for [triple] or for [wp],
    directly with respect to the evaluation judgment [eval].

    Thus, the only question that remains is whether it would have some
    interest to derive the reasoning rules for weakest preconditions ([wp])
    directly from the the reasoning rules for Hoare triples ([hoare]),
    that is, by bypassing the statement and proofs for the reasoning rules
    for Separation Logic triples ([triple]).

    In what follows, we show that if one cares only for [wp]-style rules,
    then the route to deriving them straight from [hoare]-style rules
    may indeed be somewhat shorter. *)

Module WpFromHoare.

(** Recall the definition of [triple] in terms of [hoare].

    Definition triple (t:trm) (H:hprop) (Q:val->hprop) : Prop :=
      forall (H':hprop), hoare t (H \* H') (Q \*+ H').

    In what follows, we conduct the proofs by assuming a concrete definition
    for [wp], namely [wp_high], which lends itself better to automated
    proofs. *)

Definition wp (t:trm) := fun (Q:val->hprop) =>
  \exists H, H \* \[triple t H Q].

(** First, we check the equivalence between [triple t H Q] and [H ==> wp t Q].
    This proof is the same as [wp_equiv] from the module [WpHighLevel]
    given earlier in this chapter. *)

Lemma wp_equiv : forall t H Q,
  (H ==> wp t Q) <-> (triple t H Q).
Proof using.
  unfold wp. iff M.
  { applys* triple_conseq Q M.
    applys triple_hexists. intros H'.
    rewrite hstar_comm. applys* triple_hpure. }
  { xsimpl* H. }
Qed.

(** Second, we prove the consequence-frame rule associated with [wp].
    It is the only structural rule that is needed for working with
    weakest preconditions. *)

Lemma wp_conseq_frame : forall t H Q1 Q2,
  Q1 \*+ H ===> Q2 ->
  (wp t Q1) \* H ==> (wp t Q2).

(** The proof leverages the consequence rule for [hoare] triples,
    and the frame property comes from the [forall H'] quantification
    baked in the definition of [triple]. *)

Proof using.
  introv M. unfold wp. xpull. intros H' N. xsimpl (H' \* H).
  unfolds triple. intros H''. specializes N (H \* H'').
  applys hoare_conseq N. { xsimpl. } { xchange M. }
Qed.

(** Third and last, we establish reasoning rules for terms in [wp]-style
    directly from the corresponding rules for [hoare] triples.

    The proof details are beyond the scope of this course.
    The point here is to show that the proofs are fairly concise. *)

Lemma wp_val : forall v Q,
  Q v ==> wp (trm_val v) Q.
Proof using.
  intros. unfold wp. xsimpl. intros H'. applys hoare_val. xsimpl.
Qed.

Lemma wp_fun : forall x t Q,
  Q (val_fun x t) ==> wp (trm_fun x t) Q.
Proof using.
  intros. unfold wp. xsimpl. intros H'. applys hoare_fun. xsimpl.
Qed.

Lemma wp_fix : forall f x t Q,
  Q (val_fix f x t) ==> wp (trm_fix f x t) Q.
Proof using.
  intros. unfold wp. xsimpl. intros H'. applys hoare_fix. xsimpl.
Qed.

Lemma wp_if : forall b t1 t2 Q,
  wp (if b then t1 else t2) Q ==> wp (trm_if b t1 t2) Q.
Proof using.
  intros. unfold wp. xsimpl. intros H M H'.
  applys hoare_if. applys M.
Qed.

Lemma wp_app_fun : forall x v1 v2 t1 Q,
  v1 = val_fun x t1 ->
  wp (subst x v2 t1) Q ==> wp (trm_app v1 v2) Q.
Proof using.
  introv EQ1. unfold wp. xsimpl. intros H' M. intros H''. applys* hoare_app_fun.
Qed.

Lemma wp_app_fix : forall f x v1 v2 t1 Q,
  v1 = val_fix f x t1 ->
  wp (subst x v2 (subst f v1 t1)) Q ==> wp (trm_app v1 v2) Q.
Proof using.
  introv EQ1. unfold wp. xsimpl. intros H' M. intros H''. applys* hoare_app_fix.
Qed.

(** **** Exercise: 4 stars, standard, especially useful (wp_let)

    Prove wp-style rule for let bindings. *)

Lemma wp_let : forall x t1 t2 Q,
  wp t1 (fun v => wp (subst x v t2) Q) ==> wp (trm_let x t1 t2) Q.
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** Note: [wp_seq] admits essentially the same proof as [wp_let], simply
    replacing [hoare_let] with [hoare_seq], and removing the tactic
    [intros v]. *)

(** It is technically possible to bypass even the definition of
    [triple] and specify all functions directly using the predicate
    [wp]. However, using [triple] leads to better readability of
    specifications, thus it seems preferable to continue using that
    style for specifying functions. (See discussion in chapter
    [Wand], appendix on "Texan triples".) *)

End WpFromHoare.

(* ================================================================= *)
(** ** Historical Notes *)

(** The idea of weakest precondition was introduced by [Dijstra 1975] (in Bib.v)
    in his seminal paper "Guarded Commands, Nondeterminacy and Formal
    Derivation of Programs".

    Weakest preconditions provide a reformulation of Floyd-Hoare logic.
    Numerous practical verification tools leverage weakest preconditions,
    e.g. ESC/Java, Why3, Boogie, Spec#, etc.

    In the context of Separation Logic in a proof assistant, the Iris framework
    (https://iris-project.org/), developed since 2015, exploits weakest
    preconditions to state reasoning rules. See the [Postscript]. *)

(* 2021-10-06 00:58 *)
