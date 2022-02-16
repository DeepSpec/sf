(** * Affine: Affine Separation Logic *)

Set Implicit Arguments.
From SLF Require Rules.
From SLF Require Export LibSepReference.

Implicit Types f : var.
Implicit Types b : bool.
Implicit Types v : val.
Implicit Types h : heap.
Implicit Types P : Prop.
Implicit Types H : hprop.
Implicit Types Q : val->hprop.

(* ################################################################# *)
(** * First Pass *)

(** The Separation Logic framework that we have constructed is
    well-suited for a language with explicit deallocation, but cannot
    be used as such for a language equipped with a garbage collector.

    As we pointed out in the chapter [Basic], there is no rule in
    our basic Separation Logic that allows discarding a heap predicate
    from the precondition or the postcondition.

    In this chapter, we explain how to generalize the Separation Logic
    framework to support a "discard rule", which one may invoke to discard
    heap predicates from the precondition or from the postcondition.

    The framework extended with the discard rule corresponds to an "affine"
    logic, where heap predicates may be freely discarded, as opposed to a
    "linear" logic, where heap predicates cannot be thrown away.

    This chapter is organized as follows:

    - first, we recall the example illustrating the limitation of a logic
      without a discard rule, for a garbage-collected language;
    - second, we present several versions of the "discard rule";
    - third, we show how to refine the definition of Separation Logic
      triples in such a way that the discard rules are satisfied.

    Although in the present course we consider a language for which it is
    desirable that any heap predicate can be discarded, we will present
    general definitions allowing to fine-tune which heap predicates can
    be discarded and which cannot be discarded by the user. We argue further
    on why such a fine-tuning may be interesting. *)

(* ================================================================= *)
(** ** Motivation for the Discard Rule *)

Module MotivatingExample.
Export DemoPrograms.

(** Let us recall the example of the function [succ_using_incr_attempt]
    from chapter [Basic]. This function allocates a reference with
    contents [n], then increments that reference, and finally returning
    its contents, that is, [n+1]. Let us revisit this example, with
    this time the intention of establishing for it a postcondition that
    does not leak the existence of a left-over reference cell. *)

Definition succ_using_incr :=
  <{ fun 'n =>
       let 'p = ref 'n in
       incr 'p;
       ! 'p }>.

(** In the framework developed so far, the heap predicate describing the
    reference cell allocated by the function cannot be discarded, because
    the code considered does not include a deallocation operation. Thus,
    we are forced to include in the postcondition the description of a
    left-over reference with a heap predicate, e.g., [\exists p, p ~~> (n+1)],
    or [\exists p m, p ~~> m]. *)

Lemma triple_succ_using_incr : forall (n:int),
  triple (succ_using_incr n)
    \[]
    (fun r => \[r = n+1] \* \exists p, (p ~~> (n+1))).
Proof using.
  xwp. xapp. intros p. xapp. xapp. xsimpl. auto.
Qed.

(** If we try to prove a specification that does not mention the left-over
    reference, then we get stuck with a proof obligation of the form
    [p ~~> (n+1) ==> \[]]. *)

Lemma triple_succ_using_incr' : forall (n:int),
  triple (succ_using_incr n)
    \[]
    (fun r => \[r = n+1]).
Proof using.
  xwp. xapp. intros p. xapp. xapp. xsimpl. { auto. } (* stuck here *)
Abort.

(** This situation is desirable in a programming language with explicit
    deallocation, because it ensures that the code written by the
    programmer is not missing any deallocation operation. However, it is
    ill-suited for a programming language equipped with a garbage collector
    that deallocates data automatically.

    In this chapter, we present an "affine" version of Separation Logic,
    where the above function [succ_using_incr] does admits the simple
    postcondition [fun r => \[r = n+1]], i.e., that needs not mention the
    left-over reference in the postcondition. *)

End MotivatingExample.

(* ================================================================= *)
(** ** Statement of the Discard Rule *)

(** There are several ways to state the "discard rule".
    Let us begin with two rules: one that discards a heap predicate [H']
    from the postcondition, and one that discards a heap predicate [H']
    from the precondition. *)

(** The first rule, named [triple_hany_post], asserts that an arbitrary heap
    predicate [H'] can be dropped from the postcondition, simplifying it from
    [Q \*+ H'] to [Q]. *)

Parameter triple_hany_post : forall t H H' Q,
  triple t H (Q \*+ H') ->
  triple t H Q.

(** Let us show that, using the rule [triple_hany_post], we can derive
    the desired specification for the motivating example from the
    specification that mentions the left-over postcondition. *)

Module MotivatingExampleSolved.
Export MotivatingExample.

Lemma triple_succ_using_incr' : forall (n:int),
  triple (succ_using_incr n)
    \[]
    (fun r => \[r = n+1]).
Proof using.
  intros. applys triple_hany_post. applys triple_succ_using_incr.
Qed.

End MotivatingExampleSolved.

(** A symmetric rule, named [triple_hany_pre], asserts that an arbitrary
    heap predicate [H'] can be dropped from the precondition, simplifying
    it from [H \* H'] to [H]. *)

Parameter triple_hany_pre : forall t H H' Q,
  triple t H Q ->
  triple t (H \* H') Q.

(** Observe the difference between the two rules. In [triple_hany_post],
    the discarded predicate [H'] appears in the premise, reflecting the
    fact that we discard it after the evaluation of the term [t]. On the
    contrary, in [triple_hany_pre], the discarded predicate [H'] appears
    in the conclusion, reflecting the fact that we discard it before the
    evaluation of [t]. *)

(** The two rules [triple_hany_pre] and [triple_hany_post] can be derived from
    each other. As we will establish further on, the rule [triple_hany_pre] is
    derivable from [triple_hany_post], by a simple application of the frame
    rule. Reciprocally, [triple_hany_post] is derivable from [triple_hany_pre],
    however the proof is more involved (it appears in the bonus section). *)

(* ================================================================= *)
(** ** Fine-grained Control on Collectable Predicates *)

(** As suggested in the introduction, it may be useful to constrain
    the discard rule in such a way that it can be used to discard only
    certain types of heap predicates, and not arbitrary heap predicates.

    For example, even in a programming language featuring a garbage
    collector, it may be useful to ensure that every file handle opened
    eventually gets closed, or that every lock acquired is eventually
    released. File handles and locks are example of resources that may
    be described in Separation Logic, yet that one should not be allowed
    to discard freely.

    As another example, consider the extension of Separation Logic with
    "time credits", which are used for complexity analysis. In such a
    setting, it is desirable to be able to throw away a positive number of
    credits to reflect for over-approximations in the analysis. However,
    the logic must forbid discarding predicates that capture a negative
    number of credits, otherwise soundness would be compromised. *)

(** The idea is to restrict the discard rules so that only predicates
    satisyfing a predicate called [haffine] may get discarded. The two
    discard rules will thus feature an extra premise requiring [haffine H'],
    where [H'] denotes the heap predicate being discarded. *)

Module Preview.

Parameter haffine : hprop -> Prop.

Parameter triple_haffine_post : forall t H H' Q,
  haffine H' ->
  triple t H (Q \*+ H') ->
  triple t H Q.

Parameter triple_haffine_pre : forall t H H' Q,
  haffine H' ->
  triple t H Q ->
  triple t (H \* H') Q.

End Preview.

(** To constraint the discard rule and allow fine-tuning of which heap
    predicates may be thrown away, we introduce the notions of "affine
    heap" and of "affine heap predicates", captured by the judgments
    [heap_affine h] and [haffine H], respectively.

    The definition of [heap_affine h] is left abstract for the moment.
    We will show two extreme instantiations: one that leads to a logic
    where all predicates are affine (i.e. can be freely discarded),
    one one that leads to a logic where all predicates are linear
    (i.e. none can be freely discarded, like in our previous set up). *)

(* ================================================================= *)
(** ** Definition of [heap_affine] and of [haffine] *)

(** Concretely, the notion of "affine heap" is characterize by the abstract
    predicate named [heap_affine], which is a predicate over heaps. *)

Parameter heap_affine : heap -> Prop.

(** This predicate [heap_affine] is assumed to satisfy two properties: it holds
    of the empty heap, and it is stable by (disjoint) union of heaps. *)

Parameter heap_affine_empty :
  heap_affine Fmap.empty.

Parameter heap_affine_union : forall h1 h2,
  heap_affine h1 ->
  heap_affine h2 ->
  Fmap.disjoint h1 h2 ->
  heap_affine (Fmap.union h1 h2).

(** The predicate [haffine H] captures the notion of "affine heap predicate".
    A heap predicate is affine iff it only holds of affine heaps. *)

Definition haffine (H:hprop) : Prop :=
  forall h, H h -> heap_affine h.

(** The predicate [haffine] distributes in a natural way on each of the
    operators of Separation Logic: the combination of affine heap predicates
    yields affine heap predicates. In particular:

    - [\[]] and [\[P]], which describes empty heaps, can always be discarded;
    - [H1 \* H2] can be discarded if both [H1] and [H2] can be discarded;
    - [\exists x, H] and [\forall x, H] can be discarded if [H] can be
      discarded for any [x].

*)

Lemma haffine_hempty :
  haffine \[].
Proof using.
  introv K. lets E: hempty_inv K. subst. applys heap_affine_empty.
Qed.

Lemma haffine_hpure : forall P,
  haffine \[P].
Proof using.
  intros. intros h K. lets (HP&M): hpure_inv K.
  subst. applys heap_affine_empty.
Qed.

Lemma haffine_hstar : forall H1 H2,
  haffine H1 ->
  haffine H2 ->
  haffine (H1 \* H2).
Proof using.
  introv M1 M2 K. lets (h1&h2&K1&K2&D&U): hstar_inv K.
  subst. applys* heap_affine_union.
Qed.

Lemma haffine_hexists : forall A (J:A->hprop),
  (forall x, haffine (J x)) ->
  haffine (\exists x, (J x)).
Proof using. introv F1 (x&Hx). applys* F1. Qed.

Lemma haffine_hforall' : forall A (J:A->hprop),
  (exists x, haffine (J x)) ->
  haffine (\forall x, (J x)).
Proof using.
  introv (x&Hx) M. lets N: hforall_inv M. applys* Hx.
Qed.

(** The rule [haffine_hforall'] requires the user to provide evidence
    that there exists at least one value [x] of type [A] for which
    [haffine (J x)] is true. In practice, the user is generally not
    interested in proving properties of a specific value [x], but is
    happy to justify that [J x] is affine for any [x]. The corresponding
    statement appears below, with an assumption [Inhab A] asserting that
    the type [A] is inhabited. In practice, the [\forall] quantifier
    is always invoked on inhabited types, so this is a benign restriction. *)

Lemma haffine_hforall : forall A `{Inhab A} (J:A->hprop),
  (forall x, haffine (J x)) ->
  haffine (\forall x, (J x)).
Proof using.
  introv IA M. applys haffine_hforall'. exists (arbitrary (A:=A)). applys M.
Qed.

(** In addition, [haffine (\[P] \* H)] should simplify to [haffine H]
    under the hypothesis [P]. Indeed, if a heap [h] satisfies [\[P] \* H],
    then it must be the case that the proposition [P] is true. Formally: *)

Lemma haffine_hstar_hpure_l : forall P H,
  (P -> haffine H) ->
  haffine (\[P] \* H).
Proof using. introv M. intros h K. rewrite hstar_hpure_l in K. applys* M. Qed.

(* ================================================================= *)
(** ** Definition of the "Affine Top" Heap Predicates *)

(** We next introduce a new heap predicate, called "affine top" and
    written [\GC], that is very handy for describing "the possibility
    to discard a heap predicate". We use this predicate to reformulate the
    discard rules in a more concise and more usable manner.

    This predicate is written [\GC] and named [hgc] in the formalization.
    It holds of any affine heap.

    [\GC] can be equivalently defined as [heap_affine], or as
    [exists H, \[haffine H] \* H]. The latter formulation is expressed
    in terms of existing Separation Logic operators, hence it is easier
    to manipulate in proofs using the [xsimpl] tactic. *)

Definition hgc : hprop :=
  \exists H, \[haffine H] \* H.

Declare Scope hgc_scope.
Open Scope hgc_scope.

Notation "\GC" := (hgc) : hgc_scope.

(** The introduction lemmas asserts that [\GC h] holds when [h]
    satisfies [heap_affine]. *)

(** **** Exercise: 2 stars, standard, especially useful (triple_frame)

    Prove that the affine heap predicate holds of any affine heap. *)

Lemma hgc_intro : forall h,
  heap_affine h ->
  \GC h.
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** The elimination lemma asserts the reciprocal. *)

(** **** Exercise: 2 stars, standard, optional (hgc_inv)

    Prove the elimination lemma for [\GC] expressed using [heap_affine]. *)

Lemma hgc_inv : forall h,
  \GC h ->
  heap_affine h.
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** Together, the introduction and the elimination rule justify the fact that
    [hgc] could equivalently have been defined as [heap_affine]. *)

Lemma hgc_eq_heap_affine :
  hgc = heap_affine.
Proof using.
  intros. applys himpl_antisym.
  { intros h M. applys* hgc_inv. }
  { intros h M. applys* hgc_intro. }
Qed.

(* ================================================================= *)
(** ** Properties of the [\GC] Predicate *)

(** One fundamental property that appears necessary in many of the
    soundness proofs is the following lemma, which asserts that two
    occurences of [\GC] can be collapsed into just one. *)

Lemma hstar_hgc_hgc :
  (\GC \* \GC) = \GC.
Proof using.
  unfold hgc. applys himpl_antisym.
  { xpull. intros H1 K1 H2 K2. xsimpl (H1 \* H2). applys* haffine_hstar. }
  { xpull. intros H K. xsimpl H \[]. auto. applys haffine_hempty. }
Qed.

(** Another useful property is that the heap predicate [\GC] itself
    satisifes [haffine]. Indeed, [\GC] denotes some heap [H] such that
   [H] is affine; Thus, by essence, it denotes an affine heap predicate. *)

Lemma haffine_hgc :
  haffine \GC.
Proof using.
  applys haffine_hexists. intros H. applys haffine_hstar_hpure_l. auto.
Qed.

(** The process of exploiting the [\GC] to "absorb" affine heap predicates
    is captured by the following lemma, which asserts that a heap predicate
    [H] entails [\GC] whenever [H] is affine. *)

Lemma himpl_hgc_r : forall H,
  haffine H ->
  H ==> \GC.
Proof using. introv M. intros h K. applys hgc_intro. applys M K. Qed.

(** In particular, the empty heap predicate [\[]] entails [\GC], because the
    empty heap predicate is affine (recall lemma [haffine_hempty]). *)

Lemma hempty_himpl_hgc :
  \[] ==> \GC.
Proof using. applys himpl_hgc_r. applys haffine_hempty. Qed.

(** Using the predicate [\GC], we can reformulate the constrained
    discard rule [triple_haffine_post] as follows. *)

Parameter triple_hgc_post : forall t H Q,
  triple t H (Q \*+ \GC) ->
  triple t H Q.

(** Not only is this rule more concise than [triple_haffine_post], it
    also has the benefits that the piece of heap discarded, previously
    described by [H'], no longer needs to be provided upfront at the
    moment of applying the rule. It may be provided further on in the
    reasoning, for example in an entailment, by instantiating the
    existential quantifier carried into the definition of [\GC]. *)

(* ================================================================= *)
(** ** Instantiation of [heap_affine] for a Fully Affine Logic *)

Module FullyAffineLogic.

(** To set up a fully affine logic, we consider a definition of
    [heap_affine] that holds of any heap. *)

Parameter heap_affine_def : forall h,
  heap_affine h = True.

(** It is trivial to check that [heap_affine] satisfies the required
    distribution properties on the empty heap and the union of heaps. *)

Lemma heap_affine_empty :
  heap_affine Fmap.empty.
Proof using. rewrite* heap_affine_def. Qed.

Lemma heap_affine_union : forall h1 h2,
  heap_affine h1 ->
  heap_affine h2 ->
  Fmap.disjoint h1 h2 ->
  heap_affine (Fmap.union h1 h2).
Proof using. intros. rewrite* heap_affine_def. Qed.

(** With that instantiation, [haffine] holds of any heap predicate. *)

Lemma haffine_equiv : forall H,
  (haffine H) <-> True.
Proof using.
  intros. iff M.
  { auto. }
  { unfold haffine. intros. rewrite* heap_affine_def. }
Qed.

(** With that instantiation, the affine top predicate [\GC] is equivalent
    to the top predicate [htop], defined as [fun h => True] or, equivalently,
    as [\exists H, H]. *)

Definition htop : hprop :=
  \exists H, H.

Lemma hgc_eq_htop : hgc = htop.
Proof using.
  unfold hgc, htop. applys himpl_antisym.
  { xsimpl. }
  { xsimpl. intros. rewrite* haffine_equiv. }
Qed.

End FullyAffineLogic.

(* ================================================================= *)
(** ** Instantiation of [heap_affine] for a Fully Linear Logic *)

Module FullyLinearLogic.

(** To set up a fully affine logic, we consider a definition of
    [heap_affine] that holds only of empty heaps. *)

Parameter heap_affine_def : forall h,
  heap_affine h = (h = Fmap.empty).

(** Again, it is not hard to check that [heap_affine] satisfies the
    required distributivity properties. *)

Lemma heap_affine_empty :
  heap_affine Fmap.empty.
Proof using. rewrite* heap_affine_def. Qed.

Lemma heap_affine_union : forall h1 h2,
  heap_affine h1 ->
  heap_affine h2 ->
  Fmap.disjoint h1 h2 ->
  heap_affine (Fmap.union h1 h2).
Proof using.
  introv K1 K2 D. rewrite heap_affine_def in *.
  subst. rewrite* Fmap.union_empty_r.
Qed.

(** The predicate [haffine H] is equivalent to [H ==> \[]],
    that is, it characterizes heap predicates that hold of the
    empty heap. *)

Lemma haffine_equiv : forall H,
  haffine H <-> (H ==> \[]).
Proof using.
  intros. unfold haffine. iff M.
  { intros h K. specializes M K. rewrite heap_affine_def in M.
    subst. applys hempty_intro. }
  { intros h K. specializes M K. rewrite heap_affine_def.
    applys hempty_inv M. }
Qed.

(** With that instantiation, the affine top predicate [\GC] is equivalent
    to the empty heap predicate [hempty]. *)

Lemma hgc_eq_hempty : hgc = hempty.
Proof using.
  unfold hgc. applys himpl_antisym.
  { xpull. introv N. rewrite* haffine_equiv in N. }
  { xsimpl \[]. applys haffine_hempty. }
Qed.

End FullyLinearLogic.

(* ================================================================= *)
(** ** Refined Definition of Separation Logic Triples *)

Module NewTriples.

(** Thereafter, we purposely leave the definition of [haffine]
    abstract, for the sake of generality.

    In what follows, we explain how to refine the notion of Separation
    Logic triple so as to accomodate the discard rule.

    Recall the definition of triple for a linear logic.

    Definition triple (t:trm) (H:hprop) (Q:val->hprop) : Prop :=
      forall (H':hprop), hoare t (H \* H') (Q \*+ H').

    The discard rule [triple_htop_post] asserts that postconditions
    may be freely extended with the [\GC] predicate. To support
    this rule, it suffices to modify the definition of [triple] to
    include the predicate [\GC] in the postcondition of the underlying
    Hoare triple, as follows. *)

Definition triple (t:trm) (H:hprop) (Q:val->hprop) : Prop :=
  forall (H':hprop), hoare t (H \* H') (Q \*+ H' \*+ \GC).

(** Observe that this definition of [triple] is strictly more general than
    the previous one. Indeed, as explained earlier on, when considering the
    fully linear instantiation of [haffine], the predicate [\GC] is equivalent
    to the empty predicate [\[]]. In this case, the occurence of [\GC] that
    appears in the definition of [triple] can be replaced with [\[]], yielding
    a definition equivalent to our original definition of [triple]. *)

(** For the updated definition of [triple] using [\GC], one can prove that:

    - all the existing reasoning rules of Separation Logic remain sound;
    - the discard rules [triple_htop_post], [triple_haffine_hpost]
      and [triple_haffine_hpre] can be proved sound.

*)

(* ================================================================= *)
(** ** Soundness of the Existing Rules *)

(** Let us update the soundness proof for the other structural rules. *)

(** **** Exercise: 3 stars, standard, especially useful (triple_frame)

    Prove the frame rule for the definition of [triple] that includes [\GC].
    Hint: unfold the definition of [triple] but not that of [hoare],
    then exploit lemma [hoare_conseq] and conclude using the tactic [xsimpl]. *)

Lemma triple_frame : forall t H Q H',
  triple t H Q ->
  triple t (H \* H') (Q \*+ H').
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 3 stars, standard, optional (triple_conseq)

    Prove the frame rule for the definition of [triple] that includes [\GC].
    Hint: follow the same approach as in the proof of [triple_frame],
    and leverage the tactic [xchange] to conclude. *)

Lemma triple_conseq : forall t H' Q' H Q,
  triple t H' Q' ->
  H ==> H' ->
  Q' ===> Q ->
  triple t H Q.
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** The extraction rules remain valid as well. *)

Lemma triple_hpure : forall t (P:Prop) H Q,
  (P -> triple t H Q) ->
  triple t (\[P] \* H) Q.
Proof using.
  introv M. unfolds triple. intros H'.
  rewrite hstar_assoc. applys* hoare_hpure.
Qed.

Lemma triple_hexists : forall t (A:Type) (J:A->hprop) Q,
  (forall x, triple t (J x) Q) ->
  triple t (\exists x, J x) Q.
Proof using.
  introv M. unfolds triple. intros H'.
  rewrite hstar_hexists. applys* hoare_hexists.
Qed.

(** The standard reasoning rules of Separation Logic can be derived
    for the revised notion of Separation Logic triple, the one which
    includes [\GC], following essentially the same proofs as for the
    original Separation Logic triples. The main difference is that one
    sometimes needs to invoke the lemma [hstar_hgc_hgc] for collapsing
    two [\GC] into a single one.

    In what follows, we present just one representative example of
    such proofs, namely the reasoning rule for sequences. This proof
    is similar to that of lemma [triple_seq] from chapter [Rules]. *)

Lemma triple_seq : forall t1 t2 H Q H1,
  triple t1 H (fun v => H1) ->
  triple t2 H1 Q ->
  triple (trm_seq t1 t2) H Q.
Proof using.
  introv M1 M2. intros H'. unfolds triple.
  applys hoare_seq.
  { applys M1. }
  { applys hoare_conseq. { applys M2. } { xsimpl. }
    { xchanges hstar_hgc_hgc. } }
Qed.

(* ================================================================= *)
(** ** Soundness of the Discard Rules *)

Module Export GCRules.

(** Let us first establish the soundness of the discard rule
    [triple_htop_post]. *)

(** **** Exercise: 3 stars, standard, especially useful (triple_hgc_post)

    Prove [triple_h_post] with respect to the refined definition of
    [triple] that includes [\GC] in the postcondition.
    Hint: exploit [hoare_conseq], then exploit [hstar_hgc_hgc], with
    help of the tactics [xchange] and [xsimpl]. *)

Lemma triple_hgc_post : forall t H Q,
  triple t H (Q \*+ \GC) ->
  triple t H Q.
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 1 star, standard, especially useful (triple_haffine_post)

    Prove that [triple_haffine_post] is derivable from [triple_hgc_post].
    Hint: unfold the definition of [\GC] using [unfold hgc]. *)

Lemma triple_haffine_post : forall t H H' Q,
  haffine H' ->
  triple t H (Q \*+ H') ->
  triple t H Q.
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 1 star, standard, optional (triple_hgc_post_from_triple_haffine_post)

    Reciprocally, prove that [triple_hgc_post] is derivable from
    [triple_haffine_post]. *)

Lemma triple_hgc_post_from_triple_haffine_post : forall t H Q,
  triple t H (Q \*+ \GC) ->
  triple t H Q.
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 1 star, standard, optional (triple_haffine_pre)

    Prove that [triple_haffine_pre] is derivable from [triple_hgc_post].
    Hint: exploit the frame rule, and leverage [triple_hgc_post]
    either directly or by invoking its corollary [triple_haffine_post]. *)

Lemma triple_haffine_pre : forall t H H' Q,
  haffine H' ->
  triple t H Q ->
  triple t (H \* H') Q.
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 1 star, standard, optional (triple_conseq_frame_hgc)

    Prove the combined structural rule [triple_conseq_frame_hgc], which
    extends [triple_conseq_frame] with the discard rule, replacing
    [Q1 \*+ H2 ===> Q] with [Q1 \*+ H2 ===> Q \*+ \GC].
    Hint: invoke [triple_conseq], [triple_frame] and [triple_hgc_post]
    in the appropriate order. *)

Lemma triple_conseq_frame_hgc : forall H2 H1 Q1 t H Q,
  triple t H1 Q1 ->
  H ==> H1 \* H2 ->
  Q1 \*+ H2 ===> Q \*+ \GC ->
  triple t H Q.
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 1 star, standard, optional (triple_ramified_frame_hgc)

    Prove the following generalization of the ramified frame rule
    that includes the discard rule.
    Hint: it is a corollary of [triple_conseq_frame_hgc]. Take inspiration
    from the proof of [triple_ramified_frame] in chapter [Wand]. *)

Lemma triple_ramified_frame_hgc : forall H1 Q1 t H Q,
  triple t H1 Q1 ->
  H ==> H1 \* (Q1 \--* (Q \*+ \GC)) ->
  triple t H Q.
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

End GCRules.

(* ================================================================= *)
(** ** Discard Rules in WP Style *)

(** Let us update the definition of [wp] to use the new definition
    of [triple]. *)

Definition wp (t:trm) (Q:val->hprop) : hprop :=
  \exists (H:hprop), H \* \[triple t H Q].

(** Recall the characteristic equivalence of [wp]. *)

Lemma wp_equiv : forall t H Q,
  (H ==> wp t Q) <-> (triple t H Q).
Proof using.
  unfold wp. iff M.
  { applys* triple_conseq Q M.
    applys triple_hexists. intros H'.
    rewrite hstar_comm. applys* triple_hpure. }
  { xsimpl* H. }
Qed.

(** In weakest precondition style, the discard rule [triple_hgc_post]
    translates into the entailment [wp t (Q \*+ \GC) ==> wp t Q],
    as we prove next. *)

(** **** Exercise: 1 star, standard, optional (wp_hgc_post)

    Prove the discard rule in wp-style.
    Hint: exploit [wp_equiv] and [triple_hgc_post]. *)

Lemma wp_hgc_post : forall t Q,
  wp t (Q \*+ \GC) ==> wp t Q.
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** Likewise, the wp-style presentation of the rule [triple_hgc_pre]
    takes the following form. *)

Lemma wp_haffine_pre : forall t H Q,
  haffine H ->
  (wp t Q) \* H ==> wp t Q.
Proof using.
  introv K. rewrite wp_equiv. applys triple_haffine_pre.
  { applys K. } { rewrite* <- wp_equiv. }
Qed.

(** The revised presentation of the wp-style ramified frame rule includes
    an extra [\GC] predicate. This rule captures at once all the structural
    properties of Separation Logic, including the discard rule. *)

Lemma wp_ramified : forall Q1 Q2 t,
  (wp t Q1) \* (Q1 \--* (Q2 \*+ \GC)) ==> (wp t Q2).

(** For a change, let us present below a direct proof for this lemma,
    that is, not reusing the structural rules associated with triples. *)

Proof using.
  intros. unfold wp. xpull ;=> H M.
  xsimpl (H \* (Q1 \--* Q2 \*+ \GC)).
  unfolds triple. intros H'.
  applys hoare_conseq (M ((Q1 \--* Q2 \*+ \GC) \* H')).
  { xsimpl. } { xchange hstar_hgc_hgc. xsimpl. }
Qed.

(* ================================================================= *)
(** ** Exploiting the Discard Rule in Proofs *)

(** In a practical verification proof, there are two useful ways to
    discard heap predicates that are no longer needed:

    - either by invoking [triple_haffine_pre] to remove a specific
      predicate from the current state, i.e., the precondition;
    - or by invoking [triple_htop_post] to add a [\GC] into the
      current postcondition and allow subsequent removal of any
      predicate that may be left-over in the final entailment
      justifying that the final state satisfies the postcondition.

    Eager removal of predicates from the current state is never
    necessary: one can always be lazy and postpone the application
    of the discard rule until the last step of reasoning.

    In practical, it usually suffices to anticipate, right from the
    beginning of the verification proof, the possibility of discarding
    heap predicates from the final state.

    To that end, we apply the rule [triple_htop_post] as very first
    step of the proof to extend the postcondition with a [\GC] predicate,
    which will be used to absorb all the garbage left-over at the end
    of the proof.

    We implement this strategy in a systematic manner by integrating
    directly the rule [triple_htop_post] into the tactic [xwp], which
    sets up the verification proof by computing the characteristic formula.
    To that end, we generalize the lemma [xwp_lemma], which the tactic
    [xwp] applies. Its original statement is as follows. *)

Parameter xwp_lemma : forall v1 v2 x t1 H Q,
  v1 = val_fun x t1 ->
  H ==> wpgen ((x,v2)::nil) t1 Q ->
  triple (trm_app v1 v2) H Q.

(** Its generalized form extends the postcondition to which the formula
    computed by [wpgen] is applied from [Q] to [Q \*+ \GC], as shown below. *)

Lemma xwp_lemma' : forall v1 v2 x t1 H Q,
  v1 = val_fun x t1 ->
  H ==> wpgen ((x,v2)::nil) t1 (Q \*+ \GC) ->
  triple (trm_app v1 v2) H Q.
Proof using. introv E M. applys triple_hgc_post. applys* xwp_lemma. Qed.

(** Let us update the tactic [xwp] to exploit the lemma [xwp_lemma']
    instead of [xwp_lemma]. *)

Tactic Notation "xwp" :=
  intros; applys xwp_lemma';
  [ reflexivity | simpl; unfold wpgen_var; simpl ].

(* ================================================================= *)
(** ** Example Proof Involving Discarded Heap Predicates *)

(** Using the updated version of [xwp], let us revisite the proof of our
    motivating example [succ_using_incr] in a fully affine logic, i.e.,
    a logical where any predicate can be discarded. *)

Module MotivatingExampleWithUpdatedXwp.
Export MotivatingExample.

(** Assume a fully affine logic. *)

Parameter haffine_hany : forall (H:hprop),
  haffine H.

(** Observe in the proof below the [\GC] introduced in the postcondition
    by the call to [xwp]. *)

Lemma triple_succ_using_incr : forall (n:int),
  triple (succ_using_incr n)
    \[]
    (fun r => \[r = n+1]).
Proof using.
  xwp. xapp. intros r. xapp. xapp. xsimpl. { auto. }
  (* There remains to absorb the left-over reference into the [\GC] predicate *)
  applys himpl_hgc_r. applys haffine_hany.
Qed.

(** We will show further on how to automate the work from the last line
    of the proof above, by setting up [xsimpl] to automatically resolve
    goals of the form [H ==> \GC]. *)

End MotivatingExampleWithUpdatedXwp.


(* ################################################################# *)
(** * More Details *)

(* ================================================================= *)
(** ** Revised Definition of [mkstruct] *)

(** Recall the definition [mkstruct], as stated in the file [Wand].

    Definition mkstruct (F:formula) : formula :=
      fun Q => \exists Q', (F Q') \* (Q' \--* Q).

    This definition can be generalized to handle not just the consequence
    and the frame rule, but also the discard rule.

    To that end, we augment [mkstruct] with an additional [\GC], as follows. *)

Definition mkstruct (F:formula) : formula :=
  fun Q => \exists Q', F Q' \* (Q' \--* (Q \*+ \GC)).

(** Let us prove that this revised definition of [mkstruct] does sastisfy
    the [wp]-style statement of the discard rule, which is stated
    in a way similar to [wp_hgc_post]. *)

Lemma mkstruct_hgc : forall Q F,
  mkstruct F (Q \*+ \GC) ==> mkstruct F Q.
Proof using.
  intros. unfold mkstruct. set (X := hgc) at 3. replace X with (\GC \* \GC).
  { xsimpl. } { subst X. apply hstar_hgc_hgc. }
Qed.

(** Besides, let us prove that the revised definition of [mkstruct] still
    satisfies the three originally required properties: erasure, consequence,
    and frame.

    Remark: the proofs shown below exploit a version of [xsimpl] that handles
    the magic wand but provides no built-in support for the [\GC] predicate. *)

Lemma mkstruct_erase : forall F Q,
  F Q ==> mkstruct F Q.
Proof using.
  intros. unfold mkstruct. xsimpl Q. apply himpl_hgc_r. apply haffine_hempty.
Qed.

Lemma mkstruct_conseq : forall F Q1 Q2,
  Q1 ===> Q2 ->
  mkstruct F Q1 ==> mkstruct F Q2.
Proof using.
  introv WQ. unfold mkstruct. xpull. intros Q'. xsimpl Q'. xchange WQ.
Qed.

Lemma mkstruct_frame : forall F H Q,
  (mkstruct F Q) \* H ==> mkstruct F (Q \*+ H).
Proof using.
  intros. unfold mkstruct. xpull. intros Q'. xsimpl Q'.
Qed.

(** **** Exercise: 2 stars, standard, optional (mkstruct_haffine_post)

    Prove the reformulation of [triple_haffine_post] adapted to [mkstruct],
    for discarding an affine piece of postcondition.
    Hint: [haffine] is an opaque definition at this stage; the assumption
    [haffine] needs to be exploited using the lemma [himpl_hgc_r]. *)

Lemma mkstruct_haffine_post : forall H Q F,
  haffine H ->
  mkstruct F (Q \*+ H) ==> mkstruct F Q.
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 2 stars, standard, optional (mkstruct_haffine_pre)

    Prove the reformulation of [triple_haffine_pre] adapted to [mkstruct],
    for discarding an affine piece of postcondition. *)

Lemma mkstruct_haffine_pre : forall H Q F,
  haffine H ->
  (mkstruct F Q) \* H ==> mkstruct F Q.
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

End NewTriples.

(* ================================================================= *)
(** ** The Tactic [xaffine], and Behavior of [xsimpl] on [\GC] *)

Module Xaffine.

(** The tactic [xaffine] applys to a goal of the form [haffine H].
    The tactic simplifies the goal using all the distributivity rules
    associated with [haffine]. Ultimately, it invokes [eauto with haffine],
    which can leverage knowledge specific to the definition of [haffine]
    from the Separation Logic set up at hand. *)

Create HintDb haffine.

Tactic Notation "xaffine" :=
  repeat match goal with |- haffine ?H =>
    match H with
    | (hempty) => apply haffine_hempty
    | (hpure _) => apply haffine_hpure
    | (hstar _ _) => apply haffine_hstar
    | (hexists _) => apply haffine_hexists
    | (hforall _) => apply haffine_hforall
    | (hgc) => apply haffine_hgc
    | _ => eauto with haffine
    end
  end.

Lemma xaffine_demo : forall H1 H2 H3,
  haffine H1 ->
  haffine H3 ->
  haffine (H1 \* H2 \* H3).
Proof using. introv K1 KJ. xaffine. (* remains [haffine H2] *) Abort.

End Xaffine.

Module XsimplExtended.
Import LibSepReference.

(** The tactic [xsimpl] is extended with support for simplifying goals
    of the form [H ==> \GC] into [haffine H], using lemma [himpl_hgc_r].
    For example, [xsimpl] can simplify the goal [H1 \* H2 ==> H2 \* \GC]
    into just [haffine H1]. *)

Lemma xsimpl_xgc_demo : forall H1 H2,
  H1 \* H2 ==> H2 \* \GC.
Proof using. intros. xsimpl. (* remains [haffine H1] *) Abort.

(** In addition, [xsimpl] invokes the tactic [xaffine] to simplify
    side-conditions of the form [haffine H]. For example, [xsimpl]
    can prove the following lemma. *)

Lemma xsimpl_xaffine_demo : forall H1 H2,
  haffine H1 ->
  H1 \* H2 ==> H2 \* \GC.
Proof using. introv K1. xsimpl. Qed.

End XsimplExtended.

(* ================================================================= *)
(** ** The Proof Tactics for Applying the Discard Rules *)

Module XGC.
Import LibSepReference.

(** To present the discard tactics [xgc], [xc_keep] and [xgc_post],
    we import the definitions from [LibSepDirect] but assume that the
    definition of [mkstruct] is like the one presented in the present
    file, that is, including the [\GC] when defining [mkstruct F]
    as [fun Q => \exists Q', F Q' \* (Q' \--* (Q \*+ \GC))].

    As argued earlier on, with this definition, [mkstruct] satisfies the
    following discard rule. *)

Parameter mkstruct_hgc : forall Q F,
  mkstruct F (Q \*+ \GC) ==> mkstruct F Q.

(** The tactic [xgc H] removes [H] from the precondition (i.e. from the
    current state), in the course of a proof exploiting a formula produced
    by [wpgen].

    More precisely, the tactic invokes the following variant of the rule
    [triple_haffine_pre], which allows to leverage [xsimpl] for computing
    the heap predicate [H2] that remains after a predicate [H1] is removed
    from a precondition [H], through the entailment [H ==> H1 \* H2]. *)

Lemma xgc_lemma: forall H1 H2 H F Q,
  H ==> H1 \* H2 ->
  haffine H1 ->
  H2 ==> mkstruct F Q ->
  H ==> mkstruct F Q.
Proof using.
  introv WH K M. xchange WH. xchange M.
  applys himpl_trans mkstruct_frame.
  applys himpl_trans mkstruct_hgc.
  applys mkstruct_conseq. xsimpl.
Qed.

Tactic Notation "xgc" constr(H) :=
  eapply (@xgc_lemma H); [ xsimpl | xaffine | ].

Lemma xgc_demo : forall H1 H2 H3 F Q,
  haffine H2 ->
  (H1 \* H2 \* H3) ==> mkstruct F Q.
Proof using. introv K2. xgc H2. (* clears [H2] *) Abort.

(** The tactic [xgc_keep H] is a variant of [xgc] that enables to discard
    everything but [H] from the precondition.

    The implementation of the tactic leverages the same lemma [xgc_lemma],
    only providing [H2] instead of [H1]. *)

Tactic Notation "xgc_keep" constr(H) :=
  eapply (@xgc_lemma _ H); [ xsimpl | xaffine | ].

Lemma xgc_keep_demo : forall H1 H2 H3 F Q,
  haffine H1 ->
  haffine H3 ->
  (H1 \* H2 \* H3) ==> mkstruct F Q.
Proof using. introv K1 K3. xgc_keep H2. Abort.

(** The tactic [xgc_post] simply extends the postcondition with a [\GC],
    to enable subsequent discarding of heap predicates in the final
    entailment. *)

Lemma xgc_post_lemma : forall H Q F,
  H ==> mkstruct F (Q \*+ \GC) ->
  H ==> mkstruct F Q.
Proof using. introv M. xchange M. applys mkstruct_hgc. Qed.

Tactic Notation "xgc_post" :=
  apply xgc_post_lemma.

Lemma xgc_keep_demo : forall H1 H2 H3 F Q,
  haffine H1 ->
  haffine H3 ->
  H1 ==> mkstruct F (Q \*+ H2 \*+ H3) ->
  H1 ==> mkstruct F Q.
Proof using.
  introv K1 K3 M. xgc_post. xchange M. applys mkstruct_conseq. xsimpl.
  (* Check out how the end proof fails without the call to [xgc_post]. *)
Abort.

End XGC.

(* ################################################################# *)
(** * Optional Material *)

(* ================================================================= *)
(** ** Alternative Statement for Distribution of [haffine] on Quantifiers *)

Module HaffineQuantifiers.

(** Recall the lemmas [haffine_hexists] and [haffine_hforall].

    Lemma haffine_hexists : forall A (J:A->hprop),
      (forall x, haffine (J x)) ->
      haffine (\exists x, (J x)).

    Lemma haffine_hforall : forall A `{Inhab A} (J:A->hprop),
      (forall x, haffine (J x)) ->
      haffine (\forall x, (J x)).

    They can be reformulated in a more concise way, as explained next. *)

(** First, to smoothly handle the distribution on the quantifiers, let us
    extend the notion of "affinity" to postconditions. The predicate
    [haffine_post J] asserts that [haffine] holds of [J x] for any [x]. *)

Definition haffine_post (A:Type) (J:A->hprop) : Prop :=
  forall x, haffine (J x).

(** The rules then reformulate as follows. *)

Lemma haffine_hexists : forall A (J:A->hprop),
  haffine_post J ->
  haffine (hexists J).
Proof using. introv F1 (x&Hx). applys* F1. Qed.

Lemma haffine_hforall : forall A `{Inhab A} (J:A->hprop),
  haffine_post J ->
  haffine (hforall J).
Proof using.
  introv IA F1 Hx. lets N: hforall_inv Hx. applys* F1 (arbitrary (A:=A)).
Qed.

End HaffineQuantifiers.

(* ================================================================= *)
(** ** Pre and Post Rules *)

Module FromPreToPostGC.
Import Rules ProofsSameSemantics.

(** Earlier on, we proved that [triple_hgc_pre] is derivable from
    [triple_hgc_post], through a simple application of the frame rule.

    We wrote that, reciprocally, the rule [triple_hgc_post] is derivable
    from [triple_hgc_pre], yet with a slightly more involved proof.
    Let us present this proof.

    In other word, assume [triple_hgc_pre], and let us prove the
    result [triple_hgc_post]. *)

Parameter triple_hgc_pre : forall t H Q,
  triple t H Q ->
  triple t (H \* \GC) Q.

Lemma triple_hgc_post : forall t H Q,
  triple t H (Q \*+ \GC) ->
  triple t H Q.

(** The key idea of the proof is that a term [t] admits the same behavior
    as [let x = t in x]. Thus, to simulate discarding a predicate from
    the postcondition of [t], one can invoke the discard rule on the
    precondition of the variable [x] that appears at the end of
    [let x = t in x].

    To formalize this idea, recall from [Rules] the lemma
    [eval_like_eta_expansion] which asserts the equivalence of
    [t] and [let x = t in x], and recall the lemma [triple_eval_like],
    which asserts that two equivalent terms satisfy the same triples. *)

Proof using.
  introv M. lets E: eval_like_eta_expansion t "x".
  applys triple_eval_like E. applys triple_let.
  { applys M. }
  { intros v. simpl. applys triple_hgc_pre. applys triple_val. auto. }
Qed.

End FromPreToPostGC.

(* ================================================================= *)
(** ** Low-level Definition of Refined Triples *)

Module LowLevel.
Import NewTriples.

(** Consider the updated definition of [triple] introduced in this chapter. *)

Definition triple (t:trm) (H:hprop) (Q:val->hprop) : Prop :=
  forall (H':hprop), hoare t (H \* H') (Q \*+ H' \*+ \GC).

(** In chapter [Hprop], we presented an alternative definition for
    Separation Logic triples, called [triple_lowlevel], expressed directly
    in terms of heaps.

    Definition triple_lowlevel (t:trm) (H:hprop) (Q:val->hprop) : Prop :=
      forall h1 h2,
      Fmap.disjoint h1 h2 ->
      H h1 ->
      exists h1' v,
           Fmap.disjoint h1' h2
        /\ eval (h1 \u h2) t (h1' \u h2) v
        /\ Q v h1'.

    In what follows, we explain how to generalize this definition to match
    our revised definition of [triple], and thereby obtain a direct definition
    expressed in terms of heap, that does not depend on the definition of
    [hstar] nor that of [\GC].

    Let us aim instead for a direct definition, entirely expressed in terms
    of union of heaps. To that end, we need to introduce an additional piece of
    state to describe the piece of the final heap covered by the [\GC]
    predicate.

    We will need to describe the disjointness of the 3 pieces of heap that
    describe the final state. To that end, we exploit the auxiliary definition
    [Fmap.disjoint_3 h1 h2 h3], which asserts that the three arguments denote
    pairwise disjoint heaps. It is defined in the module [Fmap] as follows.

    Definition disjoint_3 (h1 h2 h3:heap) : Prop :=
         disjoint h1 h2
      /\ disjoint h2 h3
      /\ disjoint h1 h3.
*)

(** We then formulate [triple_lowlevel] using a final state of the from
    [h1' \u h2 \u h3'] instead of just [h1' \u h2]. There, [h3'] denotes
    the piece of the final state covered by the [\GC] heap predicate.
    This piece of state is an affine heap, as captured by [heap_affine h3']. *)

Definition triple_lowlevel (t:trm) (H:hprop) (Q:val->hprop) : Prop :=
  forall h1 h2,
  Fmap.disjoint h1 h2 ->
  H h1 ->
  exists h1' h3' v,
       Fmap.disjoint_3 h1' h2 h3'
    /\ heap_affine h3'
    /\ eval (h1 \u h2) t (h1' \u h2 \u h3') v
    /\ Q v h1'.

(** One can prove the equivalence of [triple] and [triple_lowlevel]
    following a similar proof pattern as previously. *)

Lemma triple_eq_triple_lowlevel :
  triple = triple_lowlevel.
Proof using.
  applys pred_ext_3. intros t H Q.
  unfold triple, triple_lowlevel, hoare. iff M.
  { introv D P1.
    forwards~ (h'&v&R1&R2): M (=h2) (h1 \u h2). { apply* hstar_intro. }
    destruct R2 as (h2'&h1''&N0&N1&N2&N3).
    destruct N0 as (h1'&h3'&T0&T1&T2&T3). subst.
    exists h1' h1'' v. splits*.
    { rew_disjoint. auto. }
    { applys hgc_inv N1. }
    { applys_eq* R1. } }
  { introv (h1&h2&N1&N2&D&U).
    forwards~ (h1'&h3'&v&R1&R2&R3&R4): M h1 h2.
    exists (h1' \u h3' \u h2) v. splits*.
    { applys_eq* R3. }
    { subst. rewrite hstar_assoc. apply* hstar_intro.
      rewrite hstar_comm. applys* hstar_intro. applys* hgc_intro. } }
Qed.

End LowLevel.

(* ================================================================= *)
(** ** Historical Notes *)

(** The seminal presentation of Separation Logic concerns a linear logic, for
    a programming language with explicit deallocation. More recent works on
    Separation Logic for ML-style languages, equipped with a garbage collector,
    consider affine logics. For example, the original presentation of the Iris
    framework provides an affine entailment, for which [H ==> \[]] is always
    true. Follow-up work on Iris provides encodings for supporting linear
    resources, i.e., resources that are not allowed to be "dropped on the
    floor".

    This chapter gives a presentation of Separation Logic featuring a
    customizable predicate [haffine] for controlling which resources should be
    treated as affine, and which ones should be treated as linear. This
    direct approach to controlling linearity was introduced in the context of
    CFML, in work by [Guéneau, Jourdan, Charguéraud, and Pottier 2019] (in Bib.v) *)

(* 2022-02-16 01:39 *)
