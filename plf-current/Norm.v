(** * Norm: Normalization of STLC *)

(* Chapter written and maintained by Andrew Tolmach *)

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Stdlib Require Import List.
From Stdlib Require Import Strings.String.
From PLF Require Import Maps.
From PLF Require Import Smallstep.

Hint Constructors multi : core.

(** This optional chapter is based on [Pierce 2002] (in Bib.v) Chapter 12,
    and [Ahmed 2015] (in Bib.v).  It may be useful to look at those
    references, since they include some explanations and informal
    proofs that are not repeated here.

    In this chapter, we consider another fundamental theoretical
    property of the simply typed lambda-calculus: the fact that the
    evaluation of a well-typed program is guaranteed to halt in a
    finite number of steps---i.e., every well-typed term is
    _normalizable_.

    Unlike the type-safety properties we have considered so far, the
    normalization property does not extend to full-blown programming
    languages, because these languages nearly always include features,
    such as general recursion (see the [MoreStlc] chapter) or
    recursive types, that can be used to write nonterminating
    programs.  However, the issue of normalization reappears at the
    level of _types_ when we consider the metatheory of polymorphic
    versions of the lambda calculus such as System F-omega: in this
    system, the language of types effectively contains a copy of the
    simply typed lambda-calculus, and the termination of the
    typechecking algorithm thus hinges on the fact that a
    "normalization" operation on type expressions is guaranteed to
    terminate.

    Another reason for studying normalization proofs is that they are
    some of the most beautiful---and mind-blowing---mathematics to be
    found in the type theory literature, often (as here) involving the
    fundamental proof technique of _logical relations_.  To give
    readers more exposure to this proof technique, we also use it to
    develop an alternative proof of type safety at the end of this
    chapter.

    The calculus we shall consider here is the simply typed
    lambda-calculus over a single base type [bool] and with
    pairs. We'll give most details of the development for the basic
    lambda-calculus terms treating [bool] as an uninterpreted base
    type, and leave the extension to the boolean operators and pairs
    to the reader.  Even for the base calculus, normalization is not
    trivial to prove, since each reduction of a term can duplicate
    redexes in subterms. *)

(** **** Exercise: 2 stars, standard (norm_fail)

    Where do we fail if we attempt to prove normalization by a
    straightforward induction on the size of a well-typed term? *)

(* FILL IN HERE *)

(* Do not modify the following line: *)
Definition manual_grade_for_norm_fail : option (nat*string) := None.
(** [] *)

(** The best ways to understand an intricate proof like this is
    are (1) to help fill it in and (2) to extend it.  We've omitted some
    parts of the following development, including some proofs of lemmas
    and all the cases involving products and conditionals, and left
    them as exercises. *)

(* ################################################################# *)
(** * Language *)

(** We begin by repeating the definition of our STLC variant, which is
    similar to those in the [MoreStlc] chapter, plus supporting
    results including type preservation and step determinism.  (We
    won't need progress.)  You may just wish to skip down to the
    Normalization section... *)

(* A handy tactic. *)
Ltac inv H := inversion H; subst; clear H.

Open Scope string.

(* ================================================================= *)
(** ** Syntax and Operational Semantics *)

Inductive ty : Type :=
  | Ty_Bool : ty
  | Ty_Arrow : ty -> ty -> ty
  | Ty_Prod  : ty -> ty -> ty.

Inductive tm : Type :=
    (* pure STLC *)
  | tm_var : string -> tm
  | tm_app : tm -> tm -> tm
  | tm_abs : string -> ty -> tm -> tm
    (* booleans *)
  | tm_true : tm
  | tm_false : tm
  | tm_if : tm -> tm -> tm -> tm
    (* pairs *)
  | tm_pair : tm -> tm -> tm
  | tm_fst : tm -> tm
  | tm_snd : tm -> tm.

Declare Custom Entry stlc.

Notation "<{ e }>" := e (e custom stlc at level 99).
Notation "( x )" := x (in custom stlc, x at level 99).
Notation "x" := x (in custom stlc at level 0, x constr at level 0).
Notation "S -> T" := (Ty_Arrow S T) (in custom stlc at level 50, right associativity).
Notation "x y" := (tm_app x y) (in custom stlc at level 1, left associativity).
Notation "\ x : t , y" :=
  (tm_abs x t y) (in custom stlc at level 90, x at level 99,
                     t custom stlc at level 99,
                     y custom stlc at level 99,
                     left associativity).
Coercion tm_var : string >-> tm.

Notation "{ x }" := x (in custom stlc at level 1, x constr).

Notation "'Bool'" := Ty_Bool (in custom stlc at level 0).
Notation "'if' x 'then' y 'else' z" :=
  (tm_if x y z) (in custom stlc at level 89,
                    x custom stlc at level 99,
                    y custom stlc at level 99,
                    z custom stlc at level 99,
                    left associativity).
Notation "'true'"  := true (at level 1).
Notation "'true'"  := tm_true (in custom stlc at level 0).
Notation "'false'"  := false (at level 1).
Notation "'false'"  := tm_false (in custom stlc at level 0).

Notation "X * Y" :=
  (Ty_Prod X Y) (in custom stlc at level 2, X custom stlc, Y custom stlc at level 0).
Notation "( x ',' y )" := (tm_pair x y) (in custom stlc at level 0,
                                                x custom stlc at level 99,
                                                y custom stlc at level 99).
Notation "t '.fst'" := (tm_fst t) (in custom stlc at level 1).
Notation "t '.snd'" := (tm_snd t) (in custom stlc at level 1).

(* ================================================================= *)
(** ** Substitution *)

Reserved Notation "'[' x ':=' s ']' t" (in custom stlc at level 20, x constr).

Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
  match t with
  | tm_var y =>
      if x =? y then s else t
  | <{ \ y : T, t1 }> =>
      if x =? y then t else <{ \y:T, [x:=s] t1 }>
  | <{t1 t2}> =>
      <{ ([x:=s]t1) ([x:=s]t2)}>
  | <{true}> =>
      <{true}>
  | <{false}> =>
      <{false}>
  | <{if t1 then t2 else t3}> =>
      <{if ([x:=s] t1) then ([x:=s] t2) else ([x:=s] t3)}>
  | <{(t1, t2)}> =>
      <{( ([x:=s] t1), ([x:=s] t2) )}>
  | <{t0.fst}> =>
      <{ ([x:=s] t0).fst}>
  | <{t0.snd}> =>
      <{ ([x:=s] t0).snd}>
  end

  where "'[' x ':=' s ']' t" := (subst x s t) (in custom stlc).

(* ================================================================= *)
(** ** Reduction *)

Inductive value : tm -> Prop :=
  | v_abs : forall x T2 t1,
      value <{\x:T2, t1}>
  | v_true :
      value <{true}>
  | v_false :
      value <{false}>
  | v_pair : forall v1 v2,
      value v1 ->
      value v2 ->
      value <{(v1, v2)}>.

Hint Constructors value : core.

Reserved Notation "t '-->' t'" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall x T2 t1 v2,
         value v2 ->
         <{(\x:T2, t1) v2}> --> <{ [x:=v2]t1 }>
  | ST_App1 : forall t1 t1' t2,
         t1 --> t1' ->
         <{t1 t2}> --> <{t1' t2}>
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 --> t2' ->
         <{v1 t2}> --> <{v1  t2'}>
  | ST_IfTrue : forall t1 t2,
      <{if true then t1 else t2}> --> t1
  | ST_IfFalse : forall t1 t2,
      <{if false then t1 else t2}> --> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 --> t1' ->
      <{if t1 then t2 else t3}> --> <{if t1' then t2 else t3}>
  | ST_Pair1 : forall t1 t1' t2,
        t1 --> t1' ->
        <{ (t1,t2) }> --> <{ (t1' , t2) }>
  | ST_Pair2 : forall v1 t2 t2',
        value v1 ->
        t2 --> t2' ->
        <{ (v1, t2) }> -->  <{ (v1, t2') }>
  | ST_Fst1 : forall t0 t0',
        t0 --> t0' ->
        <{ t0.fst }> --> <{ t0'.fst }>
  | ST_FstPair : forall v1 v2,
        value v1 ->
        value v2 ->
        <{ (v1,v2).fst }> --> v1
  | ST_Snd1 : forall t0 t0',
        t0 --> t0' ->
        <{ t0.snd }> --> <{ t0'.snd }>
  | ST_SndPair : forall v1 v2,
        value v1 ->
        value v2 ->
        <{ (v1,v2).snd }> --> v2

where "t '-->' t'" := (step t t').

Hint Constructors step : core.

Notation multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

Notation step_normal_form := (normal_form step).

Lemma value__normal : forall {t}, value t -> step_normal_form t.
Proof with eauto.
  intros t H; induction H; intros [t' ST]; inversion ST...
Qed.

(** Aside: As a reminder, putting curly braces around one ore more
    parameters in a lemma statement means that the parameters are to
    be _inferred_ from the remaining parameters.  For example, in the
    above lemma, Rocq can infer [t] from the provided [value t].
    This is entirely analogous to inference of type arguments in
    ordinary polymorphic functions, and it can remove clutter from
    explicit applications of the lemma. We use this style for most
    lemma statements in the remainder of this chapter. *)

(* ================================================================= *)
(** ** Typing *)

Definition context := partial_map ty.

Reserved Notation "Gamma '|--' t '\in' T" (at level 40,
                                          t custom stlc, T custom stlc at level 0).

Inductive has_type : context -> tm -> ty -> Prop :=
  (* Same as before: *)
  (* pure STLC *)
  | T_Var : forall Gamma x T1,
      Gamma x = Some T1 ->
      Gamma |-- x \in T1
  | T_Abs : forall Gamma x T1 T2 t1,
      (x |-> T2 ; Gamma) |-- t1 \in T1 ->
      Gamma |-- \x:T2, t1 \in (T2 -> T1)
  | T_App : forall T1 T2 Gamma t1 t2,
      Gamma |-- t1 \in (T2 -> T1) ->
      Gamma |-- t2 \in T2 ->
      Gamma |-- t1 t2 \in T1
  | T_True : forall Gamma,
       Gamma |-- true \in Bool
  | T_False : forall Gamma,
       Gamma |-- false \in Bool
  | T_If : forall t1 t2 t3 T1 Gamma,
      Gamma |-- t1 \in Bool ->
      Gamma |-- t2 \in T1 ->
      Gamma |-- t3 \in T1 ->
      Gamma |-- if t1 then t2 else t3 \in T1
  | T_Pair : forall Gamma t1 t2 T1 T2,
      Gamma |-- t1 \in T1 ->
      Gamma |-- t2 \in T2 ->
      Gamma |-- (t1, t2) \in (T1 * T2)
  | T_Fst : forall Gamma t0 T1 T2,
      Gamma |-- t0 \in (T1 * T2) ->
      Gamma |-- t0.fst \in T1
  | T_Snd : forall Gamma t0 T1 T2,
      Gamma |-- t0 \in (T1 * T2) ->
      Gamma |-- t0.snd \in T2

where "Gamma '|--' t '\in' T" := (has_type Gamma t T).

Hint Constructors has_type : core.

(* ================================================================= *)
(** ** Weakening *)

(** The weakening lemma is proved as in pure STLC. *)

Lemma weakening : forall {Gamma Gamma' t T},
     includedin Gamma Gamma' ->
     Gamma  |-- t \in T  ->
     Gamma' |-- t \in T.
Proof.
  intros Gamma Gamma' t T H Ht.
  generalize dependent Gamma'.
  induction Ht; eauto using includedin_update.
Qed.

Lemma weakening_empty : forall {Gamma t T},
     empty |-- t \in T  ->
     Gamma |-- t \in T.
Proof.
  intros Gamma t T.
  eapply weakening.
  discriminate.
Qed.

(* ================================================================= *)
(** ** Substitution *)

Lemma substitution_preserves_typing : forall Gamma x U t v T,
  (x |-> U ; Gamma) |-- t \in T ->
  empty |-- v \in U   ->
  Gamma |-- [x:=v]t \in T.
Proof with eauto.
  intros Gamma x U t v T Ht Hv.
  generalize dependent Gamma. generalize dependent T.
  induction t; intros T Gamma H;
  (* in each case, we'll want to get at the derivation of H *)
    inv H; simpl; eauto.
  - (* var *)
    rename s into y. destruct (eqb_spec x y); subst.
    + (* x=y *)
      rewrite update_eq in H2.
      injection H2 as H2; subst.
      apply weakening_empty. assumption.
    + (* x<>y *)
      apply T_Var. rewrite update_neq in H2; auto.
  - (* abs *)
    rename s into y, t into S.
    destruct (eqb_spec x y); subst; apply T_Abs.
    + (* x=y *)
      rewrite update_shadow in H5. assumption.
    + (* x<>y *)
      apply IHt.
      rewrite update_permute; auto.
Qed.

(* ================================================================= *)
(** ** Preservation *)

 Theorem preservation : forall {t t' T},
   empty |-- t \in T  ->
   t --> t'  ->
   empty |-- t' \in T.
Proof with eauto.
  intros t t' T HT. generalize dependent t'.
  remember empty as Gamma.
  induction HT;
    intros t' HE; subst; inversion HE; subst...
  - (* T_App *)
    inversion HE; subst...
    + (* ST_AppAbs *)
      apply substitution_preserves_typing with T2...
      inversion HT1...
  - (* T_Fst *)
    inversion HT...
  - (* T_Snd *)
    inversion HT...
Qed.

(* ================================================================= *)
(** ** Free Variables and Closed Terms *)

Inductive appears_free_in : string -> tm -> Prop :=
  | afi_var : forall (x : string),
      appears_free_in x <{ x }>
  | afi_app1 : forall x t1 t2,
      appears_free_in x t1 -> appears_free_in x <{ t1 t2 }>
  | afi_app2 : forall x t1 t2,
      appears_free_in x t2 -> appears_free_in x <{ t1 t2 }>
  | afi_abs : forall x y T11 t12,
        y <> x  ->
        appears_free_in x t12 ->
        appears_free_in x <{ \y : T11, t12 }>
  (* booleans *)
  | afi_if0 : forall x t0 t1 t2,
      appears_free_in x t0 ->
      appears_free_in x <{ if t0 then t1 else t2 }>
  | afi_if1 : forall x t0 t1 t2,
      appears_free_in x t1 ->
      appears_free_in x <{ if t0 then t1 else t2 }>
  | afi_if2 : forall x t0 t1 t2,
      appears_free_in x t2 ->
      appears_free_in x <{ if t0 then t1 else t2 }>
  (* pairs *)
  | afi_pair1 : forall x t1 t2,
      appears_free_in x t1 ->
      appears_free_in x <{ (t1, t2) }>
  | afi_pair2 : forall x t1 t2,
      appears_free_in x t2 ->
      appears_free_in x <{ (t1 , t2) }>
  | afi_fst : forall x t,
      appears_free_in x t ->
      appears_free_in x <{ t.fst }>
  | afi_snd : forall x t,
      appears_free_in x t ->
      appears_free_in x <{ t.snd }>.

Hint Constructors appears_free_in : core.

Definition closed (t:tm) :=
  forall x, ~ appears_free_in x t.

Lemma free_in_context : forall x {t T Gamma},
   appears_free_in x t ->
   Gamma |-- t \in T ->
   Gamma x <> None.
Proof with eauto.
  intros x t T Gamma Hafi Htyp.
  induction Htyp; inv Hafi...
  - (* T_Var *)
    rewrite H; intro X; inv X.
  - (* T_Abs *)
    pose proof (IHHtyp H4). rewrite update_neq in H; auto.
Qed.

Corollary typable_empty__closed : forall {t T},
    empty |-- t \in T  ->
    closed t.
Proof.
  intros. unfold closed. intros x H1.
  eapply free_in_context; eauto.
Qed.

(* ================================================================= *)
(** ** Determinism *)

(** To prove determinism, we introduce a helpful tactic that
      identifies cases in which a value takes a step and solves them
      using [value__normal].  *)

Ltac solve_by_value_nf :=
  match goal with | H : value ?v, H' : ?v --> ?v' |- _ =>
  exfalso; apply value__normal in H; eauto
  end.

Lemma step_deterministic :
   deterministic step.
Proof with eauto.
   unfold deterministic.
   intros t t' t'' E1 E2.
   generalize dependent t''.
   induction E1; intros t'' E2; inv E2;
   try solve_by_invert; try f_equal; try solve_by_value_nf; eauto.
   - inv E1; solve_by_value_nf.
   - inv H2; solve_by_value_nf.
   - inv E1; solve_by_value_nf.
   - inv H2; solve_by_value_nf.
Qed.

(* ################################################################# *)
(** * Normalization *)

(** Now for the actual normalization proof.

    Our goal is to prove that every well-typed term reduces to a
    normal form.  In the terminology of Chapter [Smallstep], we
    want to show [normalizing step]. In fact, it turns out to be
    convenient to prove something slightly stronger, namely that every
    well-typed term reduces to a _value_.  This follows from the
    weaker property via progress (why?) but otherwise we don't need
    progress, and we didn't bother re-proving it above.

    Here's the key definition: *)

Definition halts  (t:tm) : Prop :=  exists t', t -->* t' /\  value t'.

(** **** Exercise: 2 stars, standard (value_halts)

    Complete the proof of the this simple but useful fact: *)

Lemma value_halts : forall {v}, value v -> halts v.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, standard (step_preserves_halting)

    Another useful and suggestive fact: the property of halting is
    preserved by taking a reduction step _or_ "undoing" a reduction
    step. Complete the proof of this lemma.

    (The proof does not depend on the precise details of the step
    relation, but in one direction you will want to use
    [value__normal] and [step_deterministic]. The lemma might still
    be true for nondeterministic languages, but the proof would be
    harder!) *)

Lemma step_preserves_halting :
  forall {t t'}, (t --> t') -> (halts t <-> halts t').
Proof.
 intros t t' ST.  unfold halts.
 split.
 (* FILL IN HERE *) Admitted.
(** [] *)

(* ================================================================= *)
(** ** First Proof Attempt *)

(** The normalization proof is quite complicated, and it requires several
    different kinds of auxiliary mechanisms. To understand the motivation
    for these, it is instructive to look at some failed proof attempts.

    First of all, let's try to prove normalization directly using just
    induction on the typing judgments. We wouldn't expect this to
    succeed, but it is useful to see just where it goes wrong. *)

Theorem normalization_try1: forall {t T},
    empty |-- t \in T ->
    halts t.
Proof.
  intros t T HT.
  (* We want to induct over the typing hypothesis.  Recall that Rocq's
     induction tactic forces us to generalize to an arbitrary context
     [Gamma] first and keep track separately of the fact that [Gamma]
     is really always [empty]. *)
  remember empty as Gamma.
  induction HT; subst Gamma; intros.
  - (* Var *)
    (* This case is impossible because a bare variable is not typable
       in an empty enivonment. *)
    rewrite apply_empty in H.  inv H.
  - (* Abs *)
    (* This case is immediate because an abstraction is already a value *)
    apply value_halts.
    econstructor.
  - (* App *)
    unfold halts.
    (* This is the hard (actually impossible) case, but let's see how
       far we can get.  The only way that an application can reduce to
       a value is if we can somehow use the [ST_AppAbs] rule (otherwise
       the reduction sequence will get stuck while still at a term that
       is still an application, which is never a value). To make that
       rule applicable, [t1] must reduce to an abstraction term and
       [t2] must reduce to a value. The inductive hypotheses get us
       almost there... *)
    destruct (IHHT1 eq_refl) as [v1 [ST1 V1]].
    destruct (IHHT2 eq_refl) as [v2 [ST2 V2]].
    (* We still need to show that [v1] is an abstraction term, which
       we can do by repeated use of preservation and some reasoning
       about canonical forms. *)
    assert (HTV1: empty |-- v1 \in (T2 -> T1)).
    { clear - HT1 ST1. induction ST1; eauto using preservation. }
    assert (V1ABS: exists x, exists t, v1 = <{ \ x : T2 , t }>).
    { inv V1; inv HTV1; eauto. }
    destruct V1ABS as [x [t E]]. subst v1.
    (* Now we can show that reduction will indeed reach a use
       of [ST_AppAbs], by repeated use of [ST_App1] and [ST_App2]. *)
    assert (ST11: <{ t1 t2 }> -->* <{ (\ x : T2, t)  t2 }>).
    { clear - ST1. induction ST1; eauto. (* using [ST_App1] *) }
    assert (ST22: <{ (\ x: T2, t) t2 }> -->* <{ (\ x : T2, t) v2 }>).
    { clear - ST2. induction ST2; eauto. (* using [ST_App2] *) }
    assert (ST23: <{ t1 t2 }> -->* <{ (\ x : T2, t)  v2 }>).
    { eapply multi_trans; eauto. }
    assert (STT: <{ t1 t2 }> -->* <{ [ x:= v2 ] t }>).
    { eapply multi_trans; eauto.  (* using [ST_AppAbs] *) }
    (* But this is as far as we can go. The induction hypotheses don't
       tell us anything about [<{ [x := v2] t >}], because it is not a
       syntactic subterm of the original term. So we have no way to
       show that it ultimately reduces to a value, and we cannot do
       anything more with this case.  (For what it's worth, the remaining
       cases actually go through successfully.) *)
Abort.

(** ** The [N] relation

    The key issue in the normalization proof (as in many proofs by
    induction) is finding a strong enough induction hypothesis.  To
    this end, we begin by defining, for each type [T], a set [N_T] of
    closed terms of type [T], where N stands for "normalizing."
    We will specify these sets using a relation [N] and write
    [N T t] when [t] is in [N_T]. (The sets [N_T] are sometimes called
    _saturated sets_ or _reducibility candidates_.)

    Here is the definition of [N] for the base language:

    - [N bool t] iff [t] is a closed term of type [bool] and [t] halts
      in a value

    - [N (T1 -> T2) t] iff [t] is a closed term of type [T1 -> T2] and
      [t] halts in a value _and_, for any term [s] such that [N T1 s],
      we have [N T2 (t s)].

    This definition gives us the strengthened induction hypothesis that we
    need.  Our primary goal is to show that all _programs_ ---i.e., all
    closed terms of base type---halt.  But closed terms of base type can
    contain subterms of functional type, so we need to know something
    about these as well.  Moreover, it is not enough to know that these
    subterms halt, because the application of a normalized function to a
    normalized argument involves a substitution, which may enable more
    reduction steps.  So we need a stronger condition for terms of
    functional type: not only should they halt themselves, but, when
    applied to halting arguments, they should yield halting results.

    We also have to define the predicate for any other types in the
    language---in our case, products. (Even though the cases of the
    proof attempt above that deal with products are not problematic,
    once we choose to introduce [N] to handle functions properly,
    we have to consider its interaction with _all_ other types --
    think about products of functions, for example.) This part of
    the [N] definition, and the subsequent proof cases that involve it,
    are left as an exercise for you.

    The form of [N] is characteristic of the _logical relations_ proof
    technique. If we want to prove some property [P] of all closed
    terms of type [A], we proceed by proving, by induction on types,
    that all terms of type [A] _possess_  property [P], all terms of type
    [A->A] _preserve_ property [P], all terms of type [(A->A)->(A->A)]
    _preserve the property of preserving_ property [P], and so on.
    We do this by defining a family of predicates, indexed by types.
    For the base type [A], the predicate just enforces property [P].
    For functional types, it says that the function should map values
    satisfying the property at the input type to values satisfying the
    property at the output type.

    A warning about terminology: "logical relations" refers to
    relations that are "logical" in a very special sense;
    "type-indexed inductive relations" might be a better name. In
    general, one can study logical relations between two or more
    terms, but here we are only considering single terms, so we should
    more properly say _logical predicates_.  (Confusingly, since these
    predicates are indexed by types, they have the form of a relation
    between types and terms---but this is not a "logical" relation!)
    In addition to using the logical predicates technique to prove
    normalization, we will also apply it to give an alternative proof
    of type safety at the end of this chapter. See [Ahmed 2015] (in Bib.v)
    and [Mitchell 1996] (in Bib.v) for more details and applications of logical
    relations.

    When we come to formalize the definition of [N] in Rocq, we hit a
    problem.  The most obvious formulation would be as a parameterized
    Inductive proposition like this:

      Inductive N : ty -> tm -> Prop :=
      | N_bool : forall b t, empty |-- t \in <{ Bool }> ->
                      halts t ->
                      N <{ Bool }> t
      | N_arrow : forall T1 T2 t, empty |-- t \in <{ T1 -> T2 }> ->
                      halts t ->
                      (forall s, N T1 s -> N T2 <{t s}>) ->
                      N <{ T1 -> T2 }> t.

    Unfortunately, Rocq rejects this definition because it violates the
    _strict positivity requirement_ for inductive definitions, which says
    that the type being defined must not occur to the left of an arrow in
    the type of a constructor argument. Here, it is the third argument to
    [N_arrow], namely [(forall s, N T1 s -> N T2 <{t s}>)], and
    specifically the [N T1 s] part, that violates this rule.  (The
    outermost arrows separating the constructor arguments don't count when
    applying this rule; if they did, we could never have genuinely inductive
    properties at all!)  The reason for the rule is that types defined
    with non-positive recursion can be used to build non-terminating
    functions, which as we know would be a disaster for Rocq's logical
    soundness. Even though the relation we want in this case might be
    perfectly innocent, Rocq still rejects it because it fails the
    positivity test.

    Fortunately, it turns out that we _can_ define [N] using a
    [Fixpoint], as shown below. *)

(** **** Exercise: 3 stars, standard, especially useful (N_products)

    Fix the product case for this definition.

    Note 1: There is more than one valid way to do this; if your first
    attempt does not work out well when you come to the later proofs,
    try another!

    Note 2: you can skip this exercise until you are ready to start
    extending the later proofs. *)

Fixpoint N (T:ty) (t:tm) : Prop :=
  empty |-- t \in T /\ halts t /\
  (match T with
   | <{ Bool }>  => True
   | <{ T1 -> T2 }> => (forall s, N T1 s -> N T2 <{t s}> )

   (* ... edit the next line when dealing with products *)
   | <{ T1 * T2 }> => False    (* FILL IN HERE *)
   end).
(* Do not modify the following line: *)
Definition manual_grade_for_N_products : option (nat*string) := None.
(** [] *)

(** As immediate consequences of this definition, we have that every
    element of every set [N_T] halts in a value and is closed with
    type [T] :*)

Lemma N_halts : forall {T t}, N T t -> halts t.
Proof.
  intros.
  destruct T; unfold N in H; destruct H as [_ [H _]]; assumption.
Qed.

Lemma N_typable_empty : forall {T t}, N T t -> empty |-- t \in T.
Proof.
  intros.
  destruct T; unfold N in H; destruct H as [H _]; assumption.
Qed.

(* ================================================================= *)
(** **  Membership in [N_T] Is Invariant Under Reduction *)

(** There's a deeper property of [N_T] that will turn out to be
   essential for the normalization proof, namely that membership in
   [N_T] is _invariant_ under reduction.  We will need this property
   in both directions, i.e., both to show that a term in [N_T] stays
   in [N_T] when it takes a forward step, and to show that any term
   that ends up in [N_T] after a step must have been in [N_T] to
   begin with.  This means that, if any term in a chain of reductions
   is in [N_T], then so is every other (well-typed) term. We will use
   this to establish that well-typed abstraction terms are indeed in [N_T].

   This lemma is similar to the [step_preserves_halting] property we
   gave above, but the proof is more complicated because it makes
   fundamental use of the structure of types.  Each direction of the
   lemma proceeds by induction on the type [T].

   One requirement for staying in [N_T] is to stay in type [T]. In
   the forward direction, we get this from ordinary type
   preservation. The product case is left as an exercise for you. *)

(** **** Exercise: 3 stars, standard (step_preserves_N) *)

Lemma step_preserves_N: forall {T t t'}, (t --> t') -> N T t -> N T t'.
Proof.
 induction T;  intros t t' E Nt; simpl in Nt |- *;
               destruct Nt as [typable_empty_t [halts_t NN]].
  - (* Bool *)
    split;[|split].
    + eapply preservation; eauto.
    + apply (step_preserves_halting E); eauto.
    + auto.
  - (* Arrow *)
    split;[|split].
    + eapply preservation; eauto.
    + apply (step_preserves_halting E); eauto.
    + intros.
      eapply IHT2.
      * apply ST_App1. apply E.
      * apply NN; auto.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** The generalization to multiple steps is trivial: *)

Lemma multistep_preserves_N : forall {T t t'},
  (t -->* t') -> N T t -> N T t'.
Proof.
  intros T t t' STM; induction STM; intros.
  - assumption.
  - apply IHSTM. eapply step_preserves_N.
    + apply H.
    + assumption.
Qed.

(** In the reverse direction, we must add the fact that [t] has type
   [T] _before_ stepping as an additional hypothesis, because
   _subject expansion_ does not hold for this language (see [StlcProp]). *)

(** **** Exercise: 4 stars, standard, especially useful (step_preserves_N') *)

Lemma step_preserves_N' : forall {T t t'},
  empty |-- t \in T -> (t --> t') -> N T t' -> N T t.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

Lemma multistep_preserves_N' : forall {T t} t',
  empty |-- t \in T -> (t -->* t') -> N T t' -> N T t.
Proof.
  intros T t t' HT STM.
  induction STM; intros.
    assumption.
    eapply step_preserves_N'.  assumption. apply H. apply IHSTM.
    eapply preservation;  eauto. auto.
Qed.

(* ================================================================= *)
(** ** Second Proof Attempt *)

(** Given the [N_halts] lemma, the task of proving normalization
    reduces to proving that every well-typed closed term of type [T]
    is a member of [N_T]. So let's attempt to prove that fact, again
    by induction on the typing derivation.  We'll ultimately get stuck
    again, but the failed proof sketch will again be instructive.

    Unlike our previous attempt, the difficult part of this proof will
    be in the [Abs] case, while the [App] case will fall out directly
    from the definition of [N_T].
*)

Lemma typable_N_try1: forall t T,
    empty |-- t \in T ->
    N T t.
Proof.
  intros t T HT.
  remember empty as Gamma.  (* as before, we must do this to induct
                               over HT. *)
  induction HT; subst Gamma; intros.
  - (* Var *)
    (* This case is again impossible because [t] is closed. *)
    rewrite apply_empty in H.  inv H.
  - (* Abs *)
    simpl; split; [| split].
    + econstructor; eauto.
    + eapply value_halts. econstructor.
    + intros s NS.
      (* This is now the hard (sub)case.
         Taking stock of what we know, we first observe that
         [s] reduces to a value [v] *)
      destruct (N_halts NS) as [v [STV V]].
      (* Moreover, using the invariance of [N] under reduction,
         we know that [v] is in [N T2]. *)
      assert (NV: N T2 v) by (eapply multistep_preserves_N; eauto).
      (* Also, the application in the goal reduces to a substitution. *)
      assert (ST: <{ (\ x : T2, t1) s }> -->* <{ [x := v] t1 }>).
      { eapply multi_trans with <{ (\ x : T2, t1) v }>.
        - clear - STV. induction STV; eauto. (* using ST_App2 *)
        - eapply multi_trans.
          + eapply multi_R; eapply ST_AppAbs; auto.
          + eapply multi_refl.
      }
      (* And the application in the gaol is well-typed *)
      assert (empty |-- (\x : T2, t1) s \in T1).
      { econstructor.
        - econstructor; eauto.
        - eapply N_typable_empty; eauto.
      }
      (* Now we can use the the invariance of [N] under
         reverse steps to simplify the goal. *)
      eapply multistep_preserves_N'; eauto.
      (* Alas, we have no way to prove this goal!  If we knew that
         [t1] was in [N], the goal would be plausible: substituting
         an N term into a N body "should" give a N result. And
         since [t1] is a subterm of the original application, we might
         hope that the induction hypothesis would tell us something
         useful about it.  But in fact, the induction hypothesis
         [IHHT] is completely useless, since its assumption
         [((x) |-> T2) = empty] is false!  Moreover, the conclusion
         [N T1 t1] of [IHHT] doesn't make sense anyway, since all
         terms in [N] are closed but [t1] may contain [x] free.
         All this suggests that we need an even more general induction
         hypothesis that talks about open terms. *)
      admit. (* impossible! *)
  - (* App *)
    (* at least this case is now immediate, as we expected *)
    eapply IHHT1; eauto.
Abort.

(* ================================================================= *)
(** ** Closing Multi-substitutions and Instantiations *)

(** The upshot of this failed proof attempt is that we need another
    generalization to state and prove [typable_N] properly.  To
    recap: Since we are arguing by induction, the demonstration that a
    term [\x : T1, t2] belongs to [N_(T1->T2)] should involve
    applying the induction hypothesis to show that [t2] belongs to
    [N_T2].  But [N_T2] is defined to be a set of _closed_
    terms, while [t2] may contain [x] free, so this does not make
    sense.

    We resolve this problem by using a standard trick to suitably
    generalize the induction hypothesis: instead of proving a
    statement involving a closed term, we generalize it to cover all
    closed _instances_ of an open term [t] that satisfy N.
    Informally, the statement of the lemma will look like this:

    If [x1:T1,..xn:Tn |-- t : T] and [v1,...,vn] are values such that
    [N T1 v1], [N T2 v2], ..., [N Tn vn], then [N T
    ([x1:=v1][x2:=v2]...[xn:=vn]t)].

    The proof will proceed by induction on the typing derivation
    [x1:T1,..xn:Tn |-- t : T]; the most interesting case will be the
    one for abstraction.

    However, before we can proceed to formalize the statement and
    proof of the lemma, we'll need to take a detour to build some
    (rather tedious) machinery to deal with the fact that we are
    performing _multiple_ substitutions on term [t] and _multiple_
    extensions of the typing context.  In particular, we must be
    precise about the order in which the substitutions occur and how
    they act on each other.  Often these details are simply elided in
    informal paper proofs, but of course Rocq won't let us do
    that. Since here we are substituting closed terms, we don't need
    to worry about how one substitution might affect the term put in
    place by another.  But we still do need to worry about the _order_
    of substitutions, because it is quite possible for the same
    variable name to appear multiple times among the [x1,...xn] with
    different associated [vi] and [Ti].

    To make everything precise, we will assume that typing context
    updates are performed from right to left, and multiple term
    substitutions are performed from left to right.  To see that this
    is consistent, suppose we have a type assignment written as
    [...,y:Bool,...,y:Bool*Bool,...]  and a corresponding term
    substitution written as [...[y:=true]...[y:=(false,false)]...t].
    Since contexts are extended from right to left, the binding
    [y:Bool] hides the binding [y:Bool*Bool]; since substitutions are
    performed left to right, we do the substitution [y:=true] first,
    so the substitution [y:=(false,false)] has no effect. Substitution
    thus correctly preserves the type of the term.

    With these points in mind, the following definitions should make
    sense.

    A _multi-substitution_ is the result of applying a list of
    substitutions, which we call an _environment_. *)

Definition env := list (string * tm).

Fixpoint msubst (ss:env) (t:tm) : tm :=
match ss with
| nil => t
| ((x,s)::ss') => msubst ss' <{ [x:=s]t }>
end.

(** We need similar machinery to talk about repeated extension of a
    typing context using a list of (variable, type) pairs, which we
    call a _type assignment_. This is a more concrete representation
    of typing contexts than the partial maps (developed in
    [Maps]) that we have used up to this point. Representing
    maps as functions is appealingly simple for many purposes, but
    it has one major drawback: we cannot enumerate the domain of a
    map or perform induction over it.  We _can_ do induction over
    type assignments, and this turns out to be very useful. *)

Definition tass := list (string * ty).

Fixpoint mupdate (Gamma : context) (xts : tass) : context :=
  match xts with
  | nil => Gamma
  | ((x,v)::xts') => update (mupdate Gamma xts') x v
  end.

(** A type assignment is readily converted into a typing context. *)

Definition tass_context (c:tass) := mupdate empty c.
Hint Unfold tass_context : core.

(** Finally, we describe the combination of a type assignment and a
    value environment that have the same domain and where
    corresponding type and value elements are related. We call this an
    _instantiation_.  We parameterize the definition over an arbitrary
    type-indexed predicate R over closed terms, since many properties
    of instantiations don't depend on the specific choice of R. (This will
    allow us to reuse these definitions and properties on other logical
    predicates besides N later in the chapter.) *)

Definition R_closed (R: ty -> tm -> Prop) :=
  forall T t, R T t -> closed t.
Hint Unfold R_closed : core.

Inductive instantiation (R: ty -> tm -> Prop)  (RC: R_closed R) :
                                            tass -> env -> Prop :=
| V_nil :
    instantiation R RC nil nil
| V_cons : forall x T v c e,
    value v -> R T v ->
    instantiation R RC c e ->
    instantiation R RC ((x,T)::c) ((x,v)::e).
Hint Constructors instantiation: core.

(** We now proceed to prove various properties of these definitions. *)

(* ----------------------------------------------------------------- *)
(** *** More Substitution Facts *)

(** First we need some additional lemmas on (ordinary)
    substitution. These will ultimately support lemmas about how
    single substitutions and multi-substitutions commute. *)

(** **** Exercise: 3 stars, standard, optional (vacuous_substitution) *)

(** Show that substituting for a variable which doesn't appear (free) has
    no effect. *)

Lemma vacuous_substitution : forall {t x},
     ~ appears_free_in x t  ->
     forall t', <{ [x:=t']t }> = t.
Proof with eauto.
  induction t; intros; simpl...
  (* FILL IN HERE *) Admitted.
(** [] *)

(** Substituting over a closed term has no effect. *)

Lemma subst_closed: forall {t},
     closed t  ->
     forall x t', <{ [x:=t']t }> = t.
Proof.
  intros. apply vacuous_substitution; auto.
Qed.

(** **** Exercise: 3 stars, standard, optional (subst_not_afi) *)

(** Show that after substituting for a variable (with a closed term),
    that variable is no longer free. Proof is by induction on [t]. *)

Lemma subst_not_afi : forall {t x v},
    closed v ->  ~ appears_free_in x <{ [x:=v]t }>.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** Substituting for the same variable twice has no effect. *)

Lemma duplicate_subst : forall {t' x t v},
  closed v -> <{ [x:=t]([x:=v]t') }> = <{ [x:=v]t' }>.
Proof.
  intros.
  eapply vacuous_substitution.
  apply subst_not_afi; auto.
Qed.

(** **** Exercise: 3 stars, standard (swap_subst) *)

(** Changing the order of two (closed) substitutions for different
    variables has no effect. Complete the following proof. *)

Lemma swap_subst : forall {t x x1 v v1},
    x <> x1 ->
    closed v -> closed v1 ->
    <{ [x1:=v1]([x:=v]t) }> = <{ [x:=v]([x1:=v1]t) }>.
Proof with eauto.
 induction t; intros; simpl.
  - (* var *)
   destruct (eqb_spec x s); destruct (eqb_spec x1 s).
   + subst. exfalso...
   + subst. simpl. rewrite eqb_refl. apply subst_closed...
   + subst. simpl. rewrite eqb_refl. symmetry. apply subst_closed...
   + simpl. rewrite <- eqb_neq in n; rewrite n.
     rewrite <- eqb_neq in n0; rewrite n0...
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ----------------------------------------------------------------- *)
(** *** Properties of Multi-Substitutions *)

(** We can distribute [msubst] over [subst] provided that all
    substituted terms are closed. But we need to adjust the
    environment on the right-hand side to account for the possibility
    that the multi-substitution has duplicate variable names. *)

Fixpoint closed_env (e:env) :=
  match e with
  | nil => True
  | (_,t)::e' => closed t /\ closed_env e'
  end.

Fixpoint remove (n:string) (e: env) : env :=
  match e with
    | nil => nil
    | ((n',x)::nxs') =>
        if n' =? n then remove n nxs'
        else (n',x)::(remove n nxs')
  end.

(** **** Exercise: 3 stars, standard, especially useful (msubst_subst)

    Complete the following proof by induction on [e]. Hint: Use the lemmas
    about substitution proved above! *)

Lemma msubst_subst: forall {e x v t},
    closed v ->
    closed_env e ->
    msubst e <{ [x:=v]t }> = <{ [x:=v]  { msubst (remove x e) t }  }> .
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** Multi-substituting into a closed term has no effect. *)
Lemma msubst_closed: forall {t},
    closed t ->
    forall {ss}, msubst ss t = t.
Proof.
  induction ss.
  - reflexivity.
  - destruct a. simpl. rewrite subst_closed; assumption.
Qed.

(** Next come a series of easy lemmas characterizing how [msubst]
    distributes over each term form *)

Lemma msubst_abs: forall {ss x T t},
  msubst ss <{ \ x : T, t }> = <{ \x : T, {msubst (remove x ss) t} }>.
Proof.
  induction ss; intros.
  - reflexivity.
  - destruct a. simpl. destruct (s =? x); simpl; auto.
Qed.

(** **** Exercise: 2 stars, standard, especially useful (msubst_app) *)

Lemma msubst_app : forall {ss t1 t2},
    msubst ss <{ t1 t2 }> = <{ {msubst ss t1} ({msubst ss t2}) }>.
Proof.
(* FILL IN HERE *) Admitted.
(** [] *)

(** To complete the product cases of the main lemma below, you'll want
    similar results on all the other term constructors; the proofs
    are extremely similar to [msubst_app]. *)


(* ----------------------------------------------------------------- *)
(** *** General Properties of Instantiations *)

(** These don't depend on the underlying predicate R, and their proofs
    are straightforward. *)

(** **** Exercise: 3 stars, standard, especially useful (instantiation_msubst)

    Applying the multi-substitution from an instantiation of R
    to a variable of type [T] yields a term [t] such that R T t.  *)

Lemma instantiation_msubst : forall {R RC c e},
    instantiation R RC c e ->
    forall x T,
      tass_context c x = Some T ->
      R T (msubst e x).
Proof.
  intros R RC c e V.
  induction V; intros x' T' G.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard (instantiation_env_closed)

    The environment of an instantiation is always closed. *)

Lemma instantiation_env_closed : forall {R RC c e},
    instantiation R RC c e ->
    closed_env e.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ================================================================= *)
(** **  Properties of N Instantiations *)

(** The key lemma about preservation of typing under substitution can
    be lifted to N-specific instantiations. *)

Lemma N_closed: R_closed N.
Proof.
  unfold R_closed. intros.
  eapply typable_empty__closed.
  eapply N_typable_empty; eauto.
Qed.

(** **** Exercise: 3 stars, standard (N_instantiation_preserves_typing) *)

Lemma N_instantiation_preserves_typing : forall {c e},
     instantiation N N_closed c e ->
     forall Gamma t S, (mupdate Gamma c) |-- t \in S ->
     Gamma |-- { (msubst e t) } \in S.
Proof.
    (* FILL IN HERE *) Admitted.
(** [] *)

(* ================================================================= *)
(** ** Congruence Lemmas on Multistep *)

(** **** Exercise: 2 stars, standard, especially useful (multistep_App2) *)

(** If we can reduce the right-hand side of an application, we can
    reduce the whole application. *)

Lemma multistep_App2 : forall {v t t'},
  value v -> (t -->* t') -> <{ v t }> -->* <{ v t' }>.
Proof.
(* FILL IN HERE *) Admitted.
(** [] *)

(** To complete the conditional and product cases of the main lemma below,
    you'll want similar lemmas; add them as the demand arises (the proofs
    are essentially identical). *)


(* ================================================================= *)
(** ** Completed Proof using N *)

(** **** Exercise: 5 stars, standard, especially useful (typable_N) *)

(** At long last, the main lemma! The conditional and product cases are
    left for you. *)

Lemma typable_N : forall c {t T},
    tass_context c |-- t \in T ->
    forall e,
    instantiation N N_closed c e ->
    N T (msubst e t).
Proof.
  intros c t T HT.
  (* We need to generalize the form of the
     hypothesis a bit before invoking induction *)
  remember (tass_context c) as Gamma.
  generalize dependent c.
  induction HT; intros c HeqGamma e V;
    try rewrite HeqGamma in *; clear HeqGamma.
  - (* T_Var *)
    eapply instantiation_msubst; eauto.
  - (* T_Abs *)
    simpl.
    split;[|split].
    + eapply N_instantiation_preserves_typing; eauto.
    + rewrite msubst_abs. apply value_halts. apply v_abs.
    + intros.
      destruct (N_halts H) as [v [P Q]].
      pose proof (multistep_preserves_N P H).
      apply multistep_preserves_N' with (msubst ((x,v)::e) t1).
      * eapply T_App.
        -- eapply N_instantiation_preserves_typing; eauto.
        -- eapply N_typable_empty; auto.
      * rewrite msubst_abs.
        eapply multi_trans.
        -- eapply multistep_App2; eauto.
        -- eapply multi_R.
           simpl. rewrite msubst_subst.
           ++ eapply ST_AppAbs; eauto.
           ++ eapply typable_empty__closed.
              apply (N_typable_empty H0).
           ++ eapply instantiation_env_closed; eauto.
     * eapply (IHHT ((x,T2)::c)).
       -- auto.
       -- constructor; auto.

  - (* T_App *)
    rewrite msubst_app.
    edestruct IHHT1 as [_ [_ P1]]; eauto.  fold N in P1.
    apply P1. eapply IHHT2; auto.

  (* FILL IN HERE *) Admitted.
(** [] *)

(** And the final theorem: *)

Theorem normalization : forall t T, empty |-- t \in T -> halts t.
Proof.
  intros.
  replace t with (msubst nil t) by reflexivity.
  eapply N_halts.
  apply (typable_N nil); eauto.
Qed.

(* ################################################################# *)
(** * Type Safety via a Logical Predicate (Optional) *)

(** In this section, we further illustrate the proof technique of
    logical predicates by developing a proof of type safety for the
    simply typed lambda calculus which works rather differently than
    the standard one based on progress and preservation that we
    studied in [StlcProp]. In this alternative approach, we
    define a notion of _semantic_ type safety as a logical predicate
    over terms that trivially implies the property that evaluation
    cannot get stuck. Then we prove that syntactically well-typed
    terms obey this predicate.

    The overall shape of this proof will be similar to that of the
    normalization proof. The logical predicate definition will again
    give us a stronger induction hypothesis for reasoning about
    functions (and booleans and pairs), although the technical details
    will be a bit different. To deal with open terms, we will be able
    to re-use the machinery of multi-substitutions and instantiations
    that we developed earlier in this chapter. Studying and
    completing the proof should give you an deeper understanding of
    how logical predicates (and, more generally, logical relations)
    can be used.

    In addition, this proof provides an introduction to the idea of
    "semantic typing," Semantic typing allows us to type many terms
    that don't have valid syntactic types; we'll see some examples
    below. And while the semantic safety proof for STLC is
    undoubtedly more complicated than the standard syntactic
    one using progress and preservation, it may generalize better to
    complex real-world languages, such as Rust, that support
    encapsulated _unsafe_ computations (although these are beyond
    the scope of this chapter). *)

(** We begin by giving a compact characterization of what it means for
    a term to be _safe_, namely that it never gets stuck. *)

Definition safe  (t:tm) : Prop :=
  forall t', t -->* t' -> step_normal_form t' -> value t'.

(* ================================================================= *)
(** ** First Proof Attempt *)

(** Our ultimate goal is to show that every syntactically well-typed
    term is safe in this sense. We know this can be done by
    alternating uses of progress and preservation, but it is once again
    instructive to attempt a direct inductive proof and see where the
    argument fails to go through.

    Actually, we'll temporarily assume we have separately proved
    preservation, so really this theorem can be viewed as an
    alternative to the progress lemma which deals with entire
    normalizing sequences of steps rather than just a single step at a
    time. *)

Theorem type_soundness_try1: forall t T, empty |-- t \in T -> safe t.
Proof.
  remember empty as Gamma. (* As before, we must do this to induct
                              over HT. *)
  intros t T HT.
  unfold safe.
  induction HT; subst Gamma; intros t' ST.
  - (* T_Var *)
    (* This case is impossible because [t] is typable in an empty
       environment. *)
    inv H.
  - (* T_Abs *)
    (* This case is immediate because [t] is already a value (and
       cannot step further). *)
    inv ST.
    + econstructor.
    + inv H.
  - (* T_App *)
    intros NFt'.
    (* This is the hard case. The only way [t'] can be a value is if
       the [ST] sequence somehow uses the [ST_AppAbs] rule (otherwise it
       gets stuck at some kind of application term, which is never a
       value).  To make that rule applicable, [t1] must reduce to an
       abstraction term and [t2] must reduce to a value.  With some effort,
       we can establish these facts... *)
    (* First, we can analyze [ST] to see that [t1] must step to a
       normal form somewhere along the way to [t'] (by zero or more
       uses of [ST_App1]). *)
    assert (N1: exists t1', t1 -->* t1'
                            /\ step_normal_form t1'
                            /\ <{ t1' t2 }> -->* t').
    { admit. (* this is provable by induction on [ST] *) }
    destruct N1 as [t1' [ST1 [NF1 RST1]]].
    (* The first induction hypothesis says [t1'] must be a value. *)
    assert (V1: value t1') by (eapply IHHT1; eauto).
    (* We can now use preservation to show that [t1'] has type [Ty_Arrow]. *)
    assert (HT1': empty |-- t1' \in (T2 -> T1)).
    { clear - HT1 ST1. induction ST1; eauto using preservation. }
    (* And a value of type [Ty_Arrow] must be an abstraction term. *)
    inversion HT1'; subst; try (inv V1; fail).
    (* Now, analyzing [RST1], we can see that [t2] must step to a
       normal form somewhere along the way to [t1'] (by zero or more
       uses of [ST_App2]). *)
    assert (N2: exists t2', t2 -->* t2'
                            /\ step_normal_form t2'
                             /\ <{ (\ x: T2, t0) t2' }> -->* t').
    { admit. (* this is provable by induction on [RST1] *) }
    destruct N2 as [t2' [ST2 [NF2 RST2]]].
    (* And by the second induction hypothesis, [t2'] must be a value. *)
    assert (V2: value t2') by (eapply IHHT2; eauto).
    (* Now we finally have enough facts to apply the [St_AppAbs]
       rule. *)
    assert (ONE:  <{ (\ x: T2, t0) t2' }> --> <{ [x := t2'] t0 }>).
    { apply ST_AppAbs; eauto. }
    (* But unfortunately, we have no induction hypothesis that tells
       us anything about the behavior of [t0], much less [[x := t2'] t0]
       (which is not even a syntactic subterm of our original [t]).
       So we cannot proceed any further with this case.  (The
       remaining cases actually go through successfully.) *)
Abort.

(* ================================================================= *)
(** ** [St] and [Sv] Predicates *)

(** Examining this failed attempt, we can see the need for a stronger
    induction hypothesis that talks about the behavior of the _bodies_
    of abstractions (after substitution of a suitable argument). This
    is similar to what we did in the normalization proof, and we will
    again use a logical predicate for this purpose.

    As before, our logical predicate [St] will be a type-indexed
    predicate over closed terms.  Any term in [St] should be safe, but
    moreover, if the term evaluates to an abstraction, the result of
    applying that abstraction (to a safe value) should also be safe,
    and so on.  (Similar considerations apply to pairs; as before, we
    leave this case to you.)  This leads us to invent another logical
    predicate [Sv] to characterize these "strongly safe" values.
    The definitions of [St] and [Sv] need to be mutually recursive,
    so we would want to write them like this:

 [[
    Fixpoint St (T:ty) (t: tm) : Prop :=
       forall t', t -->* t' -> step_normal_form t' -> Sv T t'
    with Sv (T:ty) (t:tm) {struct T}  : Prop :=
       closed t /\
          (match T with
           | <{ Bool }> => (t = <{ true }> \/ t = <{ false }> )
           | <{ T1 -> T2 }> =>
                  exists x t2,
                      t = <{ \x:T1,t2 }> /\
                      forall s, Sv T1 s -> St T2 <{ [x:=s] t2 }>
           | <{ T1 * T2 }> => ... (* left for you to fill in *)
           end).

    Unfortunately, Rocq rejects these definitions because it cannot
    convince itself that they are they are structurally recursive (on
    [T]) as we have claimed. To get around that problem, we use a
    standard trick of inlining the definition of [St] into [Sv],
    obtaining the definitions below.  *)

(** **** Exercise: 3 stars, standard, especially useful (Sv_products)

    Fix the product case for this definition. Note: you can skip this
    exercise until you are ready to start extending the later proofs.
*)

Fixpoint Sv (T:ty) (t:tm) {struct T}  : Prop :=
  closed t /\
    (match T with
     | <{ Bool }> => (t = <{ true }> \/ t = <{ false }> )
     | <{ T1 -> T2 }> =>
         exists x t2, t = <{ \x:T1,t2 }> /\
                 (forall s, Sv T1 s ->
                        (forall t', <{ [x := s] t2 }> -->* t' ->
                               step_normal_form t' ->
                               Sv T2 t'))

   (* ... edit the next line when dealing with products *)
   | <{ T1 * T2 }> => False    (* FILL IN HERE *)
     end).
(* Do not modify the following line: *)
Definition manual_grade_for_Sv_products : option (nat*string) := None.
(** [] *)

Definition St (T:ty) (t: tm) : Prop :=
  forall t', t -->* t' -> step_normal_form t' -> Sv T t'.

(** [Sv T] and [St T] are sometimes called the "value interpretation"
    and "term (or expression) interpretation" of type [T]. They
    characterize the values and terms that _behave like_ members of
    that type should.

    Note that these predicates do _not_ require (syntactic) well-typedness.
    This is unusual for a logical predicates proof, but it is appropriate
    here, since after all we are trying to prove type safety from new
    principles. If we did require well-typedness, we could still make the
    proof go through, but only with the help of the
    [substitution_preserves_typing] lemma, which is the main result needed
    to prove preservation. With the approach we take here, we don't need
    either progress or preservation.

    We do, however, explicitly require that [Sv] contain only closed
    terms. (The proof works if we impose the same requirement on [St], but
    it brings no benefit.)

    We start with a few simple consequences of these definitions: *)

(** **** Exercise: 2 stars, standard (Sv_val)

    Once you have defined the product case for [Sv], complete
    this proof that terms in [Sv] are values. *)

Lemma Sv_val : forall {T t}, Sv T t -> value t.
Proof.
  induction T; intros.
  - inv H. destruct H1; subst; auto.
  - inv H. destruct H1  as [x [t2 [E _]]]; subst; auto.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** Terms in [Sv] are also in [St]. *)

Lemma Sv_St : forall {T t}, Sv T t -> St T t.
Proof.
  intros.
  unfold St.
  intros. pose proof (Sv_val H). eapply value__normal in H2.
  inv H0; auto.
  exfalso; eapply H2. eexists;  eauto.
Qed.

(** We have successfully captured safety in [St]. (This is sometimes
    called an "adequacy" theorem for [St].) *)

Lemma St_safe: forall {T t}, St T t -> safe t.
Proof.
  intros.
  unfold safe.
  intros.
  unfold St in H.
  eapply Sv_val; eauto.
Qed.

(** As in the normalization proof, we will need to deal with open
    terms by defining closing substitutions. The instantiation
    machinery works for [Sv] just as it did for [N]. *)

Lemma Sv_closed: R_closed Sv.
Proof.
  unfold R_closed.
  intros. destruct T; destruct H; auto.
Qed.

(* ================================================================= *)
(** ** Semantic Typing *)

(** To state our main result succinctly, we define the notion of
    "semantic type" for arbitrary open terms, written [Gamma |= T \in
    t].  Our main goal will then be to prove that [Gamma |- T \in t ->
    Gamma |= T \in t]. *)

Definition has_semantic_type (Gamma: context) (t:tm) (T:ty) : Prop :=
  forall (c:tass), Gamma = tass_context c ->
              forall (e:env), instantiation Sv Sv_closed c e ->
                         St T (msubst e t).

Notation "Gamma '|==' t '\in' T" := (has_semantic_type Gamma t T) (at level 40,
                                          t custom stlc, T custom stlc at level 0).

(* ----------------------------------------------------------------- *)
(** *** Semantic Typing Examples *)

(** Before proceeding to the proof that syntactic typing implies
    semantic typing, we might stop to wonder whether the converse of
    this also holds, i.e. whether syntactic and semantic typing are
    exactly the same thing. It turns out they are not, as we
    illustrate by giving a couple of examples of terms that are not
    syntactically well-typed, but which "behave" correctly and are
    therefore semantically well-typed, *)

Module Examples.

  (** First a handy lemma. *)

  Lemma empty_context : forall {R RC c e},
      instantiation R RC c e ->
      tass_context c = empty ->
      e = nil.
  Proof.
    intros.
    destruct c.
    - inv H. auto.
    - exfalso.
      unfold tass_context in H0.
      simpl in H0. destruct p.
      assert (((s) |-> t; (mupdate empty c) s) = empty s) by (rewrite H0; auto).
      rewrite update_eq in H1.  rewrite apply_empty in H1.  inv H1.
  Qed.

  (** In the first example, the two arms of the conditional have
      different types, but the expression reduces to a [Bool] value. *)

  Remark hst_ex1 : empty |== <{ if true then false else (false,false) }> \in Ty_Bool.
  Proof.
    unfold has_semantic_type.
    intros.
    erewrite empty_context; eauto.
    simpl.
    unfold St.
    intros.
    inv H1.
    + unfold step_normal_form in H2. exfalso; apply H2; eauto.
    + inv H3.
      * inv H4.
        -- unfold Sv.  split.
           ++ unfold closed. intros. intro. inv H1.
           ++ right; auto.
        -- inv H1.
      * inv H8.
  Qed.

  (** In the second example, the term doesn't reduce to a value at all
      (in fact, it reduces to itself!).  So not only is it
      syntactically ill-typed; the normalization theorem tells us that
      there is no possible choice of types on the variable bindings
      that would _make_ it syntactically well-typed. But we can give
      it any semantic type we like. *)

  Definition x : string := "x".
  Hint Unfold x : core.
  Remark hst_ex2: forall T, empty |== <{ (\ x : Bool, (x x)) (\x : Bool, (x x)) }> \in T.
  Proof.
    unfold has_semantic_type.
    intros.
    erewrite empty_context; eauto.
    simpl.
    unfold St.
    intros.
    remember <{ (\ x : Bool, (x x)) (\ x : Bool, (x x)) }> as t.
    induction H1.
    + subst x0. unfold step_normal_form in H2. exfalso; apply H2. eexists.  eauto.
    + subst x0. inv H1.
      * simpl in H3. simpl <{ [x := \ x : Bool, x x] x x }>  in IHmulti.
        eauto.
      * inv H7.
      * inv H8.
  Qed.

End Examples.

(* ================================================================= *)
(** ** More Properties of Substitution and Instantiation *)

(** Now we turn to the syntactic --> semantic proof. As usual, we start
    with a few technical preliminaries.

    First, we will want an additional basic fact about instantiations
    (over any relational predicate).  Given an instantiation relating
    context [Gamma] and environment [e], if [t] is well-typed under
    [Gamma], applying [msubst e] to [t] yields a closed term. *)

(** **** Exercise: 4 stars, standard (instantiation_closes) *)

Lemma instantiation_closes: forall R RC c e,
    instantiation R RC c e ->
    forall t T, tass_context c |-- t \in T ->
    closed (msubst e t).
Proof.
  (* Hint: this proof is fairly straightforward once you have found
     a suitable generalization of the induction hypothesis. *)
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ================================================================= *)
(** ** Inversion lemmas about multistepping *)

(** The other preliminaries are inspired by the [admit]s that appeared
    in our initial, unsuccessful attempt to prove safety. We need a
    family of lemmas that invert the normalizing multistep
    relation. These are straightforward but rather tedious.

    First, some basic facts about decidability of values and stepping.
    Note that in classical logic these lemmas follow directly from the
    law of excluded middle, but in Rocq's constructive logic setting
    we have to prove them.  For the second lemma, the constructive
    proof gives us a useful result term [t']. Think about using
    a custom tactic to help automate this proof. *)

Lemma value_dec : forall t, value t \/ ~ value t.
Proof.
  induction t; try (right; intro X; inv X; fail); try (left; auto; fail).
  destruct IHt1; destruct IHt2;
    try (right; intro X; inv X; contradiction);
    try (left; auto; fail).
Qed.

(** **** Exercise: 3 stars, standard, especially useful (nf_dec) *)

Lemma nf_dec : forall t, step_normal_form t \/ exists t', t --> t'.
Proof with eauto.
(* FILL IN HERE *) Admitted.
(** [] *)

(** Now we can proceed to the inversion lemmas themselves. All the
    proofs are extremely similar. *)

Lemma norm_App1 : forall {t1 t2 t'},
    <{ t1 t2 }> -->* t' -> step_normal_form t' ->
    exists t1', t1 -->* t1'
                /\ step_normal_form t1'
                /\ <{ t1' t2 }> -->* t'.
Proof.
  intros until 1.
  remember <{ t1 t2 }> as t.
  generalize dependent t1.
  induction H; intros; subst x.
  - exists t1.
    split; [|split]; eauto.
    intros [t' P]; eauto.
  - destruct (nf_dec t1) as [P|[t1' P]]; eauto.
    edestruct (IHmulti t1') as [t1'' [P1 [P2 P3]]]; eauto.
    eapply step_deterministic; eauto.
Qed.

(** **** Exercise: 2 stars, standard (norm_App2) *)

Lemma norm_App2 : forall {v1 t2 t'},
    <{ v1 t2 }> -->* t' -> value v1 ->
    step_normal_form t' ->
    exists t2', t2 -->* t2'
                /\ step_normal_form t2'
                /\ <{ v1 t2' }> -->* t'.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** Add similar lemmas for other term forms as needed in the main proof below. *)

(* ================================================================= *)
(** ** Syntactic Typing implies Semantic Typing *)

(** **** Exercise: 5 stars, standard, especially useful (syntactic_type_semantic)

    Finally we reach the main lemma. Again, the conditional and product
    cases are left for you. *)

Lemma syntactic_type_semantic : forall {Gamma t T},
    Gamma |-- t \in T ->
    Gamma |== t \in T.
Proof.
  unfold has_semantic_type.
  intros Gamma t T HT.
  induction HT; intros c E e V; try rewrite E in *; clear E.

  - (* T_Var *)
    eapply Sv_St.
    eapply instantiation_msubst; eauto.

  - (* T_Abs *)
    unfold St.
    rewrite msubst_abs.
    intros.
    inv H; [| inv H1].
    unfold Sv; fold Sv; split.
    + rewrite <- msubst_abs. eapply instantiation_closes; eauto.
    + eexists. eexists. split; [eauto|].
      intros s H.
      pose proof (Sv_closed _ _ H).
      pose proof (instantiation_env_closed V).
      intros.
      rewrite <- msubst_subst in H3; auto.
      replace (msubst e <{ [x := s] t1 }>)
           with (msubst ((x,s)::e) t1) in H3 by auto.
      eapply (IHHT ((x,T2)::c)); eauto.
      constructor; auto. eapply Sv_val; eauto.

  - (* T_App *)
    pose proof (IHHT1 _ eq_refl _ V).
    pose proof (IHHT2 _ eq_refl _ V).
    unfold St.
    rewrite msubst_app.
    intros.
    destruct (norm_App1 H1 H2) as [t1' [S1 [S2 S3]]].
    pose proof (H _ S1 S2).
    inv H3. destruct H5 as [x [t11 [E P]]].
    subst t1'.
    assert (value <{ \x : T2, t11 }>) by eauto.
    destruct (norm_App2 S3 H3 H2) as [t2' [Q1 [Q2 Q3]]].
    pose proof (H0 _ Q1 Q2).
    pose proof (P _ H5).
    eapply H6; auto.
    pose proof (Sv_val H5).
    pose proof (ST_AppAbs x T2 t11 t2' H7).
    inv Q3.
    + exfalso. eapply H2. eexists; eauto.
    + erewrite (step_deterministic _ _ _ H9 H8) in H10.
      eauto.

  (* FILL IN HERE *) Admitted.
(** [] *)

(* ================================================================= *)
(** ** Safety Theorem *)

(** Putting everything tegether, we obtain our alternative
    proof of type soundness. *)

Theorem type_soundness : forall t T, empty |-- t \in T -> safe t.
Proof.
  intros.
  eapply St_safe.
  eapply syntactic_type_semantic in H.
  unfold has_semantic_type in H.
  assert (empty = mupdate empty nil) by reflexivity.
  eapply (H nil H0 nil). eauto.
Qed.

(* 2026-08-24 09:57 *)
