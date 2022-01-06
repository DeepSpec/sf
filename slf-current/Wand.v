(** * Wand: The Magic Wand Operator *)

Set Implicit Arguments.
From SLF Require Import LibSepReference.
From SLF Require Repr.
Close Scope trm_scope.

Implicit Types h : heap.
Implicit Types P : Prop.
Implicit Types H : hprop.
Implicit Types Q : val->hprop.

(* ################################################################# *)
(** * First Pass *)

(** This chapter introduces an additional Separation Logic operator,
    called the "magic wand", and written [H1 \-* H2].

    This operator has multiple use:
    - it helps reformulate the consequence-frame rule in an improved manner,
      through a rule called the "ramified frame rule",
    - it helps stating the weakest-preconditions of a number of
      languages constructs in a concise manner,
    - it can be useful to state specification for certain data structures.

    This chapter is organized as follows:
    - definition and properties of the magic wand operator,
    - generalization of the magic wand to postconditions,
    - statement and benefits of the ramified frame rule,
    - statement of the ramified frame rule in weakest-precondition style,
    - generalized definition of [wpgen] that recurses in local functions.

    The addition and bonus section includes further discussion, including:
    - presentation of alternative, equivalent definitions of the magic wand,
    - statement and proofs of additional properties of the magic wand,
    - a revised definition of [mkstruct] using the magic wand.
    - "Texan triples", which express function specifications using the
      magic wand instead of using triples,
    - two other operators, disjunction and non-separating conjunction,
      so as to complete the presentation of all Separation Logic operators. *)

(* ================================================================= *)
(** ** Intuition for the Magic Wand *)

(** The magic wand operation [H1 \-* H2], to be read "H1 wand H2",
    defines a heap predicate such that, if we extend it with [H1],
    we obtain [H2]. Formally, the following entailment holds:

      H1 \* (H1 \-* H2) ==> H2.

    Intuitively, if one can think of the star [H1 \* H2] as the addition
    [H1 + H2], then one can think of [H1 \-* H2] as the subtraction
    [-H1 + H2]. The entailment stated above essentially captures the idea
    that [(-H1 + H2) + H1] simplifies to [H2].

    Note, however, that the operation [H1 \-* H2] only makes sense if [H1]
    describes a piece of heap that "can" be subtracted from [H2]. Otherwise,
    the predicate [H1 \-* H2] characterizes a heap that cannot possibly exist.
    Informally speaking, [H1] must somehow be a subset of [H2] for the
    subtraction [-H1 + H2] to make sense.

    Another possible analogy is that of logical operators. If [P1] and [P2]
    were propositions (of type [Prop]), then [P1 \* P2] would mean [P1 /\ P2]
    and [P1 \-* P2] would mean [P1 -> P2]. The entailment
    [P1 \* (P1 \-* P2) ==> P2] then corresponds to the tautology
    [(P1 /\ (P1 -> P2)) -> P2]. *)

(* ================================================================= *)
(** ** Definition of the Magic Wand *)

Module WandDef.

(** Technically, [H1 \-* H2] holds of a heap [h] if, for any heap
    [h'] disjoint from [h] and that satisfies [H1], the union
    of [h] and [h'] satisfies [H2].

    The operator [hwand], which implements the notation [H1 \-* H2],
    may thus be defined as follows. *)

Definition hwand' (H1 H2:hprop) : hprop :=
  fun h => forall h', Fmap.disjoint h h' -> H1 h' -> H2 (h \u h').

(** The definition above is perfectly fine, however it is more practical
    to use an alternative, equivalent definition of [hwand], expressed
    in terms of previously introduced Separation Logic operators.

    The alternative definition asserts that [H1 \-* H2] corresponds to
    some heap predicate, called [H0], such that [H0] starred with [H1]
    yields [H2]. In other words, [H0] is such that [(H1 \* H0) ==> H2].
    In the definition of [hwand] shown below, observe how [H0] is
    existentially quantified. *)

Definition hwand (H1 H2:hprop) : hprop :=
  \exists H0, H0 \* \[ H1 \* H0 ==> H2 ].

Notation "H1 \-* H2" := (hwand H1 H2) (at level 43, right associativity).

(** As we establish further in this file, one can prove that [hwand]
    and [hwand'] define the same operator.

    The reason we prefer taking [hwand] as definition rather than [hwand']
    is that it enables us to establish all the properties of the magic wand
    by exploiting the tactic [xsimpl], conducting all the reasoning at the
    level of [hprop] rather than having to work with explicit heaps of type
    [heap]. *)

(* ================================================================= *)
(** ** Characteristic Property of the Magic Wand *)

(** The magic wand is not so easy to make sense of, at first. Reading
    its introduction and elimination rules may help further appreciate
    its meaning.

    The operator [H1 \-* H2] satisfies the following equivalence.
    Informally speaking, think of [H0 = -H1+H2] and [H1+H0 = H2]
    being equivalent. *)

Lemma hwand_equiv : forall H0 H1 H2,
  (H0 ==> H1 \-* H2) <-> (H1 \* H0 ==> H2).
Proof using.
  unfold hwand. iff M.
  { xchange M. intros H N. xchange N. }
  { xsimpl H0. xchange M. }
Qed.

(** It turns out that the magic wand operator is uniquely defined by the
    equivalence [(H0 ==> H1 \-* H2) <-> (H1 \* H0 ==> H2)].
    In other words, as we establish further on, any operator that satisfies
    the above equivalence for all arguments is provably equal to [hwand]. *)

(** The right-to-left direction of the equivalence is an introduction rule:
    it tells what needs to be proved for constructing a magic wand [H1 \-* H2]
    from a state [H0]. What needs to be proved to establish [H0 ==> (H1 \-* H2)]
    is that [H0], when starred with [H1], yields [H2]. *)

Lemma himpl_hwand_r : forall H0 H1 H2,
  (H1 \* H0) ==> H2 ->
  H0 ==> (H1 \-* H2).
Proof using. introv M. applys hwand_equiv. applys M. Qed.

(** The left-to-right direction of the equivalence is an elimination rule:
    it tells what can be deduced from an entailment [H0 ==> (H1 \-* H2)].
    What can be deduced from this entailment is that if [H0] is starred
    with [H1], then [H2] can be recovered. *)

Lemma himpl_hwand_r_inv : forall H0 H1 H2,
  H0 ==> (H1 \-* H2) ->
  (H1 \* H0) ==> H2.
Proof using. introv M. applys hwand_equiv. applys M. Qed.

(** This elimination rule can be equivalently reformulated in the following
    form, which makes clearer that [H1 \-* H2], when starred with [H1],
    yields [H2]. *)

Lemma hwand_cancel : forall H1 H2,
  H1 \* (H1 \-* H2) ==> H2.
Proof using. intros. applys himpl_hwand_r_inv. applys himpl_refl. Qed.

Arguments hwand_cancel : clear implicits.

(** **** Exercise: 3 stars, standard, especially useful (hwand_inv)

    Prove the following inversion lemma for [hwand]. This lemma
    essentially captures the fact that [hwand] entails its alternative
    definition [hwand']. *)

Lemma hwand_inv : forall h1 h2 H1 H2,
  (H1 \-* H2) h2 ->
  H1 h1 ->
  Fmap.disjoint h1 h2 ->
  H2 (h1 \u h2).
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(* ================================================================= *)
(** ** Magic Wand for Postconditions *)

(** In what follows, we generalize the magic wand to operate on postconditions,
    introducing a heap predicate of the form [Q1 \--* Q2], of type [hprop].
    Note that the magic wand between two postconditions produces a heap
    predicate, and not a postcondition.

    The definition follows exactly the same pattern as [hwand]: it quantifies
    some heap predicate [H0] such that [H0] starred with [Q1] yields [Q2]. *)

Definition qwand (Q1 Q2:val->hprop) : hprop :=
  \exists H0, H0 \* \[ Q1 \*+ H0 ===> Q2 ].

Notation "Q1 \--* Q2" := (qwand Q1 Q2) (at level 43).

(** The operator [qwand] satisfies essentially the same properties as [hwand].
    Let us begin with the associated equivalence rule, which captures both
    the introduction and the elimination rule. *)

Lemma qwand_equiv : forall H Q1 Q2,
  H ==> (Q1 \--* Q2)  <->  (Q1 \*+ H) ===> Q2.
Proof using.
  unfold qwand. iff M.
  { intros v. xchange M. intros H4 N. xchange N. }
  { xsimpl H. xchange M. }
Qed.

(** The cancellation rule follows. *)

Lemma qwand_cancel : forall Q1 Q2,
  Q1 \*+ (Q1 \--* Q2) ===> Q2.
Proof using. intros. rewrite <- qwand_equiv. applys qimpl_refl. Qed.

(** An interesting property of [qwand] is the fact that we can specialize
    [Q1 \--* Q2] to [(Q1 v) \-* (Q2 v)], for any value [v]. *)

Lemma qwand_specialize : forall (v:val) (Q1 Q2:val->hprop),
  (Q1 \--* Q2) ==> (Q1 v \-* Q2 v).
Proof using.
  intros. unfold qwand, hwand. xpull. intros H0 M.
  xsimpl H0. xchange M.
Qed.

(* ================================================================= *)
(** ** Frame Expressed with [hwand]: the Ramified Frame Rule *)

(** Recall the consequence-frame rule, which is pervasively used
    for example by the tactic [xapp] for reasoning about applications. *)

Parameter triple_conseq_frame : forall H2 H1 Q1 t H Q,
  triple t H1 Q1 ->
  H ==> H1 \* H2 ->
  Q1 \*+ H2 ===> Q ->
  triple t H Q.

(** This rule suffers from a practical issue, which we illustrate in
    details on a concrete example further on. For now, let us just
    attempt to describe the issue at a high-level.

    In short, the problem stems from the fact that we need to instantiate
    [H2] for applying the rule. Providing [H2] by hand is not practical, thus
    we need to infer it. The value of [H2] can be computed as the subtraction
    of [H] minus [H1]. The resulting value may then exploited in the last
    premise for constructing [Q1 \*+ H2]. This transfer of information via [H2]
    from one subgoal to another can be obtained by introducing an "evar" (Coq
    unification variable) for [H2]. However this approach does not work
    well in the cases where [H] contains existential quantifiers. Indeed,
    such existential quantifiers are typically first extracted out of the
    entailment [H ==> H1 \* H2] by the tactic [xsimpl]. However, these
    existentially quantified variables are not in the scope of [H2], hence
    the instantiation of the evar associated with [H2] typically fails. *)

(** The "ramified frame rule" exploits the magic wand operator to circumvent
    the problem, by merging the two premises [H ==> H1 \* H2] and
    [Q1 \*+ H2 ===> Q] into a single premise that no longer mentions [H2].

    This replacement premise is [H ==> H1 \* (Q1 \--* Q)]. To understand where
    it comes from, observe first that the second premise [Q1 \*+ H2 ===> Q]
    is equivalent to [H2 ==> (Q1 \--* Q)]. By replacing [H2] with [Q1 \--* Q]
    inside the first premise [H ==> H1 \* H2], we obtain the new premise
    [H ==> H1 \* (Q1 \--* Q)].

    This merging of the two entailments leads us to the statement of the
    "ramified frame rule" shown below. *)

Lemma triple_ramified_frame : forall H1 Q1 t H Q,
  triple t H1 Q1 ->
  H ==> H1 \* (Q1 \--* Q) ->
  triple t H Q.
Proof using.
  introv M W. applys triple_conseq_frame (Q1 \--* Q) M.
  { applys W. } { applys qwand_cancel. }
Qed.

(** Reciprocally, we can prove that the ramified frame rule entails
    the consequence-frame rule. Hence, the ramified frame rule has
    the same expressive power as the consequence-frame rule. *)

Lemma triple_conseq_frame_of_ramified_frame : forall H2 H1 Q1 t H Q,
  triple t H1 Q1 ->
  H ==> H1 \* H2 ->
  Q1 \*+ H2 ===> Q ->
  triple t H Q.
Proof using.
  introv M WH WQ. applys triple_ramified_frame M.
  xchange WH. xsimpl. rewrite qwand_equiv. applys WQ.
Qed.

(* ================================================================= *)
(** ** Ramified Frame Rule in Weakest-Precondition Style *)

(** The ramified frame rule, which we have just stated for triples,
    features a counterpart expressed in weakest-precondition style ([wp]).

    In what follows, we present the "wp ramified rule", named [wp_ramified].
    This rule admits a concise statement and subsumes all other
    structural rules of Separation Logic. Its statement is as follows.

    (wp t Q1) \* (Q1 \--* Q2) ==> (wp t Q2).
*)

(** To see where this statement comes from, recall from the chapter
    [WPsem] the rule named [wp_conseq_frame], which combines
    the consequence rule and the frame rule for [wp]. *)

Parameter wp_conseq_frame : forall t H Q1 Q2,
  Q1 \*+ H ===> Q2 ->
  (wp t Q1) \* H ==> (wp t Q2).

(** Let us reformulate this rule using a magic wand. The premise
    [Q1 \*+ H ===> Q2] can be rewritten as [H ==> (Q1 \--* Q2)].
    By replacing [H] with [Q1 \--* Q2] in the conclusion of
    [wp_conseq_frame], we obtain the ramified rule for [wp]. *)

Lemma wp_ramified : forall t Q1 Q2,
  (wp t Q1) \* (Q1 \--* Q2) ==> (wp t Q2).
Proof using. intros. applys wp_conseq_frame. applys qwand_cancel. Qed.

(** **** Exercise: 3 stars, standard, especially useful (wp_conseq_frame_of_wp_ramified)

    Prove that [wp_conseq_frame] is derivable from [wp_ramified].
    To that end, prove the statement of [wp_conseq_frame] by using
    only [wp_ramified], the characteristic property of the magic
    wand [qwand_equiv], and properties of the entailment relation. *)

Lemma wp_conseq_frame_of_wp_ramified : forall t H Q1 Q2,
  Q1 \*+ H ===> Q2 ->
  (wp t Q1) \* H ==> (wp t Q2).
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** The following reformulation of [wp_ramified] can be more practical
    to exploit in practice, because it applies to any goal of the form
    [H ==> wp t Q]. *)

Lemma wp_ramified_trans : forall t H Q1 Q2,
  H ==> (wp t Q1) \* (Q1 \--* Q2) ->
  H ==> (wp t Q2).
Proof using. introv M. xchange M. applys wp_ramified. Qed.

End WandDef.

(* ================================================================= *)
(** ** Automation with [xsimpl] for [hwand] Expressions *)

(** One can extend the tactic [xsimpl] to recognize the magic wand,
    and automatically perform a number of obvious simplifications.
    This extension is implemented in the file [LibSepSimpl], which
    exports the tactic [xsimpl] illustrated in this section. *)

Module XsimplDemo.

(** [xsimpl] is able to spot a magic wand that cancels out.
    For example, if an iterated separating conjunction includes
    both [H2 \-* H3] and [H2], then these two heap predicates can
    be merged, leaving just [H3]. *)

Lemma xsimpl_demo_hwand_cancel : forall H1 H2 H3 H4 H5,
  H1 \* (H2 \-* H3) \* H4 \* H2 ==> H5.
Proof using. intros. xsimpl. Abort.

(** [xsimpl] is able to simplify uncurried magic wands.
    For example, if an iterated separating conjunction includes
    [(H1 \* H2 \* H3) \-* H4] and [H2], the two predicates can be
    merged, leaving [(H1 \* H3) \-* H4]. *)

Lemma xsimpl_demo_hwand_cancel_partial : forall H1 H2 H3 H4 H5 H6,
  ((H1 \* H2 \* H3) \-* H4) \* H5 \* H2 ==> H6.
Proof using. intros. xsimpl. Abort.

(** [xsimpl] automatically applies the introduction rule [himpl_hwand_r]
    when the right-hand-side, after prior simplification, reduces to
    just a magic wand. In the example below, [H1] is first cancelled out
    from both sides, then [H3] is moved from the RHS to the LHS. *)

Lemma xsimpl_demo_himpl_hwand_r : forall H1 H2 H3 H4 H5,
  H1 \* H2 ==> H1 \* (H3 \-* (H4 \* H5)).
Proof using. intros. xsimpl. Abort.

(** [xsimpl] can iterate a number of simplifications involving
    different magic wands. *)

Lemma xsimpl_demo_hwand_iter : forall H1 H2 H3 H4 H5,
  H1 \* H2 \* ((H1 \* H3) \-* (H4 \-* H5)) \* H4 ==> ((H2 \-* H3) \-* H5).
Proof using. intros. xsimpl. Qed.

(** [xsimpl] is also able to deal with the magic wand for postconditions.
    In particular, it is able to merge [Q1 \--* Q2] with [Q1 v],
    leaving [Q2 v]. *)

Lemma xsimpl_demo_qwand_cancel : forall v (Q1 Q2:val->hprop) H1 H2,
  (Q1 \--* Q2) \* H1 \* (Q1 v) ==> H2.
Proof using. intros. xsimpl. Abort.

(** [xsimpl] is able to prove entailments whose right-hand side is
    a magic wand.  *)
Lemma xsimpl_hwand_frame : forall H1 H2 H3,
  (H1 \-* H2) ==> ((H1 \* H3) \-* (H2 \* H3)).
Proof using.
  intros. xsimpl.
  (* [xsimpl] first step is to turn the goal into:
     [(H1 \-* H2) \* (H1 \* H3) ==> (H2 \* H3)]. *)
Qed.

End XsimplDemo.

(* ================================================================= *)
(** ** Evaluation of [wpgen] Recursively in Locally Defined Functions *)

Module WPgenRec.
Implicit Types vx vf : val.

(** Recall from chapter [WPgen] the original definition of [wpgen],
    that is, before numerous refactoring. It admitted the following shape.

    Fixpoint wpgen (t:trm) (Q:val->hprop) : hprop :=
      match t with
      | trm_val v      => Q v
      | trm_fun x t1   => Q (val_fun x t1)
      | trm_fix f x t1 => Q (val_fix f x t1)
      ...
      end.

    This definition of [wpgen t Q] does not recurse inside the body
    of functions that occur in the argument [t]. Instead, it treats
    such locally defined functions just like values. *)

(** Not processing local functions does not limit expressiveness, because
    it is always possible for the user to manually invoke [wpgen]
    for each locally defined function, during the verification proof.

    Nevertheless, it is much more satisfying and much more practical
    to set up [wpgen] so that it recursively computes the weakest
    precondition of all the local functions that it encounters during
    its evaluation.

    In what follows, we show how such a version of [wpgen] can be set up.
    We begin with the case of non-recursive functions of the form
    [trm_fun x t1], then generalize the definition to the slightly more complex
    case of recursive functions of the form [trm_fix f x t1]. In both cases,
    the function [wpgen] will get recursively invoked on the body [t1]
    of the function, in a context extended with the appropriate bindings.

    The new definition of [wpgen] will take the shape shown below, for
    well-suited definitions of [wpgen_fun] and [wpgen_fix] yet to be
    introduced. In the code snippet below, [vx] denotes a value to
    which the function may be applied, and [vf] denotes the value
    associated with the function itself, this value being used in particular
    in the case of recursive calls.

    Fixpoint wpgen (E:ctx) (t:trm) : formula :=
      mkstruct match t with
      | trm_val v      => wpgen_val v
      | trm_fun x t1   => wpgen_fun (fun vx => wpgen ((x,vx)::E) t1)
      | trm_fix f x t1 => wpgen_fix (fun vf vx => wpgen ((f,vf)::(x,vx)::E) t1)
      ...
      end.
*)

(* ----------------------------------------------------------------- *)
(** *** 1. Treatment of Non-Recursive Functions *)

(** For simplicity, let us assume for now the substitution context [E] to be
    empty, and let us ignore the presence of the predicate [mkstruct].
    Our goal task is to provide a definition for [wpgen (trm_fun x t1) Q],
    expressed in terms of [wpgen t1].

    Let [vf] denote the function [val_fun x t1], which the term [trm_fun x t1]
    evaluates to. The heap predicate [wpgen (trm_fun x t1) Q] should
    assert that that the postcondition [Q] holds of the result value [vf],
    i.e., that [Q vf] should hold.

    Rather than specifying that [vf] is equal to [val_fun x t1] as we were
    doing previously, we would like to specify that [vf] denotes a function
    whose body admits [wpgen t1] as weakest precondition. This information
    no longer exposes the syntax of the term [t1], and is nevertheless
    sufficient for the user to reason about the behavior of the function [vf].

    To that end, we define the heap predicate [wpgen (trm_fun x t1) Q] to
    be of the form [\forall vf, \[P vf] \-* Q vf] for a carefully crafted
    predicate [P] that describes the behavior of the function by means of its
    weakest precondition. [P] is defined further on.

    The universal quantification on [vf] is intended to hide away from the
    user the fact that [vf] actually denotes [val_fun x t1]. It would be
    correct to replace [\forall vf, ...] with [let vf := val_fun x t1 in ...],
    yet we are purposely trying to abstract away from the syntax of [t1], hence
    the universal quantification of [vf].

    In the heap predicate [\forall vf, \[P vf] \-* Q vf], the magic wand
    features a left-hand side of the form [\[P vf]] is intended to provide
    to the user the knowledge of the weakest precondition of the body [t1] of
    the function, in such a way that the user is able to derive the
    specification aimed for the local function [vf].

    Concretely, the proposition [P vf] should enable the user establishing
    properties of applications of the form [trm_app vf vx], where [vf] denotes
    the function and [vx] denotes an argument to which the function is applied.

    To figure out the details of the statement of [P], it is useful to recall
    from chapter [WPgen] the statement of the lemma
    [triple_app_fun_from_wpgen], which we used for reasoning about top-level
    functions. Its statement appears below---variables were renamed to better
    match the current context. *)

Parameter triple_app_fun_from_wpgen : forall vf vx x t1 H' Q',
  vf = val_fun x t1 ->
  H' ==> wpgen ((x,vx)::nil) t1 Q' ->
  triple (trm_app vf vx) H' Q'.

(** The lemma above enables establishing a triple for an application
    [trm_app vf vx] with precondition [H'] and postcondition [Q'],
    from the premise [H' ==> wgen ((x,vx)::nil) t1 Q'].

    It therefore makes sense, in our definition of the predicate
    [wpgen (trm_fun x t1) Q], which we said would take the form
    [\forall vf, \[P vf] \-* Q vf], to define [P vf] as:

    forall vx H' Q', (H' ==> wpgen ((x,vx)::nil) t1 Q') ->
                     triple (trm_app vf vx) H' Q'

    This proposition can be slightly simplified, by using [wp] instead
    of [triple], allowing to eliminate [H']. We thus define [P vf] as:

    forall vx H', wpgen ((x,vx)::nil) t1 Q' ==> wp (trm_app vf vx) Q'
*)

(** Overall, the definition of [wpgen E t] is as follows. Note that
    the occurence of [nil] is replaced with [E] to account for the
    case of a nonempty context.

  Fixpoint wpgen (E:ctx) (t:trm) : formula :=
    mkstruct match t with
    ...
    | trm_fun x t1 => fun Q =>
       let P vf :=
         (forall vx H', wpgen ((x,vx)::nil) t1 Q' ==> wp (trm_app vf vx) Q') in
       \forall vf, \[P vf] \-* Q vf
   ...
   end.
*)

(** The actual definition of [wpgen] exploits an intermediate definition
    called [wpgen_fun], as shown below:

    Fixpoint wpgen (E:ctx) (t:trm) : formula :=
      mkstruct match t with
      ...
      | trm_fun x t1 => wpgen_fun (fun vx => wpgen ((x,vx)::E) t1)
      ...
      end.

    where [wpgen_fun] is defined as follows:
*)

Definition wpgen_fun (Fof:val->formula) : formula := fun Q =>
  \forall vf, \[forall vx Q', Fof vx Q' ==> wp (trm_app vf vx) Q'] \-* Q vf.

(** The soundness lemma for this construct follows from the wp-style
    reasoning rule for applications, called [wp_app_fun], introduced in
    chapter [WPsem]. It is not needed to follow at this stage through
    the details of the proof. (The proof involves lemmas about [\forall]
    and about [\-*] that are stated and proved only further on in this
    chapter.) *)

Lemma wpgen_fun_sound : forall x t1 Fof,
  (forall vx, formula_sound (subst x vx t1) (Fof vx)) ->
  formula_sound (trm_fun x t1) (wpgen_fun Fof).
Proof using.
  introv M. intros Q. unfolds wpgen_fun. applys himpl_hforall_l (val_fun x t1).
  xchange hwand_hpure_l.
  { intros. applys himpl_trans_r. { applys* wp_app_fun. } { applys* M. } }
  { applys wp_fun. }
Qed.

(** When we carry out the proof of soundness for the new version of [wpgen]
    that features [wpgen_fun], we obtain the following new proof obligation.
    (To see it, play the proof of lemma [wpgen_sound],
    in file [LibSepDirect.v].) *)

Lemma wpgen_fun_proof_obligation : forall E x t1,
  (forall E, formula_sound (isubst E t1) (wpgen E t1)) ->
  formula_sound (trm_fun x (isubst (rem x E) t1))
                (wpgen_fun (fun v => wpgen ((x,v)::E) t1)).

(** The proof exploits the lemma [wpgen_fun_sound] that we just established,
    as well as a substitution lemma, the same as the one used to justify the
    soundness of the [wpgen] of a let-binding. *)

Proof using.
  introv IH. applys wpgen_fun_sound.
  { intros vx. rewrite <- isubst_rem. applys IH. }
Qed.

(** Like for other auxiliary functions associated with [wpgen], we introduce
    a custom notation for [wpgen_fun]. Here, we let [Fun x := F] stand for
    [wpgen_fun (fun x => F)]. *)

Notation "'Fun' x ':=' F1" :=
  ((wpgen_fun (fun x => F1)))
  (at level 69, x ident, right associativity,
  format "'[v' '[' 'Fun'  x  ':='  F1  ']' ']'").

(* ----------------------------------------------------------------- *)
(** *** 2. Treatment of Recursive Functions *)

(** The formula produced by [wpgen] for a recursive function [trm_fix f x t1]
    is almost the same as for a non-recursive function, the main difference
    being that we need to add a binding in the context to associate the name [f]
    of the recursive function with the value [vf] that corresponds to the
    recursive function.

    Here again, the heap predicate [wpgen (trm_fun x t1) Q] will be of the
    form [\forall vf, \[P vf] \-* Q vf].

    To figure out the details of the statement of [P], recall from [WPgen]
    the statement of [triple_app_fix_from_wpgen], which is useful for reasoning
    about top-level recursive functions. *)

Parameter triple_app_fix_from_wpgen : forall vf vx f x t1 H' Q',
  vf = val_fix f x t1 ->
  H' ==> wpgen ((f,vf)::(x,vx)::nil) t1 Q' ->
  triple (trm_app vf vx) H' Q'.

(** It therefore makes sense to define [P vf] as:

    forall vx H' Q', (H' ==> wpgen ((f,vf)::(x,vx)::nil) t1 Q') ->
                     triple (trm_app vf vx) H' Q'

    which can be rewritten as:

    forall vx H', wpgen ((f,vf)::(x,vx)::nil) t1 Q' ==> wp (trm_app vf vx) Q'

    We thus consider:

    Fixpoint wpgen (E:ctx) (t:trm) : formula :=
      mkstruct match t with
      | ..
      | trm_fix f x t1 => wpgen_fix (fun vf v => wpgen ((f,vf)::(x,v)::E) t1)
      | ..
      end

    with the following definition for [wpgen_fix]. *)

Definition wpgen_fix (Fof:val->val->formula) : formula := fun Q =>
  \forall vf, \[forall vx Q', Fof vf vx Q' ==> wp (trm_app vf vx) Q'] \-* Q vf.

(** The soundness lemma for [wpgen_fix] is very similar to that of [wpgen_fun].
    Again, it is not needed to follow through the details of this proof. *)

Lemma wpgen_fix_sound : forall f x t1 Fof,
  (forall vf vx, formula_sound (subst x vx (subst f vf t1)) (Fof vf vx)) ->
  formula_sound (trm_fix f x t1) (wpgen_fix Fof).
Proof using.
  introv M. intros Q. unfolds wpgen_fix.
  applys himpl_hforall_l (val_fix f x t1). xchange hwand_hpure_l.
  { intros. applys himpl_trans_r. { applys* wp_app_fix. } { applys* M. } }
  { applys wp_fix. }
Qed.

(** The proof of soundness of [wpgen] involves the following proof obligation
    to handle the case of recursive functions. (To see it, play the proof of
    lemma [wpgen_sound], in file [LibSepDirect.v].) *)

Lemma wpgen_fix_proof_obligation : forall E f x t1,
  (forall E, formula_sound (isubst E t1) (wpgen E t1)) ->
  formula_sound (trm_fix f x (isubst (rem x (rem f E)) t1))
                    (wpgen_fix (fun vf vx => wpgen ((f,vf)::(x,vx)::E) t1)).
Proof using.
  introv IH. applys wpgen_fix_sound.
  { intros vf vx. rewrite <- isubst_rem_2. applys IH. }
Qed.

(** Here again, we introduce a piece of notation for [wpgen_fix]. We let
    [Fix f x := F] stand for [wpgen_fix (fun f x => F)]. *)

Notation "'Fix' f x ':=' F1" :=
  ((wpgen_fix (fun f x => F1)))
  (at level 69, f ident, x ident, right associativity,
  format "'[v' '[' 'Fix'  f  x  ':='  F1  ']' ']'").

(** Remark: similarly to [xfun], one could devise a [xfix] tactic.
    We omit the details. *)

(* ----------------------------------------------------------------- *)
(** *** 3. Final Definition of [wpgen], with Processing a Local Functions *)

(** The final definition of [wpgen] appears below. *)

Fixpoint wpgen (E:ctx) (t:trm) : formula :=
  mkstruct match t with
  | trm_val v => wpgen_val v
  | trm_var x => wpgen_var E x
  | trm_fun x t1 => wpgen_fun (fun v => wpgen ((x,v)::E) t1)
  | trm_fix f x t1 => wpgen_fix (fun vf v => wpgen ((f,vf)::(x,v)::E) t1)
  | trm_if t0 t1 t2 => wpgen_if t0 (wpgen E t1) (wpgen E t2)
  | trm_seq t1 t2 => wpgen_seq (wpgen E t1) (wpgen E t2)
  | trm_let x t1 t2 => wpgen_let (wpgen E t1) (fun v => wpgen ((x,v)::E) t2)
  | trm_app t1 t2 => wp (isubst E t)
  end.

(** The full soundness proof appears in file [LibSepDirect], lemma
    [wpgen_sound]. *)

(* ----------------------------------------------------------------- *)
(** *** 4. Tactic to Reason About Functions *)

(** Like for other language constructs, we introduce a custom tactic
    for [wpgen_fun]. It is called [xfun], and helps the user to process a
    local function definition in the course of a verification script.

    The tactic [xfun] can be invoked either with or without providing a
    specification for the local function. *)

(** First, we describe the tactic [xfun S], where [S] describes the
    specification of the local function. A typical call is of the form
    [xfun (fun (f:val) => forall ..., triple (f ..) .. ..)].

    The tactic [xfun S] generates two subgoals. The first one requires the
    user to establish the specification [S] for the function whose body admits
    the weakest precondition [Fof]. The second one requires the user to prove
    that the rest of the program is correct, in a context where the local
    function can be assumed to satisfy the specification [S].

    The definition of [xfun S] appears next. It is not required to understand
    the details. An example use case appears further on. *)

Lemma xfun_spec_lemma : forall (S:val->Prop) H Q Fof,
  (forall vf,
    (forall vx H' Q', (H' ==> Fof vx Q') -> triple (trm_app vf vx) H' Q') ->
    S vf) ->
  (forall vf, S vf -> (H ==> Q vf)) ->
  H ==> wpgen_fun Fof Q.
Proof using.
  introv M1 M2. unfold wpgen_fun. xsimpl. intros vf N.
  applys M2. applys M1. introv K. rewrite <- wp_equiv. xchange K. applys N.
Qed.

Tactic Notation "xfun" constr(S) :=
  xseq_xlet_if_needed; xstruct_if_needed; applys xfun_spec_lemma S.

(** Second, we describe the tactic [xfun] without argument. It applies to a goal
    of the form [H ==> wpgen_fun Fof Q]. The tactic [xfun] simply makes
    available an hypothesis about the local function. The user may subsequently
    exploit this hypothesis for reasoning about a call to that function, just
    like if the code of the function was inlined at its call site. The use of
    [xfun] without argument is usually relevant only for local functions that
    are invoked exactly once (as is often the case for functions passed to
    higher-order iterators). Again, an example use case appears further on. *)

Lemma xfun_nospec_lemma : forall H Q Fof,
  (forall vf,
     (forall vx H' Q', (H' ==> Fof vx Q') -> triple (trm_app vf vx) H' Q') ->
     (H ==> Q vf)) ->
  H ==> wpgen_fun Fof Q.
Proof using.
  introv M. unfold wpgen_fun. xsimpl. intros vf N. applys M.
  introv K. rewrite <- wp_equiv. xchange K. applys N.
Qed.

Tactic Notation "xfun" :=
  xseq_xlet_if_needed; xstruct_if_needed; applys xfun_nospec_lemma.

(** A generalization of [xfun] that handles recursive functions may be defined
    following exactly the same pattern. *)

(** This completes our presentation of a version of [wpgen] that recursively
    processes the local definition of non-recursive functions. An practical
    example is presented next. *)

(* ----------------------------------------------------------------- *)
(** *** 5. Example Computation of [wpgen] in Presence of a Local Function *)

(** In the example that follows, we assume all the set up from [WPgen] to
    be reproduced with the definition of [wpgen] that leverages [wpgen_fun]
    and [wpgen_fix]. This set up is formalized in full in the file
    [LibSepDirect]. *)

Import DemoPrograms.

(** Consider the following example program, which involves a local function
    definition, then two successive calls to that local function. *)

Definition myfun : val :=
  <{ fun 'p =>
       let 'f = (fun_ 'u => incr 'p) in
       'f ();
       'f () }>.

(** We first illustrate a call to [xfun] with an explicit specification.
    Here, the function [f] is specified as incrementing the reference [p].
    Observe that the body function of the function [f] is verified only
    once. The reasoning about the two calls to the function [f] that appears
    in the code are done with respect to the specification that we provide
    as argument to [xfun] at the moment of the definition of [f]. *)

Lemma triple_myfun : forall (p:loc) (n:int),
  triple (trm_app myfun p)
    (p ~~> n)
    (fun _ => p ~~> (n+2)).
Proof using.
  xwp.
  xfun (fun (f:val) => forall (m:int),
    triple (f())
      (p ~~> m)
      (fun _ => p ~~> (m+1))); intros f Hf.
  { intros. applys Hf. clear Hf. xapp. (* exploits [triple_incr] *) xsimpl. }
  xapp. (* exploits [Hf]. *)
  xapp. (* exploits [Hf]. *)
  replace (n+1+1) with (n+2); [|math]. xsimpl.
Qed.

(** We next illustrate a call to [xfun] without argument. The "generic
    specification" that comes as hypothesis about the local function
    is a proposition that describes the behavior of the function in terms
    of the weakest-precondition of its body.

    When reasoning about a call to the function, one can invoke this
    generic specification. The effect is equivalent to that of inlining
    the code of the function at its call site.

    Here, there are two calls to the function. We will thus have to exploit
    twice the generic specification of [f], which corresponds to its body
    [incr p]. We will therefore have to reason twice about the increment
    function. *)

Lemma triple_myfun' : forall (p:loc) (n:int),
  triple (trm_app myfun p)
    (p ~~> n)
    (fun _ => p ~~> (n+2)).
Proof using.
  xwp.
  xfun; intros f Hf.
  xapp. (* exploits [Hf] *)
  xapp. (* exploits [triple_incr] *)
  xapp. (* exploits [Hf] *)
  xapp. (* exploits [triple_incr] *)
  replace (n+1+1) with (n+2); [|math]. xsimpl.
Qed.

End WPgenRec.

(* ################################################################# *)
(** * More Details *)

(* ================================================================= *)
(** ** Benefits of the Ramified Rule over the Consequence-Frame Rule *)

(** Earlier on, we sketched an argument claiming that the consequence-
    frame rule is not very well suited for carrying out proofs in
    practice, due to issues with working with evars for instantiating
    the heap predicate [H2] in the rule. Let us come back to this point
    and describe the issue in depth on a concrete example, and show
    how the ramified frame rule smoothly handles that same example. *)

Module WandBenefits.
Import WandDef.

(** Recall the consequence-frame rule. *)

Parameter triple_conseq_frame : forall H2 H1 Q1 t H Q,
  triple t H1 Q1 ->
  H ==> H1 \* H2 ->
  Q1 \*+ H2 ===> Q ->
  triple t H Q.

(** One practical caveat with this rule is that we must resolve [H2],
    which corresponds to the difference between [H] and [H1].
    In practice, providing [H2] explicitly is extremely tedious.
    The alternative is to leave [H2] as an evar, and count on the
    fact that the tactic [xsimpl], when applied to [H ==> H1 \* H2],
    will correctly instantiate [H2].

    This approach works in simple cases, but fails in particular in
    the case where [H] contains an existential quantifier.
    For a concrete example, consider the specification of the
    function [ref], which allocates a reference. *)

Parameter triple_ref : forall (v:val),
  triple (val_ref v)
    \[]
    (funloc p => p ~~> v).

(** Assume that wish to derive the following triple, which extends
    both the precondition and the postcondition of the above specification
    [triple_ref] with the heap predicate [\exists l' v', l' ~~> v'].
    This predicate describes the existence of some, totally unspecified,
    reference cell. It is a bit artificial but illustrates well the issue. *)

Lemma triple_ref_extended : forall (v:val),
  triple (val_ref v)
    (\exists l' v', l' ~~> v')
    (funloc p => p ~~> v \* \exists l' v', l' ~~> v').

(** Let us prove that this specification is derivable from the
    original one, namely [triple_ref]. *)

Proof using.
  intros. applys triple_conseq_frame.
  (* observe the evar [?H2] that appears in the second and third subgoals *)
  { applys triple_ref. }
  { (* here, [?H2] should be in theory instantiated with the LHS.
       but [xsimpl] strategy is to first extract the quantifiers
       from the LHS. After that, the instantiation of [?H2] fails,
       because the LHS contains variables that are not defined in
       the scope of the evar [?H2] at the time it was introduced. *)
    xsimpl.
Abort.

(** Now, let us apply the ramified frame rule to carry out the same
    proof, and observe how the problem does not show up. *)

Lemma triple_ref_extended' : forall (v:val),
  triple (val_ref v)
    (\exists l' v', l' ~~> v')
    (funloc p => p ~~> v \* \exists l' v', l' ~~> v').
Proof using.
  intros. applys triple_ramified_frame.
  { applys triple_ref. }
  { xsimpl.
    (* Here again, [xsimpl] strategy works on the LHS, and pulls out
       the existentially quantified variables. But it works here
       because the remaining of the reasoning takes place in the
       same subgoal, in the scope of the extended Coq context. *)
    intros l' v'. rewrite qwand_equiv. xsimpl. auto. }
Qed.

End WandBenefits.

(* ================================================================= *)
(** ** Properties of [hwand] *)

Module WandProperties.
Import WandDef.

(** We next present the most important properties of [H1 \-* H2].

    Thereafter, the tactic [xsimpl] is accessible, but in a form
    that does not provide support for the magic wand.

    The actual tactic would trivially solve many of these lemmas,
    but using it would be cheating because the implementation of
    [xsimpl] relies on several of these lemmas. *)

(* ----------------------------------------------------------------- *)
(** *** Structural Properties of [hwand] *)

(** The operator [H1 \-* H2] is contravariant in [H1] and covariant
    in [H2], similarly to the implication operator [->]. *)

Lemma hwand_himpl : forall H1 H1' H2 H2',
  H1' ==> H1 ->
  H2 ==> H2' ->
  (H1 \-* H2) ==> (H1' \-* H2').
Proof using.
  introv M1 M2. applys himpl_hwand_r. xchange M1.
  xchange (hwand_cancel H1 H2). applys M2.
Qed.

(** Two predicates [H1 \-* H2] ans [H2 \-* H3] may simplify
    to [H1 \-* H3]. This simplification is reminiscent of the
    arithmetic operation [(-H1 + H2) + (-H2 + H3) = (-H1 + H3)]. *)

Lemma hwand_trans_elim : forall H1 H2 H3,
  (H1 \-* H2) \* (H2 \-* H3) ==> (H1 \-* H3).
Proof using.
  intros. applys himpl_hwand_r. xchange (hwand_cancel H1 H2).
Qed.

(** The predicate [H \-* H] holds of the empty heap.
    Intuitively, one can rewrite [0] as [-H + H]. *)

Lemma himpl_hempty_hwand_same : forall H,
  \[] ==> (H \-* H).
Proof using. intros. apply himpl_hwand_r. xsimpl. Qed.

(* ----------------------------------------------------------------- *)
(** *** Tempting Yet False Properties for [hwand] *)

(** The reciprocal entailement [(H \-* H) ==> \[]] is false, however.
    For a counterexample, instantiate [H] as [fun h => True], or,
    equivalently, [\exists H', H']. A singleton heap does satisfy
    [H \-* H], although it clearly does not satisfy the empty
    predicate [\[]]. *)

Lemma himpl_hwand_same_hempty_counterexample : forall p v,
  let H := (\exists H', H') in
  (p ~~> v) ==> (H \-* H).
Proof using. intros. subst H. rewrite hwand_equiv. xsimpl. Qed.

(** In technical terms, [H \-* H] characterizes the empty heap only
    in the case where [H] is "precise", that is, when it describes
    a heap of a specific shape. In the above counterexample, [H] is
    clearly not precise, because it is satisfied by heaps of any shape.
    The notion of "preciseness" can be defined formally, yet it is
    out of the scope of this course. *)

(** As another tempting yet false property of the magic wand,
    consider the reciprocal entailment to the cancellation lemma,
    that is, [H2 ==> H1 \* (H1 \-* H2)]. It does not hold in general.

    As counter-example, consider [H2 = \[]] and [H1 = \[False]].
    We can prove that the empty heap does not satisfies
    [\[False] \* (\[False] \-* \[])]. *)

Lemma not_himpl_hwand_r_inv_reciprocal : exists H1 H2,
  ~ (H2 ==> H1 \* (H1 \-* H2)).
Proof using.
  exists \[False] \[]. intros N. forwards K: N (Fmap.empty:heap).
  applys hempty_intro. rewrite hstar_hpure_l in K. destruct K. auto.
Qed.

(** More generally, one has to be suspicious of any entailment
    that introduces wands "out of nowhere".

    The entailment [hwand_trans_elim]:
    [(H1 \-* H2) \* (H2 \-* H3) ==> (H1 \-* H3)]
    is correct because, intuitively, the left-hand-side captures
    that [H1 <= H2] and that [H2 <= H3] for some vaguely defined
    notion of [<=] as "being a subset of". From that, we can derive
    [H1 <= H3], and justify that the right-hand-side makes sense.

    On the contrary, the reciprocal entailment
    [(H1 \-* H3) ==> (H1 \-* H2) \* (H2 \-* H3)]
    is certainly false, because from [H1 <= H3] there is no way
    to justify [H1 <= H2] nor [H2 <= H3]. *)

(* ----------------------------------------------------------------- *)
(** *** Interaction of [hwand] with [hempty] and [hpure] *)

(** The heap predicate [\[] \-* H] is equivalent to [H]. *)

Lemma hwand_hempty_l : forall H,
  (\[] \-* H) = H.
Proof using.
  intros. unfold hwand. xsimpl.
  { intros H0 M. xchange M. }
  { xsimpl. }
Qed.

(** The lemma above shows that the empty predicate [\[]] can
    be removed from the LHS of a magic wand.

    More generally, a pure predicate [\[P]] can be removed from
    the LHS of a magic wand, as long as [P] is true. Formally: *)

Lemma hwand_hpure_l : forall P H,
  P ->
  (\[P] \-* H) = H.
Proof using.
  introv HP. unfold hwand. xsimpl.
  { intros H0 M. xchange M. applys HP. }
  { xpull. auto. }
Qed.

(** Reciprocally, to prove that a heap satisfies [\[P] \-* H],
    it suffices to prove that this heap satisfies [H] under the
    assumption that [P] is true. Formally: *)

Lemma himpl_hwand_hpure_r : forall H1 H2 P,
  (P -> H1 ==> H2) ->
  H1 ==> (\[P] \-* H2).
Proof using. introv M. applys himpl_hwand_r. xsimpl. applys M. Qed.

(** **** Exercise: 2 stars, standard, optional (himpl_hwand_hpure_lr)

    Prove that [\[P1 -> P2]] entails [\[P1] \-* \[P2]]. *)

Lemma himpl_hwand_hpure_lr : forall (P1 P2:Prop),
  \[P1 -> P2] ==> (\[P1] \-* \[P2]).
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(* ----------------------------------------------------------------- *)
(** *** Interaction of [hwand] with [hstar] *)

(** An interesting property is that arguments on the LHS of a magic
    wand can equivalently be "curried" or "uncurried", just like a
    function of type "(A * B) -> C" is equivalent to a function of
    type "A -> B -> C".

    The heap predicates [(H1 \* H2) \-* H3] and [H1 \-* (H2 \-* H3)]
    and [H2 \-* (H1 \-* H3)] are all equivalent. Intuitively, they all
    describe the predicate [H3] with the missing pieces [H1] and [H2].

    The equivalence between the uncurried form [(H1 \* H2) \-* H3]
    and the curried form [H1 \-* (H2 \-* H3)] is formalized by the
    lemma shown below. The third form, [H2 \-* (H1 \-* H3)], follows
    from the commutativity property [H1 \* H2 = H2 \* H1]. *)

Lemma hwand_curry_eq : forall H1 H2 H3,
  (H1 \* H2) \-* H3 = H1 \-* (H2 \-* H3).
Proof using.
  intros. applys himpl_antisym.
  { apply himpl_hwand_r. apply himpl_hwand_r.
    xchange (hwand_cancel (H1 \* H2) H3). }
  { apply himpl_hwand_r. xchange (hwand_cancel H1 (H2 \-* H3)).
    xchange (hwand_cancel H2 H3). }
Qed.

(** Another interesting property is that the RHS of a magic wand
    can absorb resources that the magic wand is starred with.

    Concretely, from [(H1 \-* H2) \* H3], one can get the predicate
    [H3] to be absorbed by the [H2] in the magic wand, yielding
    [H1 \-* (H2 \* H3)].

    One way to read this: "if you own [H3] and, when given [H1]
    you own [H2], then, when given [H1], you own both [H2] and [H3]." *)

Lemma hstar_hwand : forall H1 H2 H3,
  (H1 \-* H2) \* H3 ==> H1 \-* (H2 \* H3).
Proof using.
  intros. applys himpl_hwand_r. xsimpl. xchange (hwand_cancel H1 H2).
Qed.

(** Remark: the reciprocal entailment is false: it is not possible
    to extract a heap predicate out of the LHS of an entailment.
    Indeed, that heap predicate might not exist if it is mentioned
    in the RHS of the magic wand. *)

(** **** Exercise: 1 star, standard, especially useful (himpl_hwand_hstar_same_r)

    Prove that [H1] entails [H2 \-* (H2 \* H1)]. *)

Lemma himpl_hwand_hstar_same_r : forall H1 H2,
  H1 ==> (H2 \-* (H2 \* H1)).
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 2 stars, standard, especially useful (hwand_cancel_part)

    Prove that [H1 \* ((H1 \* H2) \-* H3)] simplifies to [H2 \-* H3]. *)

Lemma hwand_cancel_part : forall H1 H2 H3,
  H1 \* ((H1 \* H2) \-* H3) ==> (H2 \-* H3).
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 3 stars, standard, optional (hwand_frame)

    Prove that [H1 \-* H2] entails to [(H1 \* H3) \-* (H2 \* H3)].
    Hint: you can use [xsimpl] during the proof. *)

Lemma hwand_frame : forall H1 H2 H3,
  H1 \-* H2 ==> (H1 \* H3) \-* (H2 \* H3).
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

End WandProperties.

(* ################################################################# *)
(** * Optional Material *)

(* ================================================================= *)
(** ** Equivalence Between Alternative Definitions of the Magic Wand *)

Module HwandEquiv.
Implicit Type op : hprop->hprop->hprop.

(** In what follows we prove the equivalence between the three
    characterizations of [hwand H1 H2] that we have presented:

    1. The definition [hwand'], expressed directly in terms of heaps:
       [fun h => forall h', Fmap.disjoint h h' -> H1 h' -> H2 (h' \u h)]

    2. The definition [hwand], expressed in terms of existing operators:
       [\exists H0, H0 \* \[ (H1 \* H0) ==> H2]]

    3. The characterization via the equivalence [hwand_equiv]:
       [forall H0 H1 H2, (H0 ==> H1 \-* H2) <-> (H1 \* H0 ==> H2)].

    4. The characterization via the pair of the introduction rule
       [himpl_hwand_r] and the elimination rule [hwand_cancel].

    To prove the 4-way equivalence, we first prove the equivalence
    between (1) and (2), then prove the equivalence between (2) and (3),
    and finally the equivalence between (3) and (4).
*)

Definition hwand_characterization_1 (op:hprop->hprop->hprop) :=
  op = (fun H1 H2 =>
         (fun h => forall h', Fmap.disjoint h h' -> H1 h' -> H2 (h' \u h))).

Definition hwand_characterization_2 (op:hprop->hprop->hprop) :=
  op = (fun H1 H2 => \exists H0, H0 \* \[ H1 \* H0 ==> H2 ]).

Definition hwand_characterization_3 (op:hprop->hprop->hprop) :=
  forall H0 H1 H2, (H0 ==> op H1 H2) <-> (H1 \* H0 ==> H2).

Definition hwand_characterization_4 (op:hprop->hprop->hprop) :=
     (forall H0 H1 H2, (H1 \* H0 ==> H2) -> (H0 ==> op H1 H2))
  /\ (forall H1 H2, (H1 \* (op H1 H2) ==> H2)).

(** The equivalence proofs are given here for reference. It is not needed
    to follow through the technical details. *)

Lemma hwand_characterization_1_eq_2 :
  hwand_characterization_1 = hwand_characterization_2.
Proof using.
  applys pred_ext_1. intros op.
  unfold hwand_characterization_1, hwand_characterization_2.
  asserts K: (forall A B, A = B -> (op = A <-> op = B)).
  { intros. iff; subst*. } apply K; clear K.
  apply pred_ext_3. intros H1 H2 h. iff M.
  { exists (=h). rewrite hstar_hpure_r. split.
    { auto. }
    { intros h3 K3. rewrite hstar_comm in K3.
      destruct K3 as (h1&h2&K1&K2&D&U). subst h1 h3.
      rewrites (>> union_comm_of_disjoint D). applys M D K2. } }
  { (* This direction reproduces the proof of [hwand_inv]. *)
    intros h1 D K1. destruct M as (H0&M).
    destruct M as (h0&h2&K0&K2&D'&U).
    lets (N&E): hpure_inv (rm K2). subst h h2.
    rewrite Fmap.union_empty_r in *.
    applys N. applys hstar_intro K1 K0. applys disjoint_sym D. }
Qed.

Lemma hwand_characterization_2_eq_3 :
  hwand_characterization_2 = hwand_characterization_3.
Proof using.
  applys pred_ext_1. intros op.
  unfold hwand_characterization_2, hwand_characterization_3. iff K.
  { subst. intros. (* apply hwand_equiv. *) iff M.
    { xchange M. intros H3 N. xchange N. }
    { xsimpl H0. xchange M. } }
  { apply fun_ext_2. intros H1 H2. apply himpl_antisym.
    { lets (M&_): (K (op H1 H2) H1 H2). xsimpl (op H1 H2).
      applys M. applys himpl_refl. }
    { xsimpl. intros H0 M. rewrite K. applys M. } }
Qed.

Lemma hwand_characterization_3_eq_4 :
  hwand_characterization_3 = hwand_characterization_4.
Proof using.
  applys pred_ext_1. intros op.
  unfold hwand_characterization_3, hwand_characterization_4. iff K.
  { split.
    { introv M. apply <- K. apply M. }
    { intros. apply K. auto. } }
  { destruct K as (K1&K2). intros. split.
    { introv M. xchange M. xchange (K2 H1 H2). }
    { introv M. applys K1. applys M. } }
Qed.

End HwandEquiv.

(* ================================================================= *)
(** ** Operator [hforall] *)

Module NewQwand.
Export WandDef.

(** In the beginning of this chapter, we defined [qwand] following the pattern
    of [hwand], as [ \exists H0, H0 \* \[ Q1 \*+ H0 ==> Q2 ] ].
    An alternative approach consists of defining [qwand] in terms of [hwand].

    This alternative definition involves the universal quantifier for heap
    predicates, written [\forall x, H]. The universal quantifier is the
    counterpart of the existential quantifier [\exists x, H].

    Using the [\forall] quantifier, we may define [Q1 \--* Q2] as the heap
    predicate [\forall v, (Q1 v) \-* (Q2 v)]. *)

(** Let us first formalize the definition of the universal quantifier on
    [hprop]. Technically, a heap predicate of the form [\forall x, H] stands for
    [hforall (fun x => H)], where the definition of [hforall] follows the
    exact same pattern as for [hexists]. The definition shown below is somewhat
    technical---details may be safely skipped over. *)

Definition hforall (A : Type) (J : A -> hprop) : hprop :=
  fun h => forall x, J x h.

Notation "'\forall' x1 .. xn , H" :=
  (hforall (fun x1 => .. (hforall (fun xn => H)) ..))
  (at level 39, x1 binder, H at level 50, right associativity,
   format "'[' '\forall' '/ '  x1  ..  xn , '/ '  H ']'").

(** The introduction and elimination rule for [hforall] are as follows. *)

Lemma hforall_intro : forall A (J:A->hprop) h,
  (forall x, J x h) ->
  (hforall J) h.
Proof using. introv M. applys* M. Qed.

Lemma hforall_inv : forall A (J:A->hprop) h,
  (hforall J) h ->
  forall x, J x h.
Proof using. introv M. applys* M. Qed.

(** The introduction rule in an entailement for [\forall] appears below.
    To prove that a heap satisfies [\forall x, J x], one must show that,
     for any [x], this heap satisfies [J x]. *)

Lemma himpl_hforall_r : forall A (J:A->hprop) H,
  (forall x, H ==> J x) ->
  H ==> (\forall x, J x).
Proof using. introv M. intros h K x. apply~ M. Qed.

(** The elimination rule in an entailment for [\forall] appears below.
    Assuming a heap satisfies [\forall x, J x], one can derive that the
    same heap satisfies [J v] for any desired value [v]. *)

Lemma hforall_specialize : forall A (v:A) (J:A->hprop),
  (\forall x, J x) ==> (J v).
Proof using. intros. intros h K. apply* K. Qed.

(** This last lemma can equivalently be formulated in the following way,
    which makes it easier to apply in some cases. *)

Lemma himpl_hforall_l : forall A (v:A) (J:A->hprop) H,
  J v ==> H ->
  (\forall x, J x) ==> H.
Proof using. introv M. applys himpl_trans M. applys hforall_specialize. Qed.

(** Universal quantifers that appear in the precondition of a triple
    may be specialized, just like those in the left-hand side of an
    entailment. *)

Lemma triple_hforall : forall A (v:A) t (J:A->hprop) Q,
  triple t (J v) Q ->
  triple t (\forall x, J x) Q.
Proof.
  introv M. applys triple_conseq M.
  { applys hforall_specialize. }
  { applys qimpl_refl. }
Qed.

(* ================================================================= *)
(** ** Alternative Definition of [qwand] *)

Declare Scope qwand_scope.
Open Scope qwand_scope.

(** We are now read to state the alternative definition of [Q1 \--* Q2],
    as the heap predicate [\forall v, (Q1 v) \-* (Q2 v)]. *)

Definition qwand (Q1 Q2:val->hprop) : hprop :=
  \forall v, (Q1 v) \-* (Q2 v).

Notation "Q1 \--* Q2" := (qwand Q1 Q2) (at level 43) : qwand_scope.

(** Let us establish the properties of the new definition of [qwand].

    We begin by the specialization lemma, which asserts that [Q1 \--* Q2]
    can be specialized to [(Q1 v) \-* (Q2 v)] for any value [v]. This
    result is a direct consequence of the corresponding specialization
    property of [\forall]. *)

Lemma qwand_specialize : forall (v:val) (Q1 Q2:val->hprop),
  (Q1 \--* Q2) ==> (Q1 v \-* Q2 v).
Proof using.
  intros. unfold qwand. applys himpl_hforall_l v. xsimpl.
Qed.

(** We next prove the equivalence rule. *)

Lemma qwand_equiv : forall H Q1 Q2,
  H ==> (Q1 \--* Q2)  <->  (Q1 \*+ H) ===> Q2.
Proof using.
  intros. iff M.
  { intros x. xchange M. xchange (qwand_specialize x).
    xchange (hwand_cancel (Q1 x)). }
  { applys himpl_hforall_r. intros x. applys himpl_hwand_r.
    xchange (M x). }
Qed.

(** The cancellation rule follows. *)

Lemma qwand_cancel : forall Q1 Q2,
  Q1 \*+ (Q1 \--* Q2) ===> Q2.
Proof using. intros. rewrite <- qwand_equiv. applys qimpl_refl. Qed.

(** Like [H1 \-* H2], the operation [Q1 \--* Q2] is contravariant in [Q1]
    and covariant in [Q2]. *)

Lemma qwand_himpl : forall Q1 Q1' Q2 Q2',
  Q1' ===> Q1 ->
  Q2 ===> Q2' ->
  (Q1 \--* Q2) ==> (Q1' \--* Q2').
Proof using.
  introv M1 M2. rewrite qwand_equiv. intros x.
  xchange (qwand_specialize x). xchange M1.
  xchange (hwand_cancel (Q1 x)). xchange M2.
Qed.

(** Like [H1 \-* H2], the operation [Q1 \--* Q2] can absorb in its RHS
    resources to which it is starred. *)

Lemma hstar_qwand : forall Q1 Q2 H,
  (Q1 \--* Q2) \* H ==> Q1 \--* (Q2 \*+ H).
Proof using.
  intros. rewrite qwand_equiv. xchange (@qwand_cancel Q1).
Qed.

(** **** Exercise: 1 star, standard, especially useful (himpl_qwand_hstar_same_r)

    Prove that [H] entails [Q \--* (Q \*+ H)]. *)

Lemma himpl_qwand_hstar_same_r : forall H Q,
  H ==> Q \--* (Q \*+ H).
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 2 stars, standard, optional (qwand_cancel_part)

    Prove that [H \* ((Q1 \*+ H) \--* Q2)] simplifies to [Q1 \--* Q2].
    Hint: use [xchange]. *)

Lemma qwand_cancel_part : forall H Q1 Q2,
  H \* ((Q1 \*+ H) \--* Q2) ==> (Q1 \--* Q2).
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** ** Equivalence between Alternative Definitions of the Magic Wand
       for Postconditions *)

Module QwandEquiv.
Implicit Type op : (val->hprop)->(val->hprop)->hprop.

(** In what follows we prove the equivalence between five equivalent
    characterizations of [qwand H1 H2]:

    1. The definition expressed directly in terms of heaps:
       [fun h => forall v h', Fmap.disjoint h h' -> Q1 v h' -> Q2 v (h \u h')]

    2. The definition [qwand], expressed in terms of existing operators:
       [\exists H0, H0 \* \[ (Q1 \*+ H0) ===> Q2]]

    3. The definition expressed using the universal quantifier:
       [\forall v, (Q1 v) \-* (Q2 v)]

    4. The characterization via the equivalence [hwand_equiv]:
       [forall H0 H1 H2, (H0 ==> H1 \-* H2) <-> (H1 \* H0 ==> H2)].

    5. The characterization via the pair of the introduction rule
       [himpl_qwand_r] and the elimination rule [qwand_cancel].

    The proof are essentially identical to the equivalence proofs for [hwand],
    except for definition (3), which is specific to [qwand].
*)

Definition qwand_characterization_1 op :=
  op = (fun Q1 Q2 => (fun h => forall v h', Fmap.disjoint h h' ->
                                            Q1 v h' -> Q2 v (h \u h'))).

Definition qwand_characterization_2 op :=
  op = (fun Q1 Q2 => \exists H0, H0 \* \[ Q1 \*+ H0 ===> Q2 ]).

Definition qwand_characterization_3 op :=
  op = (fun Q1 Q2 => \forall v, (Q1 v) \-* (Q2 v)).

Definition qwand_characterization_4 op :=
  forall H0 Q1 Q2, (H0 ==> op Q1 Q2) <-> (Q1 \*+ H0 ===> Q2).

Definition qwand_characterization_5 op :=
     (forall H0 Q1 Q2, (Q1 \*+ H0 ===> Q2) -> (H0 ==> op Q1 Q2))
  /\ (forall Q1 Q2, (Q1 \*+ (op Q1 Q2) ===> Q2)).

Lemma hwand_characterization_1_eq_2 :
  qwand_characterization_1 = qwand_characterization_2.
Proof using.
  applys pred_ext_1. intros op.
  unfold qwand_characterization_1, qwand_characterization_2.
  asserts K: (forall A B, A = B -> (op = A <-> op = B)).
  { intros. iff; subst*. } apply K; clear K.
  apply pred_ext_3. intros Q1 Q2 h. iff M.
  { exists (=h). rewrite hstar_hpure_r. split.
    { auto. }
    { intros v h3 K3. rewrite hstar_comm in K3.
      destruct K3 as (h1&h2&K1&K2&D&U). subst h1 h3. applys M D K2. } }
  { intros v h1 D K1. destruct M as (H0&M).
    destruct M as (h0&h2&K0&K2&D'&U).
    lets (N&E): hpure_inv (rm K2). subst h h2.
    rewrite Fmap.union_empty_r in *.
    applys N. rewrite hstar_comm. applys hstar_intro K0 K1 D. }
Qed.

Lemma qwand_characterization_2_eq_3 :
  qwand_characterization_2 = qwand_characterization_3.
Proof using.
  applys pred_ext_1. intros op.
  unfold qwand_characterization_2, qwand_characterization_3.
  asserts K: (forall A B, A = B -> (op = A <-> op = B)).
  { intros. iff; subst*. } apply K; clear K.
  apply fun_ext_2. intros Q1 Q2. apply himpl_antisym.
  { xpull. intros H0 M. applys himpl_hforall_r. intros v.
    rewrite hwand_equiv. xchange M. }
  { xsimpl (qwand Q1 Q2). applys qwand_cancel. }
Qed.

Lemma qwand_characterization_2_eq_4 :
  qwand_characterization_2 = qwand_characterization_4.
Proof using.
  applys pred_ext_1. intros op.
  unfold qwand_characterization_2, qwand_characterization_4. iff K.
  { subst. intros. iff M.
    { xchange M. intros v H3 N. xchange N. }
    { xsimpl H0. xchange M. } }
  { apply fun_ext_2. intros H1 H2. apply himpl_antisym.
    { lets (M&_): (K (op H1 H2) H1 H2). xsimpl (op H1 H2).
      applys M. applys himpl_refl. }
    { xsimpl. intros H0 M. rewrite K. applys M. } }
Qed.

Lemma qwand_characterization_4_eq_5 :
  qwand_characterization_4 = qwand_characterization_5.
Proof using.
  applys pred_ext_1. intros op.
  unfold qwand_characterization_4, qwand_characterization_5. iff K.
  { split.
    { introv M. apply <- K. apply M. }
    { intros. apply K. auto. } }
  { destruct K as (K1&K2). intros. split.
    { introv M. xchange M. xchange (K2 Q1 Q2). }
    { introv M. applys K1. applys M. } }
Qed.

End QwandEquiv.

(* ================================================================= *)
(** ** Simplified Definition of [mkstruct] *)

(** The definition of [mkstruct] can be simplified using the magic
    wand operator for postconditions.

    Recall the definition of [mkstruct] from chapter [WPgen]. *)

Definition mkstruct' (F:formula) : formula :=
  fun (Q:val->hprop) => \exists Q1 H, F Q1 \* H \* \[Q1 \*+ H ===> Q].

(** Observe that the fragment [\exists H, H \* \[Q1 \*+ H ===> Q]]
    is equivalent to [Q1 \--* Q]. This observation leads to the following
    more concise reformulation of the definition of [mkstruct]. *)

Definition mkstruct (F:formula) : formula :=
  fun Q => \exists Q1, F Q1 \* (Q1 \--* Q).

(** Let us prove, for this revised definition, that [mkstruct] satisfies
    the three required properties (recall [WPgen]): [mkstruct_erase],
    [mkstruct_frame], and [mkstruct_conseq]. In these proofs, we assume
    the revised definition of [qwand] expressed in terms of [hwand]
    and [hforall]. *)

Lemma mkstruct_erase : forall F Q,
  F Q ==> mkstruct F Q.
Proof using.
  intros. unfold mkstruct. xsimpl Q. rewrite qwand_equiv. xsimpl.
Qed.

Lemma mkstruct_conseq : forall F Q1 Q2,
  Q1 ===> Q2 ->
  mkstruct F Q1 ==> mkstruct F Q2.
Proof using.
  introv WQ. unfold mkstruct. xpull. intros Q'. xsimpl Q'.
  rewrite qwand_equiv. xchange qwand_cancel. xchange WQ.
Qed.

Lemma mkstruct_frame : forall F H Q,
  (mkstruct F Q) \* H ==> mkstruct F (Q \*+ H).
Proof using.
  intros. unfold mkstruct. xpull. intros Q'. xsimpl Q'.
  rewrite qwand_equiv. xchange qwand_cancel.
Qed.

End NewQwand.

(* ================================================================= *)
(** ** Texan Triples *)

Module TexanTriples.

(** In this section, we assume a version of [xsimpl] that handles
    the magic wand. Note that [hforall] and other operators are
    set "Opaque", their definitions cannot be unfolded. *)

Implicit Types v w : val.
Implicit Types p : loc.

(* ----------------------------------------------------------------- *)
(** *** 1. Example of Texan Triples *)

(** In this section, we show that specification triples can be presented
    in a different style using weakest preconditions. *)

(** Consider for example the specification triple for allocation. *)

Parameter triple_ref : forall v,
  triple (val_ref v)
    \[]
    (funloc p => p ~~> v).

(** This specification can be equivalently reformulated in the following
    form. *)

Parameter wp_ref : forall Q v,
  \[] \* (\forall p, p ~~> v \-* Q (val_loc p)) ==> wp (val_ref v) Q.

(** Above, we purposely left the empty heap predicate to the front to
    indicate where the precondition, if it were not empty, would go in
    the reformulation. *)

(** In what follows, we describe the chain of transformation that can take us
    from the triple form to the [wp] form, and establish the reciprocal.
    We then formalize the general pattern for translating a triple
    into a "texan triple" (i.e., the wp-based specification). *)

(** By replacing [triple t H Q] with [H ==> wp t Q], the specification
    [triple_ref] can be reformulated as follows. *)

Lemma wp_ref_0 : forall v,
  \[] ==> wp (val_ref v) (funloc p => p ~~> v).
Proof using. intros. rewrite wp_equiv. applys triple_ref. Qed.

(** We wish to cast the RHS in the form [wp (val_ref v) Q] for an abstract
    variable [Q]. To that end, we reformulate the above statement by including
    a magic wand relating the current postcondition, which is
    [(funloc p => p ~~> v)], and [Q]. *)

Lemma wp_ref_1 : forall Q v,
  ((funloc p => p ~~> v) \--* Q) ==> wp (val_ref v) Q.
Proof using. intros. xchange (wp_ref_0 v). applys wp_ramified. Qed.

(** This statement can be made slightly more readable by unfolding the
    definition of the magic wand for postconditions, as shown next. *)

Lemma wp_ref_2 : forall Q v,
  (\forall r,     (\exists p, \[r = val_loc p] \* p ~~> v) \-* Q r)
              ==> wp (val_ref v) Q.
Proof using. intros. applys himpl_trans wp_ref_1. xsimpl. Qed.

(** Interestingly, the variable [r], which is equal to [val_loc p],
    can now be substituted away, further increasing readability.
    We obtain the specificaiton of [val_ref] in "Texan triple style". *)

Lemma wp_ref_3 : forall Q v,
  (\forall p, (p ~~> v) \-* Q (val_loc p)) ==> wp (val_ref v) Q.
Proof using.
  intros. applys himpl_trans wp_ref_2. xsimpl. intros ? p ->.
  xchange (hforall_specialize p).
Qed.

(* ----------------------------------------------------------------- *)
(** *** 2. The General Pattern *)

(** In practice, specification triples can (pretty much) all be casted
    in the form: [triple t H (fun r => exists x1 x2, \[r = v] \* H')].
    In such a specification:

    - the value [v] may depend on the [xi],
    - the heap predicate [H'] may depend on [r] and the [xi],
    - the number of existentials [xi] may vary, possibly be zero,
    - the equality [\[r = v]] may be removed if no pure fact is needed about [r].

    Such a specification triple of the form
    [triple t H (fun r => exists x1 x2, \[r = v] \* H']
    can be be reformulated as the Texan triple:
    [(\forall x1 x2, H \-* Q v) ==> wp t Q].

    We next formalize the equivalence between the two presentations, for
    the specific case where the specification involves a single auxiliary
    variable, called [x]. The statement below makes it explicit that
    [v] may depend on [x], and that [H] may depend on [r] and [x]. *)

Lemma texan_triple_equiv : forall t H A (Hof:val->A->hprop) (vof:A->val),
      (triple t H (fun r => \exists x, \[r = vof x] \* Hof r x))
  <-> (forall Q, H \* (\forall x, Hof (vof x) x \-* Q (vof x)) ==> wp t Q).
Proof using.
  intros. rewrite <- wp_equiv. iff M.
  { intros Q. xchange M. applys wp_ramified_trans.
    xsimpl. intros r x ->.
    xchange (hforall_specialize x). }
  { applys himpl_trans M. xsimpl~. }
Qed.

(* ----------------------------------------------------------------- *)
(** *** 3. Other Examples *)

Section WpSpecRef.

(** The wp-style specification of [ref], [get] and [set] follow. *)

Lemma wp_get : forall v p Q,
  (p ~~> v) \* (p ~~> v \-* Q v) ==> wp (val_get p) Q.
Proof using.
  intros. rewrite wp_equiv. applys triple_conseq_frame.
  { applys triple_get. } { applys himpl_refl. } { xsimpl. intros ? ->. auto. }
Qed.

Lemma wp_set : forall v w p Q,
  (p ~~> v) \* (\forall r, p ~~> w \-* Q r) ==> wp (val_set p w) Q.
Proof using.
  intros. rewrite wp_equiv. applys triple_conseq_frame.
  { applys triple_set. } { applys himpl_refl. }
  { intros r. xchange (hforall_specialize r). }
Qed.

Lemma wp_free : forall v p Q,
  (p ~~> v) \* (\forall r, Q r) ==> wp (val_free p) Q.
Proof using.
  intros. rewrite wp_equiv. applys triple_conseq_frame.
  { applys triple_free. } { applys himpl_refl. }
  { intros r. xchange (hforall_specialize r). }
Qed.

(** Alternatively, we can advertize that [set] and [free] output the unit
    value. *)

Parameter triple_set' : forall w p v,
  triple (val_set p w)
    (p ~~> v)
    (fun r => \[r = val_unit] \* p ~~> w).

Parameter triple_free' : forall p v,
  triple (val_free p)
    (p ~~> v)
    (fun r => \[r = val_unit]).

Lemma wp_set' : forall v w p Q,
  (p ~~> v) \* (p ~~> w \-* Q val_unit) ==> wp (val_set p w) Q.
Proof using.
  intros. rewrite wp_equiv. applys triple_conseq_frame.
  { applys triple_set'. }
  { applys himpl_refl. }
  { xsimpl. intros ? ->. auto. }
Qed.

Lemma wp_free' : forall v w p Q,
  (p ~~> v) \* (Q val_unit) ==> wp (val_free p) Q.
Proof using.
  intros. rewrite wp_equiv. applys triple_conseq_frame.
  { applys triple_free'. }
  { applys himpl_refl. }
  { xsimpl. intros ? ->. auto. }
Qed.

End WpSpecRef.

(* ----------------------------------------------------------------- *)
(** *** 4. Equivalent expressiveness *)

(** Let's show that the specification [wp_ref_3] is
    as strong as the original specification [triple_ref]. *)

Lemma triple_ref_of_wp_ref_3 : forall v,
  triple (val_ref v)
    \[]
    (funloc p => p ~~> v).
Proof using.
  intros. rewrite <- wp_equiv.
  applys himpl_trans; [| applys wp_ref_3 ].
  xsimpl*.
Qed.

(** Likewise for the other three operations: the triple-based specification
    is derivable from the wp-based specification. *)

Lemma triple_get_of_wp_get : forall v p,
  triple (val_get p)
    (p ~~> v)
    (fun r => \[r = v] \* (p ~~> v)).
Proof using.
  intros. rewrite <- wp_equiv.
  applys himpl_trans; [| applys wp_get ].
  xsimpl*.
Qed.

Lemma triple_set : forall w p v,
  triple (val_set (val_loc p) v)
    (p ~~> w)
    (fun _ => p ~~> v).
Proof using.
  intros. rewrite <- wp_equiv.
  applys himpl_trans; [| applys wp_set ].
  xsimpl*.
Qed.

Lemma triple_free : forall p v,
  triple (val_free (val_loc p))
    (p ~~> v)
    (fun _ => \[]).
Proof using.
  intros. rewrite <- wp_equiv.
  applys himpl_trans; [| applys wp_free ].
  xsimpl*.
Qed.

(* ----------------------------------------------------------------- *)
(** *** 5. Exercise *)

(** Let us put to practice the use of a Texan triple on a different example.
    Recall the function [incr] and its specification (from [Hprop.v]). *)

Parameter incr : val.

Parameter triple_incr : forall (p:loc) (n:int),
  triple (incr p)
    (p ~~> n)
    (fun v => \[v = val_unit] \* (p ~~> (n+1))).

(** **** Exercise: 3 stars, standard, especially useful (wp_incr)

    State a Texan triple for [incr] as a lemma called [wp_incr],
    then prove this lemma from [triple_incr].

    Hint: the proof is a bit easier by first turning the [wp] into a [triple]
    and then reasoning about triples, compared to working on the [wp] form. *)

(* FILL IN HERE *)

(** [] *)

End TexanTriples.

(* ================================================================= *)
(** ** Direct Proof of [wp_ramified] Directly from Hoare Triples *)

Module WpFromHoare.
Import NewQwand.

(** Recall from the last section of the chapter [WPsem] that it can
    be interesting to define [wp]-style rules directly from the [hoare]
    rules, so as to bypass the statements and proofs of rules for triples.

    In the first part of this chapter, we proved that the rule
    [wp_ramified] is derivable from the consequence-frame rule for triples.
    Let us now show how to prove the rule [wp_ramified] directly from
    the rules of Hoare logic. *)

Lemma wp_ramified : forall t Q1 Q2,
  (wp t Q1) \* (Q1 \--* Q2) ==> (wp t Q2).
Proof using.
  intros. unfold wp. xpull. intros H M.
  xsimpl (H \* (Q1 \--* Q2)). intros H'.
  applys hoare_conseq M. { xsimpl. }
  intros r. xchange (qwand_specialize r). xsimpl.
  rewrite hstar_comm. applys hwand_cancel.
Qed.

End WpFromHoare.

(* ================================================================= *)
(** ** Conjunction and Disjunction Operators on [hprop] *)

(** The disjunction and the (non-separating) conjunction are two
    other Separation Logic operators. The are not so useful in
    practice, because they can be trivially encoded using Coq
    conditional construct, or using Coq pattern matching.
    Nevertheless, these two operators can prove useful in specific
    contexts. We present them also for the sake of completeness. *)

Module ConjDisj.
Import NewQwand.

(* ----------------------------------------------------------------- *)
(** *** Definition of [hor] *)

(** The heap predicate [hor H1 H2] lifts the disjunction operator
    [P1 \/ P2] from [Prop] to [hprop].

    Concretely, the heap predicate [hor H1 H2] describes a heap
    that satisfies [H1] or satifies [H2] (possibly both).

    The heap predicate [hor] admits a direct definition as a
    function over heaps. *)

Definition hor' (H1 H2 : hprop) : hprop :=
  fun h => H1 h \/ H2 h.

(** An alternative definition leverages the [\exists] quantifier.
    The definition, shown below, reads as follows: "there exists
    an unspecified boolean value [b] such that if [b] is true
    then [H1] holds, else if [b] is false then [H2] holds".

    The benefits of this definition is that the proof of its properties
    can be established without manipulating heaps explicitly. *)

Definition hor (H1 H2 : hprop) : hprop :=
  \exists (b:bool), if b then H1 else H2.

(** **** Exercise: 3 stars, standard, optional (hor_eq_hor')

    Prove the equivalence of the definitions [hor] and [hor']. *)

Lemma hor_eq_hor' :
  hor = hor'.
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** The introduction and elimination rules for [hor] are as follows.

    - If [H1] holds, then "[H1] or [H2]" holds.
    - Symmetrically, if [H2] holds, then "[H1] or [H2]" holds.
    - Reciprocally, if "[H1] or [H2]" holds, then one can perform a case
      analysis on whether it is [H1] or [H2] that holds. Concretely, to
      show that "[H1] or [H2]" entails [H3], one must show both that
      [H1] entails [H3] and that [H2] entails [H3]. *)

Lemma himpl_hor_r_l : forall H1 H2,
  H1 ==> hor H1 H2.
Proof using. intros. unfolds hor. exists* true. Qed.

Lemma himpl_hor_r_r : forall H1 H2,
  H2 ==> hor H1 H2.
Proof using. intros. unfolds hor. exists* false. Qed.

(** In practice, these two rules are easier to exploit when combined with a
    transitivity step. *)

Lemma himpl_hor_r_l_trans : forall H1 H2 H3,
  H3 ==> H1 ->
  H3 ==> hor H1 H2.
Proof using. introv W. applys himpl_trans W. applys himpl_hor_r_l. Qed.

Lemma himpl_hor_r_r_trans : forall H1 H2 H3,
  H3 ==> H2 ->
  H3 ==> hor H1 H2.
Proof using. introv W. applys himpl_trans W. applys himpl_hor_r_r. Qed.

(** The elimination rule is stated as follows. *)

Lemma himpl_hor_l : forall H1 H2 H3,
  H1 ==> H3 ->
  H2 ==> H3 ->
  hor H1 H2 ==> H3.
Proof using.
  introv M1 M2. unfolds hor. applys himpl_hexists_l. intros b. case_if*.
Qed.

(** The operator [hor] is commutative. To establish this property, it is
    handy to exploit the following lemma, called [if_neg], which swaps the
    two branches of a conditional by negating the boolean condition. *)

Lemma if_neg : forall (b:bool) A (X Y:A),
  (if b then X else Y) = (if neg b then Y else X).
Proof using. intros. case_if*. Qed.

(** **** Exercise: 2 stars, standard, especially useful (hor_comm)

    Prove that [hor] is a symmetric operator.
    Hint: exploit [if_neg] and [hprop_op_comm] (from chapter [Himpl]). *)

Lemma hor_comm : forall H1 H2,
  hor H1 H2 = hor H2 H1.
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

Module HorExample.
Import Repr.
Implicit Types q : loc.

(** Recall from chapter [Repr] the definition of [MList], and the two
    lemmas [MList_nil] and [MList_cons] that reformulates that definition. *)

(** **** Exercise: 4 stars, standard, especially useful (hor_comm)

    Prove that [MList] can be characterized by a disjunction expressed using
    [hor] as shown below. *)

Lemma MList_using_hor : forall L p,
  MList L p =
     hor (\[L = nil /\ p = null])
         (\exists x q L', \[L = x::L']
                       \* (p ~~~>`{ head := x; tail := q})
                       \* (MList L' q)).
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

End HorExample.

(* ----------------------------------------------------------------- *)
(** *** Definition of [hand] *)

(** The heap predicate [hand H1 H2] lifts the disjunction operator
    [P1 /\ P2] from [Prop] to [hprop].

    Concretely, the heap predicate [hand H1 H2] describes a heap
    that satisfies [H1] and at the same time satifies [H2].

    The heap predicate [hand] admits a direct definition as a
    function over heaps. *)

Definition hand' (H1 H2 : hprop) : hprop :=
  fun h => H1 h /\ H2 h.

(** An alternative definition leverages the [\forall] quantifier.
    The definition, shown below, reads as follows: "for any
    boolean value [b], if [b] is true then [H1] should hold, and
    if [b] is false then [H2] should hold". *)

Definition hand (H1 H2 : hprop) : hprop :=
  \forall (b:bool), if b then H1 else H2.

(** **** Exercise: 2 stars, standard, especially useful (hand_eq_hand')

    Prove the equivalence of the definitions [hand] and [hand']. *)

Lemma hand_eq_hand' :
  hand = hand'.
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** The introduction and elimination rules for [hand] are as follows.

    - If "[H1] and [H2]" holds, then in particular [H1] holds.
    - Symmetrically, if "[H1] and [H2]" holds, then in particular [H2] holds.
    - Reciprocally, to prove that a heap predicate [H3] entails
      "[H1] and [H2]", one must prove that [H3] entails [H1], and that
      [H3] satisfies [H2].
*)

Lemma himpl_hand_l_r : forall H1 H2,
  hand H1 H2 ==> H1.
Proof using. intros. unfolds hand. applys* himpl_hforall_l true. Qed.

Lemma himpl_hand_l_l : forall H1 H2,
  hand H1 H2 ==> H2.
Proof using. intros. unfolds hand. applys* himpl_hforall_l false. Qed.

Lemma himpl_hand_r : forall H1 H2 H3,
  H3 ==> H1 ->
  H3 ==> H2 ->
  H3 ==> hand H1 H2.
Proof using. introv M1 M2 Hh. intros b. case_if*. Qed.

(** **** Exercise: 1 star, standard, especially useful (hand_comm)

    Prove that [hand] is a symmetric operator.
    Hint: use [hprop_op_comm], and [rewrite if_neg] (or a case analysis
    on the boolean value coming from [hand]). *)

Lemma hand_comm : forall H1 H2,
  hand H1 H2 = hand H2 H1.
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

End ConjDisj.

(* ================================================================= *)
(** ** Summary of All Separation Logic Operators *)

Module SummaryHprop.

(** The core operators are defined as functions over heaps. *)

  Definition hempty : hprop :=
    fun h => (h = Fmap.empty).

  Definition hsingle (p:loc) (v:val) : hprop :=
    fun h => (h = Fmap.single p v).

  Definition hstar (H1 H2 : hprop) : hprop :=
    fun h => exists h1 h2, H1 h1
                                /\ H2 h2
                                /\ Fmap.disjoint h1 h2
                                /\ h = Fmap.union h1 h2.

  Definition hexists A (J:A->hprop) : hprop :=
    fun h => exists x, J x h.

  Definition hforall (A : Type) (J : A -> hprop) : hprop :=
    fun h => forall x, J x h.

(** The remaining operators can be defined either as functions over
    heaps, or as derived definitions expressed in terms of the core
    operators defined above. *)

(** Direct definition for the remaining operators. *)

Module ReaminingOperatorsDirect.

  Definition hpure (P:Prop) : hprop :=
    fun h => (h = Fmap.empty) /\ P.

  Definition hwand (H1 H2:hprop) : hprop :=
    fun h => forall h', Fmap.disjoint h h' -> H1 h' -> H2 (h \u h').

  Definition qwand (Q1 Q2:val->hprop) : hprop :=
    fun h => forall v h', Fmap.disjoint h h' -> Q1 v h' -> Q2 v (h \u h').

  Definition hor (H1 H2 : hprop) : hprop :=
    fun h => H1 h \/ H2 h.

  Definition hand (H1 H2 : hprop) : hprop :=
    fun h => H1 h /\ H2 h.

End ReaminingOperatorsDirect.

(** Alternative definitions for the same operators, expressed in terms
    of the core operators. *)

Module ReaminingOperatorsDerived.

  Definition hpure (P:Prop) : hprop :=
    \exists (p:P), \[].

  Definition hwand (H1 H2 : hprop) : hprop :=
    \exists H0, H0 \* \[ (H1 \* H0) ==> H2 ].

  Definition qwand (Q1 Q2 : val->hprop) : hprop :=
    \forall v, (Q1 v) \-* (Q2 v).

  Definition qwand' (Q1 Q2 : val->hprop) : hprop := (* alternative *)
    \exists H0, H0 \* \[ (Q1 \*+ H0) ===> Q2].

  Definition hand (H1 H2 : hprop) : hprop :=
    \forall (b:bool), if b then H1 else H2.

  Definition hor (H1 H2 : hprop) : hprop :=
    \exists (b:bool), if b then H1 else H2.

End ReaminingOperatorsDerived.

(** In practice, it saves a lot of effort to use the derived definitions,
    because using derived definitions all the properties of these definitions
    can be established with the help of the [xsimpl] tactic, through reasoning
    taking place exclusively at the level of [hprop]. *)

End SummaryHprop.

(* ================================================================= *)
(** ** Historical Notes *)

(** The magic wand is an operator that was introduced in the very first days
    of Separation Logic. From a logical perspective, it makes total sense to
    have it. From a practical perspective, however, it was not always entirely
    obvious how the magic wand could simplify specifications and proofs.

    Experience with CFML 1.0 shows that it is possible to develop an entire
    verification frameworks and verify thousands of lines of advanced data
    structures and algorithms without ever involving the magic wand operator.

    The magic wand, however, reveals its interest when exploited (1) in the
    ramified frame rule, and (2) in weakest-precondition style reasoning rules.

    The idea of the ramified frame rule was introduced by
    [Krishnaswami, Birkedal, and Aldrich 2010] (in Bib.v). Its general statement,
    as formulated in the present chapter, was proposed by
    [Hobor and Villard 2013] (in Bib.v). Developers of the tools VST and Iris
    have advertised for the interest of this rule. The ramified frame
    rule was integrated in CFML 2.0 in 2018. *)

(* 2022-01-06 13:53 *)
