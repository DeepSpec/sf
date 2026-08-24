(** * Auto: More Automation *)

Set Warnings "-notation-overridden,-notation-incompatible-prefix".
From Stdlib Require Import Arith List.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.String.
From LF Require Import Maps.
From LF Require Import Imp.
Set Default Goal Selector "!".

(** Up to now, we've used the manual part of Rocq's tactic
    facilities.  In this chapter, we'll learn more about some of
    Rocq's powerful automation features: proof search via the [auto]
    tactic, automated forward reasoning via the [Ltac] hypothesis
    matching machinery, and deferred instantiation of existential
    variables using [eapply] and [eauto].  Using these features
    together with Ltac's scripting facilities will enable us to make
    some of our proofs startlingly short!  Used properly, they can
    also make proofs more maintainable and robust to changes in
    underlying definitions.  A deeper treatment of [auto] and [eauto]
    can be found in the [UseAuto] chapter in _Programming Language
    Foundations_.

    There's one other major category of automation we haven't discussed much
    yet, namely built-in decision procedures for specific kinds of problems:
    [lia] is one example, and at the end of the chapter we will introduce one
    more called [congruence].

    We start with the [auto] tactic, though, and our motivating example will be
    the following proof, repeated with just a few small changes from the
    [Imp] chapter.  We will simplify this proof in several stages. *)

Theorem ceval_deterministic: forall c st st1 st2,
  st =[ c ]=> st1  ->
  st =[ c ]=> st2 ->
  st1 = st2.
Proof.
  intros c st st1 st2 E1 E2;
  generalize dependent st2;
  induction E1; intros st2 E2; inversion E2; subst.
  - (* E_Skip *) reflexivity.
  - (* E_Asgn *) reflexivity.
  - (* E_Seq *)
    rewrite (IHE1_1 st'0 H1) in *.
    apply IHE1_2. assumption.
  (* E_IfTrue *)
  - (* b evaluates to true *)
    apply IHE1. assumption.
  - (* b evaluates to false (contradiction) *)
    rewrite H in H5. discriminate.
  (* E_IfFalse *)
  - (* b evaluates to true (contradiction) *)
    rewrite H in H5. discriminate.
  - (* b evaluates to false *)
    apply IHE1. assumption.
  (* E_WhileFalse *)
  - (* b evaluates to false *)
    reflexivity.
  - (* b evaluates to true (contradiction) *)
    rewrite H in H2. discriminate.
  (* E_WhileTrue *)
  - (* b evaluates to false (contradiction) *)
    rewrite H in H4. discriminate.
  - (* b evaluates to true *)
    rewrite (IHE1_1 st'0 H3) in *.
    apply IHE1_2. assumption.  Qed.

(* ################################################################# *)
(** * The [auto] Tactic *)

(** Thus far, our proof scripts mostly work backward by applying
    relevant hypotheses or lemmas to the goal by name, one at a time. *)

Example auto_example_1 : forall (P Q R: Prop),
  (P -> Q) -> (Q -> R) -> P -> R.
Proof.
  intros P Q R HPQ HQR HP.
  apply HQR. apply HPQ. assumption.
Qed.

(** The [auto] tactic tries to free us from this drudgery by _searching_
    for a sequence of applications to the goal that will finally prove it: *)

Example auto_example_1' : forall (P Q R: Prop),
  (P -> Q) -> (Q -> R) -> P -> R.
Proof.
  auto.
Qed.

(** The [auto] tactic solves goals that are solvable by any combination of
    [intros] and [apply]. *)

(** Using [auto] is always "safe" in the sense that it will
    never fail and will never change the proof state: either it
    completely solves the current goal, or it does nothing. *)

(** Here is a larger example showing [auto]'s power: *)

Example auto_example_2 : forall P Q R S T U : Prop,
  (P -> Q) ->
  (P -> R) ->
  (T -> R) ->
  (S -> T -> U) ->
  ((P -> Q) -> (P -> S)) ->
  T ->
  P ->
  U.
Proof. auto. Qed.

(** Intuitively, we can understand the [auto] tactic as recursively performing
    the following backward search steps:

    - If [assumption] closes the goal, we are done.

    - If the goal is an implication ([->]) or an universal quantifier
      ([forall]), call the [intro] tactic (the unary version of [intros])
      and continue with the new goal.

    - Otherwise, apply a hypothesis whose conclusion unifies with the goal, and
      recurse on the new subgoals. If some subgoal cannot be closed, backtrack
      and try any other hypothesis unifying with the goal.

  If no candidate path leads to a complete proof, [auto] does nothing, leaving
  the goal unchanged. *)

(** If [auto] does not solve our goal as expected we can use [debug
    auto] to see a trace. In fact, [debug auto] prints the whole
    search trace even when [auto] _succeeds_, so we can also use it to
    watch [auto] backtrack: *)

Example auto_algorithm : forall (P Q R: Prop),
  (Q -> R) -> (* HQR : requires [Q] -- dead end *)
  ((P -> P) -> R) -> (* HPPR : requires [P -> P] -- proved by [intro]
                                                    and [assumption] *)
  R.
Proof. intros P Q R HQR HPPR. debug auto. Qed.

(** Proof search could, in principle, take an arbitrarily long time,
    so there is a limit to how deep [auto] will search (by default 5). *)

Example auto_example_3 : forall (P Q R S T U: Prop),
  (P -> Q) ->
  (Q -> R) ->
  (R -> S) ->
  (S -> T) ->
  (T -> U) ->
  P ->
  U.
Proof.
  intros P Q R S T U HPQ HQR HRS HST HTU HP.
  (* [auto] does nothing for this goal, even if it seems solvable *)
  auto.

  (* Let's see what [auto] does with the default search depth
     of 5 by adding the [debug] keyword: *)
  debug auto.

  (* What it did is this: *)
  (* apply HTU. *)
  (* apply HST. *)
  (* apply HRS. *)
  (* apply HQR. *)
  (* apply HPQ. *)
  (* But then it couldn't prove [P]
     even though it had [P] as a hypothesis *)

  (* With an optional argument to [auto] we can change the maximum
     search depth; in this case a depth of 6 does the trick: *)
  auto 6.
Qed.

(** When searching for potential proofs of the current goal,
    [auto] considers the hypotheses in the current context together
    with a _hint database_ of other lemmas and constructors.  Some
    common lemmas about equality and logical operators are installed
    in this hint database by default. *)

Example auto_example_4 : forall P Q R : Prop,
  Q ->
  (Q -> R) ->
  P \/ (Q /\ R).
Proof. auto. Qed.

(** If we want to see which facts [auto] is using, we can use [info_auto]
    instead. As opposed to [debug auto] which also prints failed paths,
    [info_auto] only displays the successful proof path. *)

Example auto_example_4' : forall P Q R : Prop,
  Q ->
  (Q -> R) ->
  P \/ (Q /\ R).
Proof.
  info_auto.
Qed.

(** [auto] used the following facts from the default hint database: *)
Check or_intror : forall A B : Prop, B -> A \/ B.
Check conj : forall A B : Prop, A -> B -> A /\ B.

Example auto_example_5: 2 = 2.
Proof.
  info_auto.
Qed.

(** [auto] subsumes reflexivity because [eq_refl] is
    a fact in the default hint database: *)
Check @eq_refl : forall A (x:A), x = x.

(** We can extend the hint database just for the purposes of one
    application of [auto] by writing "[auto using ...]". *)

Lemma le_antisym : forall n m: nat, (n <= m /\ m <= n) -> n = m.
Proof. lia. Qed.

Example auto_example_6 : forall n m p q : nat,
  (p = q -> (n <= m /\ m <= n)) ->
  p = q ->
  n = m.
Proof.
  auto using le_antisym.
Qed.

(** Of course, in any given development there will probably be
    some specific constructors and lemmas that are used very often in
    proofs.  We can add these to the global hint database by writing

      Hint Resolve T : core.

    at the top level, where [T] is a top-level theorem or a
    constructor of an inductively defined proposition (i.e., anything
    whose type is an implication).  As a shorthand, we can write

      Hint Constructors c : core.

    to tell Rocq to do a [Hint Resolve] for _all_ of the constructors
    from the inductive definition of [c].

    It is also sometimes necessary to add

      Hint Unfold d : core.

    where [d] is a defined symbol, so that [auto] knows to unfold uses
    of [d], thus enabling further possibilities for applying lemmas that
    it knows about. *)

(** It is also possible to define specialized hint databases (besides
    [core]) that can be activated only when needed; indeed, it is good
    style to create your own hint databases instead of polluting
    [core].

    See the Rocq reference manual for details. *)

Hint Resolve le_antisym : core.

Example auto_example_6' : forall n m p q : nat,
  (p = q -> (n <= m /\ m <= n)) ->
  p = q ->
  n = m.
Proof.
  auto. (* picks up hint from database *)
Qed.

Definition is_fortytwo x := (x = 42).

Example auto_example_7: forall x,
  (x <= 42 /\ 42 <= x) -> is_fortytwo x.
Proof.
  auto.  (* does nothing *)
Abort.

Hint Unfold is_fortytwo : core.

Example auto_example_7' : forall x,
  (x <= 42 /\ 42 <= x) -> is_fortytwo x.
Proof.
  auto. (* try also: info_auto. *)
Qed.

(** Note that the [Hint Unfold is_fortytwo] command above the
    example is needed because, unlike the normal [apply] tactic, the
    [simple apply] steps that are performed by [auto] do not do any
    automatic unfolding. *)

(** Let's take a first pass over [ceval_deterministic], using [auto]
    to simplify the proof script. *)

Theorem ceval_deterministic': forall c st st1 st2,
  st =[ c ]=> st1  ->
  st =[ c ]=> st2 ->
  st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2.
  induction E1; intros st2 E2;
    inversion E2; subst; (* <- ends with ; *)
    auto.             (* <---- here's one good place to try auto *)
  - (* E_Seq *)
    rewrite (IHE1_1 st'0 H1) in *.
    auto.             (* <---- here's another *)
  - (* E_IfTrue *)
    rewrite H in H5. discriminate.
  - (* E_IfFalse *)
    rewrite H in H5. discriminate.
  - (* E_WhileFalse *)
    rewrite H in H2. discriminate.
  - (* E_WhileTrue, with b false *)
    rewrite H in H4. discriminate.
  - (* E_WhileTrue, with b true *)
    rewrite (IHE1_1 st'0 H3) in *.
    auto.             (* <---- and another *)
Qed.

(** When we are using a particular tactic many times in a proof, we
    can use a variant of the [Proof] command to make that tactic into
    a default within the proof.  Saying [Proof with t] (where [t] is
    an arbitrary tactic) allows us to use [t1...] as a shorthand for
    [t1;t] within the proof.  As an illustration, here is an alternate
    version of the previous proof, using [Proof with auto]. *)

Theorem ceval_deterministic'_alt: forall c st st1 st2,
  st =[ c ]=> st1 ->
  st =[ c ]=> st2 ->
  st1 = st2.
Proof with auto.
  intros c st st1 st2 E1 E2.
  generalize dependent st2.
  induction E1; intros st2 E2;
    inversion E2; subst...
  - (* E_Seq *)
    rewrite (IHE1_1 st'0 H1) in *...
  - (* E_IfTrue *)
    rewrite H in H5. discriminate.
  - (* E_IfFalse *)
    rewrite H in H5. discriminate.
  - (* E_WhileFalse *)
    rewrite H in H2. discriminate.
  - (* E_WhileTrue, with b false *)
    rewrite H in H4. discriminate.
  - (* E_WhileTrue, with b true *)
    rewrite (IHE1_1 st'0 H3) in *...
Qed.

(* ================================================================= *)
(** ** Exercises  *)

From LF Require IndProp.

Module Exercises.

Import IndProp. Import Pumping.

(** **** Exercise: 1 star, standard (pumping_constant_ge_1_redux)

    Use [auto], [lia], and [;] to reprove this lemma in a "single" line.
    The "official" proof in [IndProp] takes about a dozen lines. *)

Lemma pumping_constant_ge_1 :
  forall T (re : reg_exp T),
    pumping_constant re >= 1.
(* FILL IN HERE *) Admitted.
(* Do not modify the following line: *)
Definition manual_grade_for_pumping_constant_ge_1_redux : option (nat*string) := None.
(** [] *)

(* ----------------------------------------------------------------- *)
(** *** Regular Expression Optimization Exercise  *)

(** **** Exercise: 3 stars, standard (re_opt_match_auto) *)

(** As a simple illustration of the benefits of automation,
    let's consider another problem on regular expressions, which we
    formalized in [IndProp].  A given set of strings can be
    denoted by many different regular expressions.  For example, [App
    EmptyString re] matches exactly the same strings as [re].  We can
    write a function that "optimizes" any regular expression into a
    potentially simpler one by applying this fact throughout the r.e.
    (Note that, for simplicity, the function does not optimize
    expressions that arise as the result of other optimizations.) *)

Fixpoint re_opt {T:Type} (re: reg_exp T) : reg_exp T :=
  match re with
  | App _ EmptySet => EmptySet
  | App EmptyStr re2 => re_opt re2
  | App re1 EmptyStr => re_opt re1
  | App re1 re2 => App (re_opt re1) (re_opt re2)
  | Union EmptySet re2 => re_opt re2
  | Union re1 EmptySet => re_opt re1
  | Union re1 re2 => Union (re_opt re1) (re_opt re2)
  | Star EmptySet => EmptyStr
  | Star EmptyStr => EmptyStr
  | Star re => Star (re_opt re)
  | EmptySet => EmptySet
  | EmptyStr => EmptyStr
  | Char x => Char x
  end.

(** We would like to show the equivalence of re's with their
    "optimized" form.  Here is an incredibly tedious manual
    proof of (one direction of) its correctness: *)

Lemma re_opt_match : forall T (re: reg_exp T) s,
  s =~ re -> s =~ re_opt re.
Proof.
  intros T re s M.
  induction M
    as [| x'
       | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
       | s1 re1 re2 Hmatch IH | s2 re1 re2 Hmatch IH
       | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2].
  - (* MEmpty *) simpl. apply MEmpty.
  - (* MChar *) simpl. apply MChar.
  - (* MApp *) simpl.
    destruct re1.
    + inversion IH1.
    + inversion IH1. simpl. destruct re2.
      * apply IH2.
      * apply IH2.
      * apply IH2.
      * apply IH2.
      * apply IH2.
      * apply IH2.
    + destruct re2.
      * inversion IH2.
      * inversion IH2. rewrite app_nil_r. apply IH1.
      * apply MApp.
        -- apply IH1.
        -- apply IH2.
      * apply MApp.
        -- apply IH1.
        -- apply IH2.
      * apply MApp.
        -- apply IH1.
        -- apply IH2.
      * apply MApp.
        -- apply IH1.
        -- apply IH2.
    + destruct re2.
      * inversion IH2.
      * inversion IH2. rewrite app_nil_r.  apply IH1.
      * apply MApp.
        -- apply IH1.
        -- apply IH2.
      * apply MApp.
        -- apply IH1.
        -- apply IH2.
      * apply MApp.
        -- apply IH1.
        -- apply IH2.
      * apply MApp.
        -- apply IH1.
        -- apply IH2.
    + destruct re2.
      * inversion IH2.
      * inversion IH2. rewrite app_nil_r. apply IH1.
      * apply MApp.
        -- apply IH1.
        -- apply IH2.
      * apply MApp.
        -- apply IH1.
        -- apply IH2.
      * apply MApp.
        -- apply IH1.
        -- apply IH2.
      * apply MApp.
        -- apply IH1.
        -- apply IH2.
    + destruct re2.
      * inversion IH2.
      * inversion IH2. rewrite app_nil_r. apply IH1.
      * apply MApp.
        -- apply IH1.
        -- apply IH2.
      * apply MApp.
        -- apply IH1.
        -- apply IH2.
      * apply MApp.
        -- apply IH1.
        -- apply IH2.
      * apply MApp.
        -- apply IH1.
        -- apply IH2.
  - (* MUnionL *) simpl.
    destruct re1.
    + inversion IH.
    + destruct re2.
      * apply IH.
      * apply MUnionL. apply IH.
      * apply MUnionL. apply IH.
      * apply MUnionL. apply IH.
      * apply MUnionL. apply IH.
      * apply MUnionL. apply IH.
    + destruct re2.
      * apply IH.
      * apply MUnionL. apply IH.
      * apply MUnionL. apply IH.
      * apply MUnionL. apply IH.
      * apply MUnionL. apply IH.
      * apply MUnionL. apply IH.
    + destruct re2.
      * apply IH.
      * apply MUnionL. apply IH.
      * apply MUnionL. apply IH.
      * apply MUnionL. apply IH.
      * apply MUnionL. apply IH.
      * apply MUnionL. apply IH.
    + destruct re2.
      * apply IH.
      * apply MUnionL. apply IH.
      * apply MUnionL. apply IH.
      * apply MUnionL. apply IH.
      * apply MUnionL. apply IH.
      * apply MUnionL. apply IH.
    + destruct re2.
      * apply IH.
      * apply MUnionL. apply IH.
      * apply MUnionL. apply IH.
      * apply MUnionL. apply IH.
      * apply MUnionL. apply IH.
      * apply MUnionL. apply IH.
  - (* MUnionR *) simpl.
    destruct re1.
    + apply IH.
    + destruct re2.
      * inversion IH.
      * apply MUnionR. apply IH.
      * apply MUnionR. apply IH.
      * apply MUnionR. apply IH.
      * apply MUnionR. apply IH.
      * apply MUnionR. apply IH.
    + destruct re2.
      * inversion IH.
      * apply MUnionR. apply IH.
      * apply MUnionR. apply IH.
      * apply MUnionR. apply IH.
      * apply MUnionR. apply IH.
      * apply MUnionR. apply IH.
    + destruct re2.
      * inversion IH.
      * apply MUnionR. apply IH.
      * apply MUnionR. apply IH.
      * apply MUnionR. apply IH.
      * apply MUnionR. apply IH.
      * apply MUnionR. apply IH.
    + destruct re2.
      * inversion IH.
      * apply MUnionR. apply IH.
      * apply MUnionR. apply IH.
      * apply MUnionR. apply IH.
      * apply MUnionR. apply IH.
      * apply MUnionR. apply IH.
    + destruct re2.
      * inversion IH.
      * apply MUnionR. apply IH.
      * apply MUnionR. apply IH.
      * apply MUnionR. apply IH.
      * apply MUnionR. apply IH.
      * apply MUnionR. apply IH.
 - (* MStar0 *) simpl.
    destruct re.
    + apply MEmpty.
    + apply MEmpty.
    + apply MStar0.
    + apply MStar0.
    + apply MStar0.
    + simpl.
      destruct re.
      * apply MStar0.
      * apply MStar0.
      * apply MStar0.
      * apply MStar0.
      * apply MStar0.
      * apply MStar0.
 - (* MStarApp *) simpl.
   destruct re.
   + inversion IH1.
   + inversion IH1. inversion IH2. apply MEmpty.
   + apply star_app.
     * apply MStar1. apply IH1.
     * apply IH2.
   + apply star_app.
     * apply MStar1.  apply IH1.
     * apply IH2.
   + apply star_app.
     * apply MStar1.  apply IH1.
     * apply IH2.
   + apply star_app.
     * apply MStar1.  apply IH1.
     * apply IH2.
Qed.

(** Use [auto] to shorten the proof. The proof above is about 200
    lines. Reduce it to 50 or fewer lines of similar
    density. Eliminate all uses of [apply], thus removing the need to
    name specific constructors and lemmas about regular expressions.

    Hint: You can use a bottom-up approach. First copy-paste the
    entire proof below. Then automate the innermost bullets first,
    proceeding outwards. Frequently double-check that the entire proof
    still compiles. If it doesn't, undo the most recent changes you
    made until you get back to a compiling proof. *)

Lemma re_opt_match'' : forall T (re: reg_exp T) s,
  s =~ re -> s =~ re_opt re.
Proof.
(* FILL IN HERE *) Admitted.
(* Do not modify the following line: *)
Definition manual_grade_for_re_opt_match'' : option (nat*string) := None.
(** [] *)

(* ----------------------------------------------------------------- *)
(** *** Optional Pumping Exercise  *)

(** **** Exercise: 3 stars, advanced, optional (pumping_redux_strong)

    Use [auto], [lia], [repeat], [;], [try], etc. to shorten the official proof
    of the stronger Pumping Lemma optional exercise from [IndProp]. *)

Lemma pumping : forall T (re : reg_exp T) s,
    s =~ re ->
    pumping_constant re <= length s ->
    exists s1 s2 s3,
      s = s1 ++ s2 ++ s3 /\
        s2 <> [] /\
        length s1 + length s2 <= pumping_constant re /\
        forall m, s1 ++ napp m s2 ++ s3 =~ re.
Proof.
  (* FILL IN HERE *) Admitted.
(* Do not modify the following line: *)
Definition manual_grade_for_pumping_redux_strong : option (nat*string) := None.
(** [] *)

End Exercises.

(* ################################################################# *)
(** * Searching For Hypotheses *)

(** The proof has become simpler, but there is still an annoying
    degree of repetition. Let's start by tackling the contradiction
    cases. Each of them occurs in a situation where we have both

      H1: beval st b = false

    and

      H2: beval st b = true

    as hypotheses.  The contradiction is evident, but demonstrating it
    is a little complicated: we have to locate the two hypotheses [H1]
    and [H2] and do a [rewrite] following by a [discriminate].  We'd
    like to automate this process.

    (In fact, Rocq has a built-in tactic [congruence] that will do the
    job in this case.  We'll ignore this tactic for now, in order to
    demonstrate how to build forward-search tactics by hand.)

    As a first step, we can abstract out the piece of script in
    question by writing a little function in Ltac. *)

Ltac rwd H1 H2 := rewrite H1 in H2; discriminate.

Theorem ceval_deterministic'': forall c st st1 st2,
  st =[ c ]=> st1  ->
  st =[ c ]=> st2 ->
  st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2;
  induction E1; intros st2 E2; inversion E2; subst; auto.
  - (* E_Seq *)
    rewrite (IHE1_1 st'0 H1) in *.
    auto.
  - (* E_IfTrue *)
    rwd H H5.                 (* <----- *)
  - (* E_IfFalse *)
    rwd H H5.                 (* <----- *)
  - (* E_WhileFalse *)
    rwd H H2.                 (* <----- *)
  - (* E_WhileTrue - b false *)
    rwd H H4.                 (* <----- *)
  - (* EWhileTrue - b true *)
    rewrite (IHE1_1 st'0 H3) in *.
    auto. Qed.

(** That's a bit better, but we really want Rocq to discover the
    relevant hypotheses for us.  We can do this by using the [match
    goal] facility of Ltac. *)

Ltac find_rwd :=
  match goal with
    H1: ?E = true, H2: ?E = false |- _
       =>
    rwd H1 H2
  end.

(** This [match goal] looks for two distinct hypotheses that
    have the form of equalities, with the same arbitrary expression
    [E] on the left and with conflicting boolean values on the right.
    If such hypotheses are found, it binds [H1] and [H2] to their
    names and applies the [rwd] tactic to [H1] and [H2].

    Adding this tactic to the ones that we invoke in each case of the
    induction handles all of the contradictory cases. *)

Theorem ceval_deterministic''': forall c st st1 st2,
  st =[ c ]=> st1  ->
  st =[ c ]=> st2 ->
  st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2;
  induction E1; intros st2 E2; inversion E2; subst;
       try find_rwd;                                  (* <------ *)
       auto.
  - (* E_Seq *)
    rewrite (IHE1_1 st'0 H1) in *.
    auto.
  - (* E_WhileTrue - b true *)
    rewrite (IHE1_1 st'0 H3) in *.
    auto. Qed.

(** Let's see about the remaining cases. Each of them involves
    rewriting a hypothesis after feeding it with the required
    condition. We can automate the task of finding the relevant
    hypotheses to rewrite with. *)

Ltac find_eqn :=
  match goal with
    H1: forall x, ?P x -> ?L = ?R,
    H2: ?P ?X
    |- _
    => rewrite (H1 X H2) in *
  end.

(** The pattern [forall x, ?P x -> ?L = ?R] matches any hypothesis of
    the form "for all [x], _some property of [x]_ implies _some
    equality_."  The property of [x] is bound to the pattern variable
    [P], and the left- and right-hand sides of the equality are bound
    to [L] and [R].  The name of this hypothesis is bound to [H1].
    Then the pattern [?P ?X] matches any hypothesis that provides
    evidence that [P] holds for some concrete [X].  If both patterns
    succeed, we apply the [rewrite] tactic (instantiating the
    quantified [x] with [X] and providing [H2] as the required
    evidence for [P X]) in all hypotheses and the goal. *)



Theorem ceval_deterministic'''': forall c st st1 st2,
  st =[ c ]=> st1  ->
  st =[ c ]=> st2 ->
  st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2;
  induction E1; intros st2 E2; inversion E2; subst;
    try find_rwd;
    try find_eqn;    (* <------- *)
    auto.
Qed.

(** The big payoff in this approach is that the new proof script is
    more robust in the face of changes to our language.  To test this,
    let's try adding a [REPEAT] command to the language. *)

Module Repeat.

Inductive com : Type :=
  | CSkip
  | CAsgn (x : string) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com)
  | CRepeat (c : com) (b : bexp).

(** [REPEAT] behaves like [while], except that the loop guard is
    checked _after_ each execution of the body, with the loop
    repeating as long as the guard stays _false_.  Because of this,
    the body will always execute at least once. *)

Notation "'repeat' x 'until' y 'end'" :=
         (CRepeat x y)
            (in custom com at level 0,
             x at level 99, y at level 99).
Notation "'skip'"  :=
         CSkip (in custom com at level 0).
Notation "x := y"  :=
         (CAsgn x y)
            (in custom com at level 0, x constr at level 0,
             y at level 85, no associativity).
Notation "x ; y" :=
         (CSeq x y)
           (in custom com at level 90, right associativity).
Notation "'if' x 'then' y 'else' z 'end'" :=
         (CIf x y z)
           (in custom com at level 89, x at level 99,
            y at level 99, z at level 99).
Notation "'while' x 'do' y 'end'" :=
         (CWhile x y)
            (in custom com at level 89, x at level 99, y at level 99).

Reserved Notation "st '=[' c ']=>' st'"
         (at level 40, c custom com at level 99, st' constr at next level).

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      st =[ skip ]=> st
  | E_Asgn  : forall st a1 n x,
      aeval st a1 = n ->
      st =[ x := a1 ]=> (x !-> n ; st)
  | E_Seq : forall c1 c2 st st' st'',
      st  =[ c1 ]=> st'  ->
      st' =[ c2 ]=> st'' ->
      st  =[ c1 ; c2 ]=> st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> st' ->
      st =[ if b then c1 else c2 end ]=> st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> st' ->
      st =[ if b then c1 else c2 end ]=> st'
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ while b do c end ]=> st
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      st  =[ c ]=> st' ->
      st' =[ while b do c end ]=> st'' ->
      st  =[ while b do c end ]=> st''
  | E_RepeatEnd : forall st st' b c,
      st  =[ c ]=> st' ->
      beval st' b = true ->
      st  =[ repeat c until b end ]=> st'
  | E_RepeatLoop : forall st st' st'' b c,
      st  =[ c ]=> st' ->
      beval st' b = false ->
      st' =[ repeat c until b end ]=> st'' ->
      st  =[ repeat c until b end ]=> st''

  where "st =[ c ]=> st'" := (ceval c st st').

(** Our first attempt at the determinacy proof does not quite succeed:
    the [E_RepeatEnd] and [E_RepeatLoop] cases are not handled by our
    previous automation. *)

Theorem ceval_deterministic: forall c st st1 st2,
  st =[ c ]=> st1  ->
  st =[ c ]=> st2 ->
  st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2;
  induction E1;
    intros st2 E2; inversion E2; subst; try find_rwd; try find_eqn; auto.
  - (* E_RepeatEnd *)
    + (* b evaluates to false (contradiction) *)
       find_rwd.
       (* oops: why didn't [find_rwd] solve this for us already?
          answer: we did things in the wrong order. *)
  - (* E_RepeatLoop *)
     + (* b evaluates to true (contradiction) *)
        find_rwd.
Qed.

(** Fortunately, to fix this, we just have to swap the invocations of
    [find_eqn] and [find_rwd]. *)

Theorem ceval_deterministic': forall c st st1 st2,
  st =[ c ]=> st1  ->
  st =[ c ]=> st2 ->
  st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2;
  induction E1;
    intros st2 E2; inversion E2; subst; try find_eqn; try find_rwd; auto.
Qed.

End Repeat.

(** These examples just give a flavor of what "hyper-automation"
    can achieve in Rocq.  The details of [match goal] are a bit
    tricky (and debugging scripts using it is, frankly, not very
    pleasant).  But it is well worth adding at least simple uses to
    your proofs, both to avoid tedium and to "future proof" them. *)

(* ################################################################# *)
(** * The [eapply] and [eauto] tactics *)

(** To close the chapter, let's look at one more convenience
    feature of Rocq: its ability to delay instantiation of
    quantifiers.  To motivate this feature, recall this example from
    the [Imp] chapter: *)

Example ceval_example1:
  empty_st =[
    X := 2;
    if (X <= 1)
      then Y := 3
      else Z := 4
    end
  ]=> (Z !-> 4 ; X !-> 2).
Proof.
  (* We supply the intermediate state [st']... *)
  apply E_Seq with (st' := X !-> 2).
  - apply E_Asgn. reflexivity.
  - apply E_IfFalse.
    + reflexivity.
    + apply E_Asgn. reflexivity.
Qed.


(** In the first step of the proof, we had to explicitly provide a
    longish expression to help Rocq instantiate a "hidden" argument to
    the [E_Seq] constructor.  This was needed because the definition
    of [E_Seq]...

          E_Seq : forall c1 c2 st st' st'',
            st  =[ c1 ]=> st'  ->
            st' =[ c2 ]=> st'' ->
            st  =[ c1 ; c2 ]=> st''

   is quantified over a variable, [st'], that does not appear in its
   conclusion, so unifying its conclusion with the goal state doesn't
   help Rocq find a suitable value for this variable.  If we leave
   out the [with], this step fails ("Error: Unable to find an
   instance for the variable [st']").

   What's silly about this error is that the appropriate value for
   [st'] will actually become obvious in the very next step, where we
   apply [E_Asgn].  If Rocq could just wait until we get to this step,
   there would be no need for us to give the value explicitly.  This
   is exactly what the [eapply] tactic allows: *)

Example ceval'_example1:
  empty_st =[
    X := 2;
    if (X <= 1)
      then Y := 3
      else Z := 4
    end
  ]=> (Z !-> 4 ; X !-> 2).
Proof.
  (* 1 *) eapply E_Seq. (* introduces [?st'] existential variable *)
  - (* 2 *) apply E_Asgn. (* instantiates [?st'] with [X !-> ?n];
                       using a fresh existential variable [?n] *)
    (* 3 *) simpl. reflexivity. (* instantiates [?n] with [2] *)
  - (* 4 *) apply E_IfFalse.
    + reflexivity.
    + apply E_Asgn. reflexivity.
Qed.

(** The [eapply H] tactic behaves just like [apply H] except
    that, after it finishes unifying the goal state with the
    conclusion of [H], it skips checking whether all the variables
    that were introduced in the process have been given concrete
    values during unification.

    If you step through the proof above, you'll see that the goal
    state at position [1] mentions the _existential variable_ [?st']
    in both of the generated subgoals.  The next step (which gets us
    to position [2]) replaces [?st'] with a concrete value.  This new
    value contains a new existential variable [?n], which is
    instantiated in its turn by the following [reflexivity] step,
    position [3].  When we start working on the second subgoal
    (position [4]), we observe that the occurrence of [?st'] in this
    subgoal has been replaced by the value that it was given during
    the first subgoal. *)

(** Several of the tactics that we've seen so far, including [exists],
    [constructor], and [auto], have variants similar to [eapply]. *)

(** For instance, in addition to [exists] Rocq also provides an
    [eexists] tactic. To prove a goal of the form [exists x, P x], the
    [exists t] tactic requires us to supply a concrete term [t],
    changing the goal to [P t]. The [eexists] tactic instead
    introduces a fresh existential variable [?x] in its place, leaving
    us with the goal [P ?x]. The value of [?x] has to be determined by
    unification in some later proof step. *)

Example eexists_example : exists s',
  (Y !-> 1 ; X !-> 2) =[
    if (X <= Y)
      then Z := Y - X
      else Y := X + Z
    end
  ]=> s'.
Proof.
  eexists. eapply E_IfFalse.
  - reflexivity.
  - eapply E_Asgn. reflexivity.
Qed.

(** Similarly, [econstructor] is to [constructor] what [eapply] is to
    [apply].  In the proof of [ceval'_example1], we could have written
    [econstructor] in place of [eapply E_Seq]: Rocq would pick the
    matching constructor ([E_Seq]) and leave the intermediate state as
    an existential variable, to be determined by a later step. Here is
    that proof again, using [econstructor]. *)

Example econstructor_example :
  empty_st =[
    X := 2;
    if (X <= 1)
      then Y := 3
      else Z := 4
    end
  ]=> (Z !-> 4 ; X !-> 2).
Proof.
  econstructor.
  - apply E_Asgn. reflexivity.
  - apply E_IfFalse.
    + reflexivity.
    + apply E_Asgn. reflexivity.
Qed.

(** The [eauto] tactic works like [auto], except that it uses [eapply]
    instead of [apply]. Before using it in an example, we give some
    hints to [eauto] about using the constructors of [ceval] and the
    definitions of [state] and [total_map] as part of its proof search. *)

Hint Constructors ceval : core.
(* HIDE CH: I think better would be to choose another example that
   doesn't need `Hint Transparent` *)
Hint Transparent state total_map : core.

Example eauto_example : exists s',
  (Y !-> 1 ; X !-> 2) =[
    if (X <= Y)
      then Z := Y - X
      else Y := X + Z
    end
  ]=> s'.
Proof. info_eauto. Qed.

(** [info_eauto] shows us which facts [eauto] uses. *)

(** Pro tip: One might think that, since [eapply] and [eauto]
    are more powerful than [apply] and [auto], we should just use them
    all the time.  Unfortunately, they are also significantly slower
    -- especially [eauto].  Rocq experts tend to use [apply] and [auto]
    most of the time, only switching to the [e] variants when the
    ordinary variants don't do the job. *)

(* ################################################################# *)
(** * Constraints on Existential Variables *)

(** In order for [Qed] to succeed, all existential variables need to
    be determined by the end of the proof. Otherwise Rocq
    will (rightly) refuse to accept the proof. Remember that the Rocq
    tactics build proof objects, and proof objects containing
    existential variables are not complete. *)

Lemma silly1 : forall (P : nat -> nat -> Prop) (Q : nat -> Prop),
  (forall x y : nat, P x y) ->
  (forall x y : nat, P x y -> Q x) ->
  Q 42.
Proof.
  intros P Q HP HQ. eapply HQ. apply HP. Unshelve. exact 0.
(** Rocq gives a warning after [apply HP]: "All the remaining goals
    are on the shelf," means that we've finished all our top-level
    proof obligations but along the way we've put some aside to be
    done later, and we have not finished those.  Trying to close the
    proof with [Qed] would yield an error. (Try it!) *)
Abort.

(** An additional constraint is that existential variables cannot be
    instantiated with terms containing ordinary variables that did not
    exist at the time the existential variable was created.  (The
    reason for this technical restriction is that allowing such
    instantiation would lead to inconsistency of Rocq's logic.) *)

Lemma silly2 :
  forall (P : nat -> nat -> Prop) (Q : nat -> Prop),
  (exists y, P 42 y) ->
  (forall x y : nat, P x y -> Q x) ->
  Q 42.
Proof.
  intros P Q HP HQ. eapply HQ. destruct HP as [y HP'].
  Fail apply HP'.

(** The error we get, with some details elided, is:

      cannot instantiate "?y" because "y" is not in its scope

    In this case there is an easy fix: doing [destruct HP] _before_
    doing [eapply HQ]. *)
Abort.

Lemma silly2_fixed :
  forall (P : nat -> nat -> Prop) (Q : nat -> Prop),
  (exists y, P 42 y) ->
  (forall x y : nat, P x y -> Q x) ->
  Q 42.
Proof.
  intros P Q HP HQ. destruct HP as [y HP'].
  eapply HQ. apply HP'.
Qed.

(** The [apply HP'] in the last step unifies the existential variable
    in the goal with the variable [y].

    Note that the [assumption] tactic doesn't work in this case, since
    it cannot handle existential variables.  However, Rocq also
    provides an [eassumption] tactic that solves the goal if one of
    the premises matches the goal up to instantiations of existential
    variables. We can use it instead of [apply HP'] if we like. *)

Lemma silly2_eassumption : forall (P : nat -> nat -> Prop) (Q : nat -> Prop),
  (exists y, P 42 y) ->
  (forall x y : nat, P x y -> Q x) ->
  Q 42.
Proof.
  intros P Q HP HQ. destruct HP as [y HP']. eapply HQ. eassumption.
Qed.

(** The [eauto] tactic will use [eapply] and [eassumption], streamlining
    the proof even further. *)

Lemma silly2_eauto : forall (P : nat -> nat -> Prop) (Q : nat -> Prop),
  (exists y, P 42 y) ->
  (forall x y : nat, P x y -> Q x) ->
  Q 42.
Proof.
  intros P Q HP HQ. destruct HP as [y HP']. eauto.
Qed.

(* ################################################################# *)
(** * Solver for Equalities: The [congruence] Tactic *)

(** Rocq has several special-purpose tactics that can solve certain
    kinds of goals automatically, based on algorithms for specific
    mathematical or logical domains. One of these tactics, [lia],
    were already introduced in [Imp], and here we will
    learn one more: [congruence].  *)

(** The [lia] tactic makes use of facts about addition and
    multiplication to prove equalities. A more basic way of treating
    such formulas is to regard every function appearing in them as
    a black box: nothing is known about the function's behavior.
    Based on the properties of equality itself, it is still possible
    to prove some formulas. For example, [y = f x -> g y = g (f x)],
    even if we know nothing about [f] or [g]: *)

Theorem eq_example1 :
  forall (A B C : Type) (f : A -> B) (g : B -> C) (x : A) (y : B),
    y = f x -> g y = g (f x).
Proof.
  intros. rewrite H. reflexivity.
Qed.

(** The essential properties of equality are that it is:

    - reflexive

    - symmetric

    - transitive

    - a _congruence_: it respects function and predicate
      application. *)

(** It is that congruence property that we're using when we
    [rewrite] in the proof above: if [a = b] then [f a = f b].  (The
    [ProofObjects] chapter explores this idea further under the
    name "Leibniz equality".) *)

(** The [congruence] tactic is a decision procedure for equality with
    uninterpreted functions and other symbols.  *)

Theorem eq_example1' :
  forall (A B C : Type) (f : A -> B) (g : B -> C) (x : A) (y : B),
    y = f x -> g y = g (f x).
Proof.
  congruence.
Qed.

(** The [congruence] tactic is able to work with constructors,
    even taking advantage of their injectivity and distinctness. *)

Theorem eq_example2 : forall (n m o p : nat),
    (n, o) = (m, p) ->
    n = m.
Proof.
  congruence.
Qed.

Theorem eq_example3 : forall (X : Type) (h : X) (t : list X),
    nil <> h :: t.
Proof.
  congruence.
Qed.

(** This gives us another way to simplify our determinism proof,
    which gets quite short even without using custom tactics: *)

Theorem ceval_deterministic_congruence: forall c st st1 st2,
  st =[ c ]=> st1  ->
  st =[ c ]=> st2 ->
  st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2.
  induction E1; intros st2 E2;
    inversion E2; subst;
    auto;
    try congruence. (* <---- this solves 4 cases, previously proved
                             by rewrite and discriminate *)
  - (* E_Seq *)
    rewrite (IHE1_1 st'0 H1) in *.
    auto.
  - (* E_WhileTrue, with b true *)
    rewrite (IHE1_1 st'0 H3) in *.
    auto.
Qed.

(** **** Exercise: 2 stars, standard (automatic_solvers)

    The exercises below could be proved with (relatively) long manual
    proof scripts, but each can be solved with just a single
    invocation of an automatic solver we learned about ([congruence]
    or [lia]). *)

Theorem cons_equal : forall {X} (n m: X) (l: list X),
    n = m -> n :: l = m :: l.
Proof. (* FILL IN HERE *) Admitted.

Theorem plus_le_cancel_r : forall n m p : nat,
    n + p <= m + p -> n <= m.
Proof. (* FILL IN HERE *) Admitted.

Theorem no_half : forall n,
    2 * n <> 1.
Proof. (* FILL IN HERE *) Admitted.

Theorem pair_equal : forall {X} (a b c d: X) (e: X * X),
    (a, (b, c)) = (d, e) ->
    e = (d, c) ->
    b = d.
Proof. (* FILL IN HERE *) Admitted.
(** [] *)


(* 2026-08-24 10:03 *)
