(** * AltAuto: More Automation *)

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Lia
                        Arith.
From LF Require Import IndProp.

(** Up to now, we've used the more manual part of Coq's tactic
    facilities.  In this chapter, we'll learn more about some of Coq's
    powerful automation features.

    As a simple illustration of the benefits of automation, let's
    consider another problem on regular expressions, which we
    formalized in [IndProp].  A given set of strings can be
    denoted by many different regular expressions.  For example, [App
    EmptyString re] matches exactly the same strings as [re].  We can
    write a function that "optimizes" any regular expression into a
    potentially simpler one by applying this fact throughout the
    r.e.  (Note that, for simplicity, the function does not optimize
    expressions that arise as the result of other optimizations.) *)

Fixpoint re_opt_e {T:Type} (re: reg_exp T) : reg_exp T :=
  match re with
  | App EmptyStr re2 => re_opt_e re2
  | App re1 re2 => App (re_opt_e re1) (re_opt_e re2)
  | Union re1 re2 => Union (re_opt_e re1) (re_opt_e re2)
  | Star re => Star (re_opt_e re)
  | _ => re
  end.

(** We would like to show the equivalence of re's with their "optimized" form.
One direction of this equivalence looks like this (the other is similar).
*)

Lemma re_opt_e_match : forall T (re: reg_exp T) s,
  s =~ re -> s =~ re_opt_e re.
Proof.
  intros T re s M.
  induction M
    as [| x'
        | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
        | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
        | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2].
  - (* MEmpty *) simpl. apply MEmpty.
  - (* MChar *) simpl. apply MChar.
  - (* MApp *) simpl.
    destruct re1.
    + apply MApp. apply IH1. apply IH2.
    + inversion Hmatch1. simpl.  apply IH2.
    + apply MApp. apply IH1. apply IH2.
    + apply MApp. apply IH1. apply IH2.
    + apply MApp. apply IH1. apply IH2.
    + apply MApp. apply IH1. apply IH2.
  - (* MUnionL *) simpl. apply MUnionL. apply IH.
  - (* MUnionR *) simpl. apply MUnionR. apply IH.
  - (* MStar0 *) simpl. apply MStar0.
  - (* MStarApp *) simpl. apply MStarApp. apply IH1.  apply IH2.
Qed.

(* ################################################################# *)
(** * Coq Automation *)

(** The amount of repetition in this last proof is rather
    annoying.  And if we wanted to extend the optimization function to
    handle other, similar, rewriting opportunities,
    it would start to be a real problem.

    So far, we've been doing all our proofs using just a small handful
    of Coq's tactics and completely ignoring its powerful facilities
    for constructing parts of proofs automatically.  This section
    introduces some of these facilities, and we will see more over the
    next several chapters.  Getting used to them will take some
    energy -- Coq's automation is a power tool -- but it will allow us
    to scale up our efforts to more complex definitions and more
    interesting properties without becoming overwhelmed by boring,
    repetitive, low-level details. *)

(* ################################################################# *)
(** * Tacticals *)

(** _Tacticals_ is Coq's term for tactics that take other tactics as
    arguments -- "higher-order tactics," if you will.  *)

(* ----------------------------------------------------------------- *)
(** *** The [try] Tactical *)

(** If [T] is a tactic, then [try T] is a tactic that is just like [T]
    except that, if [T] fails, [try T] _successfully_ does nothing at
    all (instead of failing). *)

Theorem silly1 : forall n,  1 + n = S n.
Proof. try reflexivity. (* this just does [reflexivity] *) Qed.

Theorem silly2 : forall (P : Prop), P -> P.
Proof.
  intros P HP.
  try reflexivity. (* just [reflexivity] would have failed *)
  apply HP. (* we can still finish the proof in some other way *)
Qed.

(** There is no real reason to use [try] in completely manual
    proofs like these, but it is very useful for doing automated
    proofs in conjunction with the [;] tactical, which we show
    next. *)

(* ----------------------------------------------------------------- *)
(** *** The [;] Tactical (Simple Form) *)

(** In its most common form, the [;] tactical takes two tactics as
    arguments.  The compound tactic [T;T'] first performs [T] and then
    performs [T'] on _each subgoal_ generated by [T]. *)

(** For example, consider the following trivial lemma: *)

Lemma foo : forall n,  n+1 =? 0 = false.
Proof.
  intros.
  destruct n eqn:E.
    (* Leaves two subgoals, which are discharged identically...  *)
    - (* n=0 *) simpl. reflexivity.
    - (* n=Sn' *) simpl. reflexivity.
Qed.

(** We can simplify this proof using the [;] tactical: *)

Lemma foo' : forall n, n+1 =? 0 = false.
Proof.
  intros.
  (* [destruct] the current goal *)
  destruct n;
  (* then [simpl] each resulting subgoal *)
  simpl;
  (* and do [reflexivity] on each resulting subgoal *)
  reflexivity.
Qed.

(** Using [try] and [;] together, we can get rid of the repetition in
    the proof that was bothering us a little while ago. *)

Lemma re_opt_e_match' : forall T (re: reg_exp T) s,
  s =~ re -> s =~ re_opt_e re.
Proof.
  intros T re s M.
  induction M
    as [| x'
        | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
        | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
        | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2];
    (* Do the [simpl] for every case here: *)
    simpl.
  - (* MEmpty *) apply MEmpty.
  - (* MChar *) apply MChar.
  - (* MApp *)
    destruct re1;
    (* Most cases follow by the same formula.
       Notice that [apply MApp] gives two subgoals:
       [try apply H1] is run on both of them and
       succeeds on the first but not the second;
       [apply H2] is then run on this remaining goal. *)
    try (apply MApp; try apply IH1; apply IH2).
    (* The interesting case, on which [try...] does nothing,
       is when [re1 = EmptyStr]. In this case, we have
       to appeal to the fact that [re1] matches only the
       empty string: *)
    inversion Hmatch1. simpl. apply IH2.
  - (* MUnionL *) apply MUnionL. apply IH.
  - (* MUnionR *) apply MUnionR. apply IH.
  - (* MStar0 *) apply MStar0.
  - (* MStarApp *)  apply MStarApp. apply IH1.  apply IH2.
Qed.



(* ----------------------------------------------------------------- *)
(** *** The [;] Tactical (General Form) *)

(** The [;] tactical also has a more general form than the simple
    [T;T'] we've seen above.  If [T], [T1], ..., [Tn] are tactics,
    then

      T; [T1 | T2 | ... | Tn]

    is a tactic that first performs [T] and then performs [T1] on the
    first subgoal generated by [T], performs [T2] on the second
    subgoal, etc.

    So [T;T'] is just special notation for the case when all of the
    [Ti]'s are the same tactic; i.e., [T;T'] is shorthand for:

      T; [T' | T' | ... | T']

*)

(* We can use this mechanism to give a slightly neater version
of our optimization proof: *)

Lemma re_opt_e_match'' : forall T (re: reg_exp T) s,
  s =~ re -> s =~ re_opt_e re.
Proof.
  intros T re s M.
  induction M
    as [| x'
        | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
        | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
        | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2];
    (* Do the [simpl] for every case here: *)
    simpl.
  - (* MEmpty *) apply MEmpty.
  - (* MChar *) apply MChar.
  - (* MApp *)
    destruct re1;
    try (apply MApp; [apply IH1 | apply IH2]).  (* <=== *)
    inversion Hmatch1. simpl. apply IH2.
  - (* MUnionL *) apply MUnionL. apply IH.
  - (* MUnionR *) apply MUnionR. apply IH.
  - (* MStar0 *) apply MStar0.
  - (* MStarApp *)  apply MStarApp; [apply IH1 |  apply IH2].  (* <=== *)
Qed.

(* ----------------------------------------------------------------- *)
(** *** The [repeat] Tactical *)

(** The [repeat] tactical takes another tactic and keeps applying this
    tactic until it fails or stops making progress. Here is an example 
    showing that [10] is in a long list using repeat. *)

Theorem In10 : In 10 [1;2;3;4;5;6;7;8;9;10].
Proof.
  repeat (try (left; reflexivity); right).
Qed.

(** The tactic [repeat T] never fails: if the tactic [T] doesn't apply
    to the original goal, then repeat still succeeds without changing
    the original goal (i.e., it repeats zero times). *)

Theorem In10' : In 10 [1;2;3;4;5;6;7;8;9;10].
Proof.
  repeat (left; reflexivity).
  repeat (right; try (left; reflexivity)).
Qed.

(** The tactic [repeat T] also does not have any upper bound on the
    number of times it applies [T].  If [T] is a tactic that always
    succeeds, then repeat [T] will loop forever (e.g., [repeat simpl]
    loops, since [simpl] always succeeds).  While evaluation in Coq's
    term language, Gallina, is guaranteed to terminate, tactic
    evaluation is not!  This does not affect Coq's logical
    consistency, however, since the job of [repeat] and other tactics
    is to guide Coq in constructing proofs; if the construction
    process diverges, this simply means that we have failed to
    construct a proof, not that we have constructed a wrong one. *)

(** **** Exercise: 3 stars, standard (re_opt) *)

(** Consider this more powerful version of the regular expression optimizer. *)

Fixpoint re_opt {T:Type} (re: reg_exp T) : reg_exp T :=
  match re with
  | App re1 EmptySet => EmptySet
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

(* Here is an incredibly tedious manual proof of (one direction of) its correctness: *)

Lemma re_opt_match : forall T (re: reg_exp T) s,
  s =~ re -> s =~ re_opt re.
Proof.
  intros T re s M.
  induction M
    as [| x'
        | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
        | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
        | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2].
  - simpl. apply MEmpty.
  - simpl. apply MChar.
  - simpl.
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
      * apply MApp. apply IH1. apply IH2.
      * apply MApp. apply IH1. apply IH2.
      * apply MApp. apply IH1. apply IH2.
      * apply MApp. apply IH1. apply IH2.
    + destruct re2.
      * inversion IH2.
      * inversion IH2. rewrite app_nil_r.  apply IH1.
      * apply MApp. apply IH1. apply IH2.
      * apply MApp. apply IH1.  apply IH2.
      * apply MApp. apply IH1.  apply IH2.
      * apply MApp. apply IH1.  apply IH2.
    + destruct re2.
      * inversion IH2.
      * inversion IH2. rewrite app_nil_r. apply IH1.
      * apply MApp. apply IH1.  apply IH2.
      * apply MApp. apply IH1.  apply IH2.
      * apply MApp. apply IH1.  apply IH2.
      * apply MApp. apply IH1.  apply IH2.
    + destruct re2.
      * inversion IH2.
      * inversion IH2. rewrite app_nil_r. apply IH1.
      * apply MApp. apply IH1.  apply IH2.
      * apply MApp. apply IH1.  apply IH2.
      * apply MApp. apply IH1.  apply IH2.
      * apply MApp. apply IH1.  apply IH2.
  - simpl.
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
  - simpl.
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
 - simpl.
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
 - simpl.
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

(* Use the automation tools described so far to shorten the proof. *)

Lemma re_opt_match' : forall T (re: reg_exp T) s,
  s =~ re -> s =~ re_opt re.
Proof.
(* FILL IN HERE *) Admitted.
(* Do not modify the following line: *)
Definition manual_grade_for_re_opt : option (nat*string) := None.
(** [] *)

(* ================================================================= *)
(** ** A Few More Handy Tactics *)

(** By the way, here are some miscellaneous tactics that you may find
    convenient as we continue.

     - [clear H]: Delete hypothesis [H] from the context.

     - [rename... into...]: Change the name of a hypothesis in the
       proof context.  For example, if the context includes a variable
       named [x], then [rename x into y] will change all occurrences
       of [x] to [y].

     - [subst x]: Find an assumption [x = e] or [e = x] in the
       context, replace [x] with [e] throughout the context and
       current goal, and clear the assumption.

     - [subst]: Substitute away _all_ assumptions of the form [x = e]
       or [e = x].

    We'll see examples as we go along. *)

(* ================================================================= *)
(** ** Defining New Tactics *)

(** Coq also provides several ways of "programming" tactic
scripts.

    - Coq has a built-in language called [Ltac] with primitives that
      can examine and modify the proof state.  The full details are a
      bit too complicated to get into here (and it is generally agreed
      that [Ltac] is not the most beautiful part of Coq's design!),
      but they can be found in the reference manual and other books on
      Coq. Simple use cases are not too difficult.

    - There is also an OCaml API, which can be used to build tactics
      that access Coq's internal structures at a lower level, but this
      is seldom worth the trouble for ordinary Coq users.
*)

(**    Here is a simple [Ltac] example: *)

Ltac impl_and_try c := simpl; try c.

(** This defines a new tactical called [simpl_and_try] that takes one
    tactic [c] as an argument and is defined to be equivalent to the
    tactic [simpl; try c].  Now writing "[simpl_and_try reflexivity.]"
    in a proof will be the same as writing "[simpl; try
    reflexivity.]" *)

(* ################################################################# *)
(** * Decision Procedures *)

(** So far, the automation we have considered has primarily been
    useful for removing repetition. Another important category of
    automation consists of built-in decision procedures for specific
    kinds of problems.  There are several of these, but the [lia]
    tactic is the most important to start with. *)

(* ================================================================= *)
(** ** The [lia] Tactic *)

(** The [lia] tactic implements a decision procedure for integer linear
    arithmetic, a subset of propositional logic and arithmetic. 

    If the goal is a formula made out of

      - variables and constants of type [nat] (or other integer types)

      - numeric constants, addition ([+] and [S]), subtraction ([-]
        and [pred]), and multiplication by constants 
        (this is what makes it linear arithmetic) 

      - equality ([=] and [<>]) and ordering ([<=]), and

      - the logical connectives [/\], [\/], [~], [->], and [<->].

    then invoking [lia] will either solve the goal or fail, meaning
    that the goal is actually false.  (If the goal is _not_ of this
    form, [lia] will also fail.) *)

Example silly_lia_example : forall m n o p,
  m + n <= n + o /\ o + 3 = p + 3 ->
  m <= p.
Proof.
  intros. lia.
Qed.

(* ################################################################# *)
(** * Search Tactics *)

(** Another very important category of automation tactics
    helps us construct proofs by _searching_ for relevant facts
    These tactics include the [auto] tactic for backwards reasoning,
    automated forward reasoning via the [Ltac] hypothesis matching
    machinery, and deferred instantiation of existential variables
    using [eapply] and [eauto].  Using these features together with
    Ltac's scripting facilities will enable us to make our proofs
    startlingly short!  Used properly, they can also make proofs more
    maintainable and robust to changes in underlying definitions.  A
    deeper treatment of [auto] and [eauto] can be found in the
    [UseAuto] chapter in _Programming Language Foundations_. *)

(* ================================================================= *)
(** ** The [constructor] tactic. *)

(** A simple first example of a search tactic is [constructor],
    which tries to find a constructor [c] (from some
    [Inductive] definition in the current environment) that can be
    applied to solve the current goal.  If one is found, behave
    like [apply c]. *)

Print ev.
(* ===> 
   Inductive ev : nat -> Prop :=
    ev_0 : ev 0 
  | ev_SS : forall n : nat, ev n -> ev (S (S n))
*)

Example constructor_example: forall (n:nat),
    ev (n+n).
Proof.
  induction n; simpl.
  - constructor. (* applies ev_0 *)
  - rewrite add_comm. simpl. constructor. (* applies ev_SS *) auto.
Qed.

(** This saves us from needing to remember the names of our constructors.
    Warning: if more than one constructor can apply, [constructor] picks
    the first one (in the order in which they were defined in the [Inductive])
    which is not necessarily the one we want! *)

(* ================================================================= *)
(** ** The [auto] Tactic *)

(** Thus far, our proof scripts mostly apply relevant hypotheses or
    lemmas by name, and one at a time. *)

Example auto_example_1 : forall (P Q R: Prop),
  (P -> Q) -> (Q -> R) -> P -> R.
Proof.
  intros P Q R H1 H2 H3.
  apply H2. apply H1. apply H3. 
Qed.

(** The [auto] tactic frees us from this drudgery by _searching_ for a
    sequence of applications that will prove the goal: *)

Example auto_example_1' : forall (P Q R: Prop),
  (P -> Q) -> (Q -> R) -> P -> R.
Proof.
  auto.
Qed.

(** The [auto] tactic solves goals that are solvable by any combination of
     - [intros] and
     - [apply] (of hypotheses from the local context, by default). *)

(** Using [auto] is always "safe" in the sense that it will never fail
    and will never change the proof state: either it completely solves
    the current goal, or it does nothing. *)

(** Here is a more interesting example showing [auto]'s power: *)

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

(** Proof search could, in principle, take an arbitrarily long time,
    so there are limits to how far [auto] will search by default. *)

Example auto_example_3 : forall (P Q R S T U: Prop),
  (P -> Q) ->
  (Q -> R) ->
  (R -> S) ->
  (S -> T) ->
  (T -> U) ->
  P ->
  U.
Proof.
  (* When it cannot solve the goal, [auto] does nothing *)
  auto.
  (* Optional argument says how deep to search (default is 5) *)
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

(** If we want to see which facts [auto] is using, we can use
    [info_auto] instead. *)

Example auto_example_5: 2 = 2.
Proof.
  (* auto subsumes reflexivity because eq_refl is in hint database *)
  info_auto.
Qed.

(** We can extend the hint database just for the purposes of one
    application of [auto] by writing "[auto using ...]". *)

Lemma le_antisym : forall n m: nat, (n <= m /\ m <= n) -> n = m.
Proof. intros. lia. Qed.

Example auto_example_6 : forall n m p : nat,
  (n <= p -> (n <= m /\ m <= n)) ->
  n <= p ->
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

    to tell Coq to do a [Hint Resolve] for _all_ of the constructors
    from the inductive definition of [c].

    It is also sometimes necessary to add

      Hint Unfold d : core.

    where [d] is a defined symbol, so that [auto] knows to expand uses
    of [d], thus enabling further possibilities for applying lemmas that
    it knows about. *)

(** It is also possible to define specialized hint databases that can
    be activated only when needed.  See the Coq reference manual for
    more. *)

Hint Resolve le_antisym : core.

Example auto_example_6' : forall n m p : nat,
  (n<= p -> (n <= m /\ m <= n)) ->
  n <= p ->
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
Proof. info_auto. Qed.


(** **** Exercise: 3 stars, advanced (pumping_redux)

    Use [auto], [lia], and any other useful tactics from this chapter to
    shorten your proof (or the "official" solution proof) of the weak Pumping
    Lemma exercise from [IndProp]. *)
Import Pumping.
Lemma weak_pumping : forall T (re : reg_exp T) s,
  s =~ re ->
  pumping_constant re <= length s ->
  exists s1 s2 s3,
    s = s1 ++ s2 ++ s3 /\
    s2 <> [] /\
    forall m, s1 ++ napp m s2 ++ s3 =~ re.
Proof.
(* FILL IN HERE *) Admitted.
(* Do not modify the following line: *)
Definition manual_grade_for_pumping_redux : option (nat*string) := None.
(** [] *)

(** **** Exercise: 3 stars, advanced, optional (pumping_redux_strong)

    Use [auto], [lia], and any other useful tactics from this chapter to
    shorten your proof (or the "official" solution proof) of the stronger
    Pumping Lemma exercise from [IndProp]. *)
Import Pumping.
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


(* ================================================================= *)
(** ** The [eapply] and [eauto] variants *)

(** To close the chapter, we'll introduce one more convenient feature
    of Coq: its ability to delay instantiation of quantifiers. To motivate
    this feature, consider again this simple example: *)

Example trans_example1:  forall a b c d,
    a <= b + b*c  ->
    (1+c)*b <= d ->
    a <= d.
Proof.
  intros a b c d H1 H2.
  apply le_trans with (b+ b*c).  (* <-- We must supply the intermediate value *)
  + apply H1.
  + simpl in H2. rewrite mul_comm. apply H2.
Qed.

(** In the first step of the proof, we had to explicitly provide a
    longish expression to help Coq instantiate a "hidden" argument to
    the [le_trans] constructor. This was needed because the definition
    of [le_trans]...

    le_trans : forall m n o : nat, m <= n -> n <= o -> m <= o

   is quantified over a variable, [n], that does not appear in its
   conclusion, so unifying its conclusion with the goal state doesn't
   help Coq find a suitable value for this variable.  If we leave
   out the [with], this step fails ("Error: Unable to find an
   instance for the variable [n]").

   We already know one way to avoid an explicit [with] clause, namely
   to provide [H1] as the (first) explicit argument to [le_trans].
   But here's another way, using the [eapply tactic]: *)

Example trans_example1':  forall a b c d,
    a <= b + b*c  ->
    (1+c)*b <= d ->
    a <= d.
Proof.
  intros a b c d H1 H2.
  eapply le_trans.  (* 1 *)
  + apply H1.  (* 2 *)
  + simpl in H2. rewrite mul_comm. apply H2.
Qed.

(** The [eapply H] tactic behaves just like [apply H] except
    that, after it finishes unifying the goal state with the
    conclusion of [H], it does not bother to check whether all the
    variables that were introduced in the process have been given
    concrete values during unification.

    If you step through the proof above, you'll see that the goal
    state at position [1] mentions the _existential variable_ [?n]
    in both of the generated subgoals.  The next step (which gets us
    to position [2]) replaces [?n] with a concrete value.  When we
    start working on the second subgoal (position [3]), we observe
    that the occurrence of [?n] in this subgoal has been replaced
    by the value that it was given during the first subgoal. *)

(** Several of the tactics that we've seen so far, including [exists],
    [constructor], and [auto], have [e...] variants.  For example,
    here's a proof using [eauto]: *)

Example trans_example2:  forall a b c d,
    a <= b + b*c  ->
    b + b*c <= d ->
    a <= d.
Proof.
  intros a b c d H1 H2.
  info_eauto using le_trans.
Qed.

(** The [eauto] tactic works just like [auto], except that it uses
    [eapply] instead of [apply].

    Pro tip: One might think that, since [eapply] and [eauto] are more
    powerful than [apply] and [auto], it would be a good idea to use
    them all the time.  Unfortunately, they are also significantly
    slower -- especially [eauto].  Coq experts tend to use [apply] and
    [auto] most of the time, only switching to the [e] variants when
    the ordinary variants don't do the job. *)

(* 2021-05-18 18:03 *)
