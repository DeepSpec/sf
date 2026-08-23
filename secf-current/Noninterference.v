(** * Noninterference: Defining Secrecy and Secure Multi-Execution *)

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Init.Nat.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Arith.EqNat. Import Nat.
Set Default Goal Selector "!".

(** Programmers have to be very careful about how information flows in
    the software they develop to prevent leaking secret data. For
    instance, in course management systems students shouldn't be able
    to obtain information about other students' grades or passwords. *)

(** Information-flow control tries to prevent leaking such secret
    information.  But how does one formalize that a program doesn't
    leak any information about the secret inputs to public outputs? *)

(** We first investigate this question of how to define secrecy in the
    very simple setting of Rocq functions taking two arguments, one we
    call the public input and the other one we call the secret
    input. Our functions return a pair where the first element is the
    public output and the second one the secret output. *)

(** Say we have the following function working on natural numbers: *)

Definition secure_f (pi si : nat) : nat*nat := (pi+1, pi+si*2).

(** This function seems intuitively secure, since the first output [pi+1], which
    we assume to be public, only depends on the public input [pi], but not on
    the secret input [si]. The second output [pi+si*2] depends on both the
    public input and the secret input, but that's okay, since we assume this
    second output to be secret. *)

(** Still, how can we mathematically define that this function is secure? *)

(* ################################################################# *)
(** * Naive attempt at defining secrecy *)

(** A naive security definition, which we'll only use as a
    strawman, is one that simply requires that the public output is
    different from the secret input, for all inputs of function [f]: *)

Definition broken_sec_def (f : nat -> nat -> nat*nat) :=
  forall pi si, fst (f pi si) <> si.

(** This broken definition would reject our [secure_f] above as
    insecure though. Here is a counterexample: *)

Example example_secure_f : secure_f 7 8 = (8,23).
Proof. reflexivity. Qed.

Lemma broken_sec_def_rejects_secure_f : ~broken_sec_def secure_f.
Proof. intros Hc. apply (Hc 7 8). reflexivity. Qed.

(** In this (spurious) counterexample the public output [8] happens to
    be equal to the value of the secret input [8]. But the secret
    input wasn't used at all in computing the public output. The
    public output was simply computed as [7+1], where [7] is the
    _public_ input. The fact that this returns the same value as the
    secret input is just a coincidence, not an information leak. *)

(** Even worse, this broken definition of security would allow _insecure_
    functions, such as the following one whose public output is [si+1]: *)

Definition insecure_f (pi si : nat) : nat*nat := (si+1, pi+si*2).

(** This function's public output is _never equal_ to its secret
    input, yet an attacker can easily compute one from the other by
    just subtracting [1]. So the secret is entirely leaked, yet our
    broken definition accepts this as secure: *)

Lemma broken_sec_def_accepts_insecure_f : broken_sec_def insecure_f.
Proof.
  unfold broken_sec_def. intros pi si. induction si as [| si' IH].
  - simpl. intros contra. discriminate contra.
  - simpl in *. intro Hc. injection Hc as Hc. apply IH. apply Hc.
Qed.

(** This naive attempt at defining secure information flow by looking at how
    inputs and outputs are related for a single execution of the
    program was a complete failure. In fact, it is well known in the
    formal security research community that secure information flow
    _cannot_ be defined by looking at just one single program execution. *)

(* ################################################################# *)
(** * Noninterference for pure functions *)

(** The simplest correct way to define secure information flow is a
    property called _noninterference_ [Sabelfeld and Myers 2003] (in Bib.v),
    which in its most standard form looks at _two_ program executions:
    for two different secret inputs the public outputs should not change: *)

Definition noninterferent {PI SI PO SO : Type} (f:PI->SI->PO*SO) :=
  forall (pi:PI) (si1 si2:SI), fst (f pi si1) = fst (f pi si2).

(** This definition prevents changes in secret inputs from changing the
    public outputs, so it prevents secret inputs from interfering with
    public outputs in any way. At the same time it allows secret
    inputs to influence secret outputs and also public inputs to
    influence both public and secret outputs:

                                ┌───╮
                                │ f │
                           pi ─>┼───┼─> po
                                │╲  │
                                │ ╲ │
                                │  ╲│
                           si ─>┼───┼─> so
                                └───╯
*)

(** The definition above states noninterference for arbitrary types
    of inputs and outputs, so we can instantiate them to [nat] when
    looking at our example functions above: *)

Print secure_f. (* fun pi si : nat => (pi + 1, pi + si * 2) *)

Lemma noninterferent_secure_f : noninterferent secure_f.
Proof. unfold noninterferent, secure_f. simpl. reflexivity. Qed.

Print insecure_f. (* fun pi si : nat => (si + 1, pi + si * 2) *)

Lemma interferent_insecure_f : ~noninterferent insecure_f.
Proof.
  (* WORKED IN CLASS *)
  unfold noninterferent. simpl. intros contra.
  specialize (contra 42 3 7). simpl in contra. discriminate contra.
Qed.

(** The [secure_f] function above is quite obviously noninterferent,
    because the expression [pi+1] computing the public output doesn't
    syntactically mention the secret input at all. Since
    noninterference is a semantic property though (not a syntactic
    one), functions where the expression computing the public output
    does syntactically mention the secret input can still be
    noninterferent. Here is a first example: *)

Definition less_obvious_f1 (pi si : nat) : nat*nat := (si * 0, pi+si).

(** This new function is noninterferent: since the public output is
    the constant [0], it can't depend on [si], even if it syntactically
    mentions it: *)

Lemma noninterferent_less_obvious_f1 : noninterferent less_obvious_f1.
Proof.
  unfold noninterferent, less_obvious_f1. intros pi si1 si2. simpl.
  rewrite <- mult_n_O. rewrite <- mult_n_O. reflexivity.
Qed.




(** Here is another example of a function that is noninterferent, even
    if this is not syntactically obvious: *)

Definition less_obvious_f2 (pi si : nat) : nat*nat :=
  (if si =? 1 then si*pi else pi, pi+si).

(** For proving this function noninterferent we first show that the
    public output of this function is in fact always equal to just its
    public input: *)

Lemma po_equal_pi_f2 : forall si pi, (if si =? 1 then si*pi else pi) = pi.
Proof.
  intros si pi. destruct (si =? 1) eqn:Eq.
  - apply Nat.eqb_eq in Eq. rewrite Eq.
    simpl. rewrite <- plus_n_O. reflexivity.
  - reflexivity.
Qed.

Lemma noninterferent_less_obvious_f2 : noninterferent less_obvious_f2.
Proof.
  unfold noninterferent, less_obvious_f2. intros pi si1 si2.
  rewrite po_equal_pi_f2. rewrite po_equal_pi_f2. simpl. reflexivity.
Qed.

(** Branching on a secret is dangerous, since one can
    easily leak the secret this way, even if both the [then] and the
    [else] branches are public constants. For instance the following
    function leaks whether [si] is zero or not, so it is not secure. *)

Definition less_obvious_f3 (pi si : nat) : nat*nat :=
  (if si =? 0 then 1 else 0, pi+si).

Lemma interferent_less_obvious_f3 : ~noninterferent less_obvious_f3.
Proof.
  unfold noninterferent, less_obvious_f3. simpl. intros contra.
  specialize (contra 42 0 10). simpl in contra. discriminate contra.
Qed.

(* ================================================================= *)
(** ** Noninterference Exercises *)

(** Let's practice with some "prove or disprove noninterference"
    exercises, for which you are required to give constructive proofs,
    i.e. the use of classical axioms like excluded middle is not allowed. *)

(** **** Exercise: 1 star, standard (prove_or_disprove_obvious_f1) *)
Definition obvious_f1 (pi si : nat) : nat*nat := (0,0).

Lemma prove_or_disprove_obvious_f1 :
  noninterferent obvious_f1 \/ ~noninterferent obvious_f1.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 1 star, standard (prove_or_disprove_obvious_f2) *)
Definition obvious_f2 (pi si : nat) : nat*nat := (pi+(2*si),(2*pi)+si).

Lemma prove_or_disprove_obvious_f2 :
  noninterferent obvious_f2 \/ ~noninterferent obvious_f2.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard (prove_or_disprove_less_obvious_f4) *)

Definition less_obvious_f4 (pi si : nat) : nat*nat :=
  (if si =? 0 then si * pi else pi, pi+si).

(** Is the [less_obvious_f4] function noninterferent or not? *)

Lemma prove_or_disprove_less_obvious_f4 :
  noninterferent less_obvious_f4 \/ ~noninterferent less_obvious_f4.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard (prove_or_disprove_less_obvious_f5) *)

Definition less_obvious_f5 (pi si : nat) : nat*nat :=
  (if si =? 0 then si + pi else pi, pi+si).

(** Is the [less_obvious_f5] function noninterferent or not? *)

Lemma prove_or_disprove_less_obvious_f5 :
  noninterferent less_obvious_f5 \/ ~noninterferent less_obvious_f5.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard (prove_or_disprove_less_obvious_f6) *)

Definition less_obvious_f6 (pi si : nat): nat*nat :=
  (if Nat.ltb si pi then 0 else pi, pi+si).

(** Is the [less_obvious_f6] function noninterferent or not? *)

Lemma prove_or_disprove_less_obvious_f6 :
  noninterferent less_obvious_f6 \/ ~noninterferent less_obvious_f6.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, standard, optional (prove_or_disprove_less_obvious_f7) *)

Definition less_obvious_f7 (pi si : nat): nat*nat :=
  if si + pi =? 0 then (si,pi) else (pi,si).

Lemma prove_or_disprove_less_obvious_f7 :
  noninterferent less_obvious_f7 \/ ~noninterferent less_obvious_f7.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard (noninterferent_diff_si_same) *)

(** Finally, consider the following alternative definition of
    noninterference, which requires the two secret inputs to be
    different. It more directly captures the original intuition that
    _changing_ the secret input should not change the public output: *)

Definition noninterferent_diff_si {PI SI PO SO : Type} (f:PI->SI->PO*SO) :=
  forall (pi:PI) (si1 si2:SI), si1 <> si2 -> fst (f pi si1) = fst (f pi si2).

(** Prove that this definition of noninterference is equivalent to the
    original one, at least on type [nat] (which supports decidable
    equality; otherwise we would need excluded middle to prove this). *)

Lemma noninterferent_diff_si_same : forall (f:nat->nat->nat*nat),
  noninterferent_diff_si f <-> noninterferent f.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ################################################################# *)
(** * A too-strong secrecy definition *)

(** In the definition of noninterference above we pass the same public
    inputs to the two executions and this allows public outputs to
    depend on public inputs. To convince ourselves of this, let's look
    at the following overly strong definition of security: *)

Definition too_strong_sec_def {PI SI PO SO : Type} (f:PI->SI->PO*SO) :=
  forall (pi1 pi2:PI) (si1 si2:SI), fst (f pi1 si1) = fst (f pi2 si2).

(** This basically says that the public output of [f] can depend
    neither on the public input nor on the secret input, so it has to
    be constant, which is not the case for our [secure_f]. *)

Print secure_f. (* fun pi si : nat => (pi + 1, pi + si * 2) *)

Lemma secure_f_rejected_again : ~too_strong_sec_def secure_f.
Proof.
  unfold too_strong_sec_def, secure_f. simpl. intros contra.
  specialize (contra 0 1 0 0). discriminate contra.
Qed.

(* ################################################################# *)
(** * Noninterferent the same as being splittable *)

(** Noninterference is still a very strong property, though. In
    particular, [f] being noninterferent is equivalent to [f] being
    splittable into two distinct functions: a public function that
    doesn't get the secret input, and a secret function that does. *)

Definition splittable {PI SI PO SO : Type} (f:PI->SI->PO*SO) :=
  exists (pf : PI -> PO) (sf : PI -> SI -> SO),
    forall pi si , f pi si = (pf pi, sf pi si).

(** One of the equivalence directions is easy: *)

Theorem splittable_noninterferent : forall PI SI PO SO : Type,
  forall f : PI -> SI -> PO*SO, splittable f -> noninterferent f.
Proof.
  unfold splittable, noninterferent.
  intros PI SI PO SO f [pf [sf H]] pi si1 si2.
  rewrite H. rewrite H. simpl. reflexivity.
Qed.

(** The other equivalence direction is more interesting: *)

Theorem noninterferent_splittable : forall PI SI PO SO : Type,
  forall some_si : SI, (* we require SI to be an inhabited type! *)
  forall f : PI -> SI -> PO*SO, noninterferent f -> splittable f.
Proof.
  unfold splittable, noninterferent.
  intros PI SI PO SO some_si f NI.
  (* we construct pf and sf using f itself *)
  (* for pf we pass the SI inhabitant as a dummy secret value! *)
  exists (fun pi => fst (f pi some_si)).
  exists (fun pi si => snd (f pi si)).
  (* we then use NI to change from dummy secret to real one *)
  intros pi si. rewrite (NI _ _ si).
  destruct (f pi si) as [po so]. reflexivity.
Qed.

(** This splittability result is also the key idea behind static
    _program partitioning_ [Zdancewic et al 2002] (in Bib.v), where a
    program is split so that its public part never even mentions
    the secrets -- in contrast to secure multi-execution below,
    which runs the unchanged program on dummy secret inputs. We
    formalize a simple variant of program partitioning for Imp in
    the "Program partitioning" section of [StaticIFC]. *)

(* ################################################################# *)
(** * Secure Multi-Execution (SME) *)

(** The previous proof also captures the key idea behind Secure
    Multi-Execution (SME) [Devriese and Piessens 2010] (in Bib.v), an
    enforcement mechanism that can make _any_ function
    noninterferent. To achieve this SME runs the function twice, once
    passing a dummy secret as input to obtain the public output, and
    once using the real secret input to obtain the secret output. *)

Definition sme {PI SI PO SO : Type} (some_si : SI)
  (f:PI->SI->PO*SO) : PI->SI->PO*SO :=
    fun pi si => (fst (f pi some_si), snd (f pi si)).

(** Functions protected by [sme] are guaranteed to satisfy noninterference: *)

Theorem noninterferent_sme :  forall PI SI PO SO : Type,
  forall some_si : SI,
  forall f : PI -> SI -> PO*SO,
    noninterferent (sme some_si f).
Proof. intros PI SI PO SO some_si f pi si1 si2. simpl. reflexivity. Qed.

(** Moreover, if the function we pass to [sme] is already noninterferent,
    then its behavior will not change; so we say that [sme] is a _transparent_
    enforcement mechanism for noninterference: *)

Theorem transparent_sme : forall PI SI PO SO : Type,
  forall some_si : SI,
  forall f : PI -> SI -> PO*SO,
    noninterferent f -> forall pi si, f pi si = sme some_si f pi si.
Proof.
  unfold noninterferent, sme. intros PI SI PO SP some_si f NI.
  (* The rest is the same as [noninterferent_splittable] proof *)
  intros pi si. rewrite (NI _ _ si).
  destruct (f pi si) as [po so]. reflexivity.
Qed.

(** It is interesting to look at what [sme] does for _interferent_ functions,
    like [insecure_f], whose public output was its secret input plus [1]: *)

Print insecure_f. (* fun pi si : nat => (si + 1, pi + si * 2) *)

Example example1_sme_insecure_f: sme 0 insecure_f 0 0 = (1, 0).
Proof. reflexivity. Qed.

Example example2_sme_insecure_f: sme 0 insecure_f 0 1 = (1, 2).
Proof. reflexivity. Qed.

Example example3_sme_insecure_f: sme 0 insecure_f 1 1 = (1, 3).
Proof. reflexivity. Qed.

(** Now the public output of [sme insecure_f 0] is the dummy secret
    [0] plus [1], so always the constant [1]. *)

Lemma constant_sme_insecure_f: forall pi si,
  fst (sme 0 insecure_f pi si) = 1.
Proof. unfold sme, insecure_f. reflexivity. Qed.

(** This is a secure behavior, but it is different from that of the
    original [insecure_f] function. So we are giving up some
    correctness for security. There is no free lunch! *)

(** Of course the public output of [sme] does not always become constant,
    since some functions still use the public input. *)

Definition another_insecure_f (pi si : nat) := (pi+si, pi+si).

Lemma sme_another_insecure_f : forall pi si,
  sme 0 (another_insecure_f) pi si = (pi,pi+si).
Proof. unfold sme, another_insecure_f.
  intros pi si. simpl. rewrite <- plus_n_O. reflexivity. Qed.

(** **** Exercise: 1 star, standard (sme_another_insecure_f2) *)
Definition another_insecure_f2 (pi si : nat) : nat*nat :=
  (if si =? 0 then 2*pi else pi, pi+si).

Lemma sme_another_insecure_f2 : forall pi si,
    sme 0 (another_insecure_f2) pi si = (2*pi, pi+si).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard (sme_another_insecure_f3) *)
Definition another_insecure_f3 (pi si : nat) : nat*nat :=
  (if si =? pi then si * pi else pi, pi+si).

Lemma sme_another_insecure_f3 : forall pi si,
    sme 0 (another_insecure_f3) pi si = (pi, pi+si).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 1 star, standard (sme_correct_so)

    While the public output of [sme] can be incorrect,
    the secret output of [sme] is obviously always correct: *)
Lemma sme_correct_so : forall PI SI PO SO : Type,
  forall some_si : SI,
  forall f : PI -> SI -> PO*SO,
  forall pi si, snd (f pi si) = snd (sme some_si f pi si).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** Beyond giving up on correctness for the public outputs of insecure functions,
    the other downside of SME is that we have to run the function
    twice for our two security levels, public and secret. In general,
    we need to run the program as many times as we have security
    levels, which can be a large number (e.g., exponential if we take our
    security levels to be sets of users). This is inefficient! *)

(** Other information-flow control mechanisms overcome these downsides,
    but have their own pros and cons, for instance:
        - _Information-flow type systems_ ([StaticIFC]) do not
          introduce any runtime overhead, but use static
          overapproximations that reject some secure programs.
        - _Relational Hoare Logic_ is static and precise, but requires
          nontrivial manual proofs for each individual program.
        - _Dynamic information-flow control_ (a secure variant of dynamic
          taint tracking) is generally more efficient than SME, but
          uses dynamic overapproximations that unnecessarily change
          some program behavior to prevent leaks, for instance forcefully
          terminating even some secure programs (which is not transparent).

    Again, there is no free lunch! *)

From Stdlib Require Import Lia.
From SECF Require Import Maps.
From SECF Require Import Imp.

(* ################################################################# *)
(** * Noninterference for state transformers *)

(** The noninterference formalization above can be adapted to Rocq
    functions that transform states to states (of type
    [state->state]), where we label each variable as either public or
    secret using a _label map_. *)

Print state. (* state = total_map nat = string -> nat *)

Inductive label : Type :=
  | public
  | secret.

Definition label_map := total_map label. (* = string -> label *)

(** Equality of labels is decidable, and we introduce the usual [=?]
    notation for the corresponding boolean equality test: *)

Definition label_eqb (l1 l2 : label) : bool :=
  match l1, l2 with
  | public, public | secret, secret => true
  | _, _ => false
  end.

Declare Scope label_scope.
Infix "=?" := label_eqb : label_scope.
Delimit Scope label_scope with label.
Open Scope label_scope.

Lemma label_eqb_refl : forall {l : label}, (l =? l) = true.
Proof. intros [|]; reflexivity. Qed.

Lemma label_eqb_eq : forall {l1 l2 : label},
  (l1 =? l2) = true <-> l1 = l2.
Proof.
  intros [|] [|]; split; intros H; try reflexivity; discriminate H.
Qed.

Lemma label_eqb_spec : forall l1 l2 : label,
  reflect (l1 = l2) (l1 =? l2).
Proof.
  intros [|] [|]; constructor; (reflexivity || discriminate).
Qed.

Lemma label_eqb_neq : forall {l1 l2 : label},
  (l1 =? l2) = false <-> l1 <> l2.
Proof.
  intros l1 l2. destruct (label_eqb_spec l1 l2) as [Heq | Hneq].
  - split.
    + intros H. discriminate H.
    + intros H. exfalso. apply H. apply Heq.
  - split.
    + intros _. apply Hneq.
    + intros _. reflexivity.
Qed.

(** As opposed to the state, which the transformer changes, the label
    of the variables is fixed. *)

(** A noninterference attacker can only observe the final values of
    variables our label map ([L]) considers public ([L x = public]),
    not of secret ones ([L x = secret]). We formalize this as a notion
    of _publicly equivalent states_ that agree on the values of all
    public variables: *)

Definition pub_equiv (L : label_map) (s1 s2 : state) :=
  forall x:string, L x = public -> s1 x = s2 x.

(** [pub_equiv L] is an equivalence relation on states -- reflexive,
    symmetric, and transitive. *)

Lemma pub_equiv_refl : forall (L:label_map) (s:state),
  pub_equiv L s s.
Proof. intros L s x Hx. reflexivity. Qed.

Lemma pub_equiv_sym : forall (L:label_map) (s1 s2:state),
  pub_equiv L s1 s2 ->
  pub_equiv L s2 s1.
Proof. unfold pub_equiv. intros L s1 s2 H x Px. rewrite H; auto. Qed.

Lemma pub_equiv_trans : forall (L:label_map) (s1 s2 s3:state),
  pub_equiv L s1 s2 ->
  pub_equiv L s2 s3 ->
  pub_equiv L s1 s3.
Proof. unfold pub_equiv. intros L s1 s2 s3 H12 H23 x Px.
       rewrite H12; try rewrite H23; auto. Qed.

(** This makes this noninterference definition symmetric, since we can
    use [pub_equiv] both for the initial states (i.e., inputs) and for
    the final states (i.e., outputs): *)

Definition noninterferent_state L (f : state -> state) :=
  forall s1 s2, pub_equiv L s1 s2 -> pub_equiv L (f s1) (f s2).

(** Formally, a state transformer [f] is _noninterferent_
    whenever it maps any two publicly equivalent initial states [s1]
    and [s2] to publicly equivalent final states [f s1] and [f s2]. *)

(** Intuitively, this ensures that the values of the public variables
    in the final state can only depend on the value of public
    variables in the initial state, and do not depend on the initial
    value of secret variables. In particular, changing the value of
    the secret variables in the initial state (as allowed by
    [pub_equiv L s1 s2]), should lead to no change in the final value
    of the public variables (as required by [pub_equiv L s1' s2']). *)

(** As a first example, the identity state transformer is noninterferent: *)

Definition tid (s:state) : state := s.

Lemma noninterferent_tid : forall L : label_map,
  noninterferent_state L tid.
Proof.
  unfold noninterferent_state. intros L s1 s2 PEq.
  unfold tid. apply PEq.
Qed.

(** Another simple example, the transformer that assigns the constant
    [c] to the public variable [X] is also noninterferent: *)

Definition tconstX c (s:state) : state := (X !-> c; s).

(** This is just syntactic sugar defined in [Maps] for
    [t_update s X c]. *)

(** In this and the further examples we will consider a fixed variable
    assignment [LXP], in which [X] is the only public variable, and
    all other variables are secret. *)

Definition LXP : label_map := (X !-> public; __ !-> secret).

(** For proving [tconstX] noninterferent with respect to the
    [LXP] variable mapping we first prove a lemma specific to [LXP]: *)

Lemma LXP_public : forall x, LXP x = public -> x = X.
Proof.
  unfold LXP. intros x Hx.
  destruct (String.eqb_spec x X).
  - subst. reflexivity.
  - rewrite t_update_neq in Hx.
    + rewrite t_apply_empty in Hx. discriminate.
    + intro contra. subst. contradiction.
Qed.

(** In the proof above we are using the [t_update_neq] and
    [t_apply_empty] lemmas from [Maps]. We also used lemma
    [String.eqb_spec] to do case analysis on whether the [x] is
    equal to [X]. For more details on how this works, please check
    out the explanations about the [reflect] inductive predicate in
    the [IndProp] chapter from Logical Foundations.

    Now back to our noninterference proof for [tconstX]: *)

Lemma noninterferent_tconstX : forall c,
    noninterferent_state LXP (tconstX c).
Proof.
  unfold noninterferent_state, tconstX. intros c s1 s2 _PEq.
  unfold pub_equiv. intros x Px. apply LXP_public in Px. subst.
  repeat rewrite t_update_eq. reflexivity.
Qed.

(** **** Exercise: 2 stars, standard (noninterferent_tincX) *)

(** Prove that the transformer incrementing [X] is
    noninterferent, using the [pub_equiv] hypothesis: *)

Definition tincX (s:state) : state := (X !-> s X + 1; s).

Lemma noninterferent_tincX : noninterferent_state LXP tincX.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard (noninterferent_tincY) *)

(** Prove that the transformer incrementing [Y] is also noninterferent,
    since the value of the public variable [X] is unaffected: *)

Definition tincY (s:state) : state := (Y !-> s Y + 1; s).

Lemma noninterferent_tincY : noninterferent_state LXP tincY.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** The transformer copying the secret in [Y] to public variable [X]
    is insecure: *)

Definition tYtoX (s:state) : state := (X !-> s Y; s).

(** We prove a trivial lemma to be used in the proof below: *)
Lemma LXPX : LXP X = public.
Proof. reflexivity. Qed.

Lemma interferent_YtoX : ~noninterferent_state LXP tYtoX.
Proof.
  unfold noninterferent_state, tYtoX. intros Hc.
  (* We choose two states that differ in secret variable [Y] *)
  set (s1 := Y !-> 0; __ !-> 0).
  set (s2 := Y !-> 1; __ !-> 0).
  (* These two states are equivalent wrt [LXP]
     so we can instantiate [Hc] with them *)
  assert (Peq: pub_equiv LXP s1 s2).
  { clear Hc. intros x H. apply LXP_public in H. subst. reflexivity. }
  specialize (Hc s1 s2 Peq). unfold pub_equiv in Hc.
  specialize (Hc X LXPX). repeat rewrite t_update_eq in Hc.
  (* We obtained [Hc : s1 Y = s2 Y], but that is a contradiction *)
  unfold s1, s2, t_update in Hc. simpl in Hc. discriminate Hc.
Qed.

(** The [set] tactic in the proof above allows us to give names
    to complex expressions, making proofs more readable and
    manageable. It's particularly useful when constructing concrete
    counterexamples where one needs to work with specific values. *)

(** **** Exercise: 3 stars, standard (interferent_tXtimesYtoX)

    Prove that multiplying [X] and [Y] and storing the result in [X]
    is also insecure, since [Y] is secret: *)

Definition tXtimesYtoX (s:state) : state := (X !-> s X * s Y; s).

Lemma interferent_tXtimesYtoX : ~noninterferent_state LXP tXtimesYtoX.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)



(* ----------------------------------------------------------------- *)
(** *** Relating current and previous noninterference definitions *)

(** Our [noninterferent_state] definition works for [state->state] functions. *)

Print noninterferent_state.
(* fun (L : label_map) (f : state -> state) =>
   forall s1 s2 : state, pub_equiv L s1 s2 -> pub_equiv L (f s1) (f s2) *)

(** In contrast, our original [noninterferent] definition was for
    functions on pairs: *)

Print noninterferent.
(* fun {PI SI PO SO : Type} (f : PI -> SI -> PO * SO) =>
   forall (pi : PI) (si1 si2 : SI), fst (f pi si1) = fst (f pi si2) *)

(** We can prove an equivalence between [noninterferent_state]
    and our original [noninterferent] definition. For this we need to
    split and merge states. We also need a few helper lemmas. *)

(** The way we define [split_state] and [merge_state] is a good
    example of programming with higher-order functions, and there's
    more of this in the [Maps] chapter of Logical Foundations.

    The [split_state] function takes a state [s] and zeroes out the variables
    [x] for which [L x] is different from an argument label [l]. So
    [split_state s L public] keeps the public variables, and zeroes out the
    secret ones. Dually, [split_state s L secret] keeps the secret variables,
    and zeroes out the public ones.  *)

Definition split_state (s:state) (L:label_map) (l:label) : state :=
  fun x : string => if L x =? l then s x else 0.

(** The [merge_state] function takes in two states [ps] and [ss]
    and produces a new state that contains the public variables from
    [ps] and the secret variables from [ss]. *)

Definition merge_states (ps ss:state) (L:label_map) : state :=
  fun x : string => if L x =? public then ps x else ss x.

(** Using [merge_states] and [split_state] we can convert state
    transformers working on merged states into functions working on
    split states (which we will use to instantiate the original
    [noninterferent] definition): *)

Definition split_state_fun (L : label_map) (mf : state -> state) :=
  fun ps ss : state =>
    let ms := mf (merge_states ps ss L) in
    (split_state ms L public, split_state ms L secret).

(** The technical development needed for the equivalence proof between
    [noninterferent_state] and our original [noninterferent]
    definition is not that interesting though, and one can skip
    directly to the [noninterferent_state_ni] statement on first read. *)

Definition pub_equiv_split (L : label_map) (s1 s2 : state) :=
  forall x:string, (split_state s1 L public) x = (split_state s2 L public) x.

Theorem pub_equiv_split_iff : forall L s1 s2,
  pub_equiv L s1 s2 <-> pub_equiv_split L s1 s2.
Proof.
  unfold pub_equiv, pub_equiv_split, split_state. intros. split.
  - intros H x. destruct (label_eqb_spec (L x) public).
    + apply H. apply e.
    + reflexivity.
  - intros H x. specialize (H x).
    destruct (label_eqb_spec (L x) public).
    + intros _. apply H.
    + contradiction.
Qed.

Theorem pub_equiv_merge_states : forall L ps ss1 ss2,
  pub_equiv L (merge_states ps ss1 L) (merge_states ps ss2 L).
Proof.
  unfold pub_equiv, merge_states. intros L ps ss1 ss2 x Hx.
  rewrite Hx. reflexivity.
Qed.

From Stdlib Require Import FunctionalExtensionality.

Theorem merge_states_split_state : forall s L,
  merge_states (split_state s L public) (split_state s L secret) L = s.
Proof.
  unfold merge_states, split_state. intros s L.
  apply functional_extensionality. intro x.
  destruct (L x) eqn:Heq; reflexivity.
Qed.

(** Now we can finally state our equivalence theorem between
    [noninterferent_state] and [noninterferent]: *)

Theorem noninterferent_state_ni : forall L f,
  noninterferent_state L f <->
  noninterferent (split_state_fun L f).
Proof.
  unfold noninterferent_state, noninterferent, split_state_fun.
  intros L f. split.
  - intros H ps ss1 ss2. simpl.
    assert (H' : pub_equiv L (merge_states ps ss1 L)
                             (merge_states ps ss2 L)).
      { apply pub_equiv_merge_states. }
    apply H in H'. rewrite pub_equiv_split_iff in H'.
    unfold pub_equiv_split in H'.
    apply functional_extensionality. apply H'.
  - intros H s1 s2 Hequiv. simpl in H.
    rewrite pub_equiv_split_iff in *. unfold pub_equiv_split in *.
    intro x.
    specialize (H (split_state s1 L public)
                  (split_state s1 L secret)
                  (split_state s2 L secret)).
    rewrite merge_states_split_state in H.
    apply functional_extensionality in Hequiv. rewrite Hequiv in H.
    rewrite merge_states_split_state in H.
    rewrite H. reflexivity.
Qed.

(* ################################################################# *)
(** * Secure Multi-Execution for state transformers *)

(** We can use the [split_state] and [merge_states] functions above to
    also define SME for state transformers. We call the [split_state]
    below to zero out all secret variables before calling [f] the first
    time to obtain the final value of the public variables. *)

Definition sme_state (f : state -> state) (L:label_map) :=
  fun s => merge_states (f (split_state s L public)) (f s) L.

(** We will see examples of this below, but for now we prove the
    same two theorems for [sme_state] as for [sme]; first noninterference: *)

Theorem noninterferent_sme_state : forall L f,
  noninterferent_state L (sme_state f L).
Proof.
  unfold noninterferent_state, sme_state.
  intros L f s1 s2 Hequiv.
  rewrite pub_equiv_split_iff in Hequiv.
  unfold pub_equiv_split in Hequiv.
  apply functional_extensionality in Hequiv. rewrite Hequiv.
  apply pub_equiv_merge_states.
Qed.

(** Then for transparency we first need a few extra lemmas:  *)

Lemma pub_equiv_split_state : forall (L:label_map) s,
  pub_equiv L (split_state s L public) s.
Proof.
  unfold pub_equiv, split_state.
  intros L s x Hx. destruct (label_eqb_spec (L x) public).
  - reflexivity.
  - contradiction.
Qed.

Lemma merge_state_pub_equiv : forall L ss ps,
  pub_equiv L ps ss ->
  merge_states ps ss L = ss.
Proof.
  unfold pub_equiv, merge_states.
  intros L ss ps H. apply functional_extensionality.
  intros x. destruct (L x) eqn:Heq.
  - rewrite H.
    + reflexivity.
    + assumption.
  - reflexivity.
Qed.

Theorem transparent_sme_state : forall f L,
  noninterferent_state L f -> forall s, f s = sme_state f L s.
Proof.
  intros f L Hni s. unfold sme_state.
  symmetry. apply merge_state_pub_equiv.
  apply Hni. apply pub_equiv_split_state.
Qed.

(** Before turning to concrete [sme_state] examples we prove some
    more lemmas that allow us to reason at a higher level, without
    unfolding [merge_states] and [split_state] by hand everywhere.

    The first two characterize [split_state _ _ public]: it keeps the
    public variables unchanged and zeroes out the secret ones. *)

Lemma split_state_public_id : forall s L x,
  L x = public -> split_state s L public x = s x.
Proof. intros s L x H. unfold split_state. rewrite H. reflexivity. Qed.

Lemma split_state_secret_zero : forall s L x,
  L x = secret -> split_state s L public x = 0.
Proof. intros s L x H. unfold split_state. rewrite H. reflexivity. Qed.

(** The next two lemmas spell out the interaction between
    [merge_states] and updates to public variables. Recall that a
    merge takes its public variables from the first argument and its
    secret variables from the second.  So updating a _public_ variable
    [x] on the first argument survives the merge ... *)

Lemma merge_states_update_pub_fst : forall (L:label_map) x v s1 s2,
  L x = public ->
  merge_states (x !-> v; s1) s2 L = (x !-> v; merge_states s1 s2 L).
Proof.
  intros L x v s1 s2 Hx. apply functional_extensionality. intros y.
  unfold merge_states. destruct (String.eqb_spec x y).
  - subst y. rewrite Hx. repeat rewrite t_update_eq. reflexivity.
  - repeat rewrite t_update_neq; try assumption. reflexivity.
Qed.

(** ... while updating a public variable [x] on the second argument is
    a no-op, since the merge never reads public variables from there. *)

Lemma merge_states_update_pub_snd : forall (L:label_map) x v s1 s2,
  L x = public ->
  merge_states s1 (x !-> v; s2) L = merge_states s1 s2 L.
Proof.
  intros L x v s1 s2 Hx. apply functional_extensionality. intros y.
  unfold merge_states. destruct (String.eqb_spec x y).
  - subst y. rewrite Hx. reflexivity.
  - rewrite t_update_neq; try assumption. reflexivity.
Qed.

(** Dually, updating a _secret_ variable [x] on the first argument is a
    no-op (the merge reads public variables from the first argument,
    not secret ones) ... *)

Lemma merge_states_update_sec_fst : forall (L:label_map) x v s1 s2,
  L x = secret ->
  merge_states (x !-> v; s1) s2 L = merge_states s1 s2 L.
Proof.
  intros L x v s1 s2 Hx. apply functional_extensionality. intros y.
  unfold merge_states. destruct (String.eqb_spec x y).
  - subst y. rewrite Hx. reflexivity.
  - rewrite t_update_neq; try assumption. reflexivity.
Qed.

(** ... while updating a secret variable [x] on the second argument
    survives the merge. *)

Lemma merge_states_update_sec_snd : forall (L:label_map) x v s1 s2,
  L x = secret ->
  merge_states s1 (x !-> v; s2) L = (x !-> v; merge_states s1 s2 L).
Proof.
  intros L x v s1 s2 Hx. apply functional_extensionality. intros y.
  unfold merge_states. destruct (String.eqb_spec x y).
  - subst y. rewrite Hx. repeat rewrite t_update_eq. reflexivity.
  - (repeat rewrite t_update_neq); try assumption. reflexivity.
Qed.

(** Combining the previous lemmas, we get what happens when _both_ runs
    update the same variable [x] (with possibly different values), which
    is the situation that arises in practice.  For a public [x] the merge
    keeps the first argument's value... *)

Lemma merge_states_update_pub : forall (L:label_map) x v1 v2 s1 s2,
  L x = public ->
  merge_states (x !-> v1; s1) (x !-> v2; s2) L
    = (x !-> v1; merge_states s1 s2 L).
Proof.
  intros L x v1 v2 s1 s2 Hx.
  rewrite merge_states_update_pub_fst; try assumption.
  rewrite merge_states_update_pub_snd; try assumption.
  reflexivity.
Qed.

(** ... while for a secret [x] it keeps the second argument's value. *)

Lemma merge_states_update_sec : forall (L:label_map) x v1 v2 s1 s2,
  L x = secret ->
  merge_states (x !-> v1; s1) (x !-> v2; s2) L
    = (x !-> v2; merge_states s1 s2 L).
Proof.
  intros L x v1 v2 s1 s2 Hx.
  rewrite merge_states_update_sec_fst; try assumption.
  rewrite merge_states_update_sec_snd; try assumption.
  reflexivity.
Qed.

(** The final lemma captures what [sme_state] does to a transformer
    that updates a single _public_ variable [x] (leaving everything
    else untouched): the value written to [x] is computed from the
    public projection [split_state s L public] of the state, rather
    than from the full state [s].  This is exactly the mechanism by
    which SME severs the dependency of public outputs on secret
    inputs. Using the lemmas above we can prove it purely by
    rewriting, without unfolding [merge_states]: *)

Lemma sme_state_update_pub : forall (x:string) (e:state->nat) (L:label_map) s,
  L x = public ->
  sme_state (fun s => (x !-> e s; s)) L s
    = (x !-> e (split_state s L public); s).
Proof.
  intros x e L s Hx. unfold sme_state.
  rewrite merge_states_update_pub_fst; try assumption.
  rewrite merge_states_update_pub_snd; try assumption.
  rewrite merge_state_pub_equiv.
  - reflexivity.
  - apply pub_equiv_split_state.
Qed.

(** Here is an example showing how [sme_state] changes the behavior
    of insecure transformers so that they become secure: *)

Lemma sme_state_tYtoX : sme_state tYtoX LXP = tconstX 0.
Proof.
  apply functional_extensionality. intros s.
  unfold tYtoX, tconstX.
  assert (HX : LXP X = public). { reflexivity. }
  assert (HY : LXP Y = secret). { reflexivity. }
  rewrite sme_state_update_pub; try assumption.
  (* the public run reads [Y] from the secret-zeroed state, so [X := 0] *)
  rewrite split_state_secret_zero; try assumption.
  reflexivity.
Qed.

(** **** Exercise: 3 stars, standard (sme_state_tXplusYtoX) *)

(** Show that applying [sme_state] to the following transformer turns
    it into identity. (Hint: It helps if, like in the proof above, one
    uses high-level lemmas instead of unfolding everything.) *)

Definition tXplusYtoX (s:state) : state := (X !-> s X + s Y; s).

Lemma sme_state_tXplusYtoX : sme_state tXplusYtoX LXP = tid.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ================================================================= *)
(** ** Optional: Connection between [sme] and [sme_state]  *)

(** We can formally relate [sme] and [sme_state], but this gets pretty
    technical, so the curious reader can directly skip to the two
    theorems at the end of this subsection. *)

Lemma split_merge_public: forall s L,
    split_state s L public = merge_states s (fun _ => 0) L.
Proof.
  intros. eapply functional_extensionality. intro x.
  unfold split_state, merge_states.
  destruct (L x) eqn:PUB; simpl; reflexivity.
Qed.

Lemma split_merge_split_public: forall s s' L,
    split_state (merge_states s s' L) L public = split_state s L public.
Proof.
  intros. eapply functional_extensionality. intro x.
  unfold split_state, merge_states.
  destruct (L x) eqn:PUB; simpl; reflexivity.
Qed.

Lemma split_merge_split_secret: forall s s' L,
    split_state (merge_states s s' L) L secret = split_state s' L secret.
Proof.
  intros. eapply functional_extensionality. intro x.
  unfold split_state, merge_states.
  destruct (L x) eqn:PUB; simpl; reflexivity.
Qed.

Lemma merge_states_same: forall s L,
    merge_states s s L = s.
Proof.
  unfold merge_states. intros.
  eapply functional_extensionality. intro x.
  destruct (L x); reflexivity.
Qed.

Lemma split_state_idem: forall s L l,
    split_state (split_state s L l) L l = split_state s L l.
Proof.
  unfold split_state. intros.
  eapply functional_extensionality. intro x.
  destruct (L x =? l); reflexivity.
Qed.

Lemma split_state_orthogonal: forall s L l1 l2,
    l1 <> l2 ->
    split_state (split_state s L l1) L l2 = fun _ => 0.
Proof.
  unfold split_state. intros s L l1 l2 Hneq.
  eapply functional_extensionality. intro x.
  destruct (label_eqb_spec (L x) l2) as [Heq2 | Hneq2];
    [| reflexivity].
  destruct (label_eqb_spec (L x) l1) as [Heq1 | Hneq1];
    [| reflexivity].
  exfalso. apply Hneq. rewrite <- Heq1. apply Heq2.
Qed.

(** First, we show a relationship between [sme] and [sme_state] using
    [split_state_fun]: *)

Theorem split_sme_state_sme: forall L f,
    split_state_fun L (sme_state f L) = sme (fun _ => 0) (split_state_fun L f).
Proof.
  intros.
  eapply functional_extensionality. intro PI.
  eapply functional_extensionality. intro SI.
  unfold split_state_fun, sme.
  rewrite pair_equal_spec. split.
  - simpl. unfold sme_state.
    rewrite <- split_merge_public.
    repeat rewrite split_merge_split_public. reflexivity.
  - simpl. unfold sme_state.
    rewrite split_merge_split_secret. reflexivity.
Qed.

(** Second, we also show a relationship between [sme] and [sme_state]
    using [merge_state_fun]: *)

Definition merge_state_fun (L : label_map) (sf : state -> state -> state*state) :=
  fun s : state =>
    let ps := sf (split_state s L public) (split_state s L secret) in
    merge_states (fst ps) (snd ps) L.

Theorem merge_sme_state_sme: forall L f,
    sme_state (merge_state_fun L f) L = merge_state_fun L (sme (fun _ => 0) f).
Proof.
  intros.
  eapply functional_extensionality. intro s.
  eapply functional_extensionality. intro x.
  unfold merge_state_fun. simpl.
  unfold sme_state. unfold merge_states.
  destruct (L x) eqn:PUB.
  - rewrite split_state_idem.
    rewrite split_state_orthogonal; [reflexivity | discriminate].
  - reflexivity.
Qed.

(* ################################################################# *)
(** * Noninterference for Imp programs without loops *)

(** For programs without loops the "failed attempt" evaluation function from
    [Imp] works well and allows us to easily define a state transformer
    function for each Imp command. *)

Print ceval_fun_no_while.
(* = fix ceval_fun_no_while (st : state) (c : com) : state := *)
(*   match c with                                             *)
(*     | <{ skip }> =>                                        *)
(*         st                                                 *)
(*     | <{ x := a }> =>                                      *)
(*         (x !-> aeval st a ; st)                            *)
(*     | <{ c1 ; c2 }> =>                                     *)
(*         let st' := ceval_fun_no_while st c1 in             *)
(*         ceval_fun_no_while st' c2                          *)
(*     | <{ if b then c1 else c2 end}> =>                     *)
(*         if (beval st b)                                    *)
(*           then ceval_fun_no_while st c1                    *)
(*           else ceval_fun_no_while st c2                    *)
(*     | <{ while b do c end }> =>                            *)
(*         st  (/* bogus */)                                  *)
(*   end.                                                     *)
Definition flip {A B C : Type} (f : A -> B -> C) := fun b a => f a b.
Definition cinterp : com -> state -> state := flip ceval_fun_no_while.

Definition noninterferent_no_while L c : Prop :=
  noninterferent_state L (cinterp c).

(** A command [c] without loops is noninterferent if the state
    transformer obtained by interpreting the command with [cinterp]
    maps public-equivalent states to public-equivalent states. *)

(** We can use this definition to prove that the following command is
    noninterferent: *)

Definition secure_com : com :=
  <{ X := X+1;
     Y := (X-1)+Y*2 }>.

Lemma noninterferent_secure_com :
  noninterferent_no_while LXP secure_com.
Proof.
  unfold noninterferent_no_while, noninterferent_state, secure_com.
  intros s1 s2 PEQUIV x Hx.

  (* Since x is the only public variable in LXP, we know [x = X] *)
  apply LXP_public in Hx. subst.

  (* From public equivalence we show [s1 X = s2 X]. *)
  specialize (PEQUIV X LXPX).

  (* We use computation (running [cinterp]) to show that
     [X] in [secure_com] depends only on the initial [X]. *)
  simpl. rewrite PEQUIV. reflexivity.
Qed.

(** **** Exercise: 2 stars, standard (noninterferent_secure_ex1) *)
Definition secure_ex1 :=
  <{ Y := Y - 1;
     X := 1 }>.

Lemma noninterferent_secure_ex1 :
  noninterferent_no_while LXP secure_ex1.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, standard, optional (noninterferent_secure_ex2) *)
Definition secure_ex2 :=
  <{ if X = 0 then
       X := X + 5
     else
       Y := X
     end }>.

Lemma noninterferent_secure_ex2 :
  noninterferent_no_while LXP secure_ex2.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** Now let's look at a couple of insecure commands: *)

Definition insecure_com1 : com :=
  <{ X := Y+1; (* <- bad explicit flow! *)
     Y := (X-1)+Y*2 }>.

(** An _explicit flow_ is when a command directly assigns an expression
    depending on secret variables to a public variable, like the [X := Y+1]
    assignment above. Explicit flows are easier to find automatically
    and even simple taint-tracking would be enough for discovering this.

    We prove that [insecure_com1] is insecure: *)

Lemma interferent_insecure_com1 :
  ~noninterferent_no_while LXP insecure_com1.
Proof.
  unfold noninterferent_no_while, noninterferent_state, insecure_com1.
  intro Hc.

  (* Choose [s1] and [s2] that are [pub_equiv]
     but that differ in secret variable [Y]. *)
  set (s1 := (Y !-> 0)).
  set (s2 := (Y !-> 1)).

  assert (PEq: pub_equiv LXP s1 s2).
  { clear Hc. intros x H. apply LXP_public in H. subst. reflexivity. }

  specialize (Hc s1 s2 PEq X LXPX).

  (* Computing reveals that the final value of [X] in [insecure_com1]
     depends on the initial [Y]. *)
  simpl in Hc. unfold s1, s2, t_update in Hc. simpl in Hc.

  (* Contradiction: LHS gives X = 1, RHS gives X = 2,
                    but Hc claims they're equal. *)
  discriminate Hc.
Qed.

(** **** Exercise: 2 stars, standard (interferent_insecure_com_explicit) *)
Definition insecure_com_explicit :=
  <{ X := Y * X; (* <- bad explicit flow! *)
     Y := Y - 1 }>.

Lemma interferent_insecure_com_explicit :
  ~noninterferent_no_while LXP insecure_com_explicit.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** Noninterference can be violated not only by explicit flows,
    but also by _implicit flows_, which leak secret information via
    the control-flow of the program. Here is a simple example: *)

Definition insecure_com2 : com :=
  <{ if Y = 0 then
       Y := 42
     else
       X := X+1 (* <- bad implicit flow! *)
     end }>.

(** Here the expression [X+1] we are assigning to [X] is public
    information, but we are doing this assignment after we branched on
    a secret condition [Y = 0], which indirectly leaks information
    about the value of [Y]: an attacker can infer that if [X] got
    incremented the initial value of [Y] was not [0]. *)

Lemma interferent_insecure_com2 :
  ~noninterferent_no_while LXP insecure_com2.
Proof.
  (* The same proof as for [insecure_com1] does the job *)
  unfold noninterferent_no_while, noninterferent_state, insecure_com1.
  intro Hc.

  (* Choose [s1] and [s2] that are pub_equiv but have different secret inputs. *)
  set (s1 := (X !-> 0 ; Y !-> 0)).
  set (s2 := (X !-> 0 ; Y !-> 1)).
  specialize (Hc s1 s2).

  assert (PEq: pub_equiv LXP s1 s2).
  { clear Hc. intros x H. apply LXP_public in H. subst. reflexivity. }

  specialize (Hc PEq X LXPX).

  (* Computing reveals that X in [insecure_com2] depends on the initial Y. *)
  simpl in Hc. unfold s1, s2, t_update in Hc. simpl in Hc.

  (* Contradiction: LHS gives X = 0, RHS gives X = 1,
                    but Hc claims they're equal. *)
  discriminate Hc.
Qed.

(** **** Exercise: 3 stars, standard (interferent_insecure_com_implicit) *)
Definition insecure_com_implicit :=
  <{ if Y = 42 then
       X := X - 1 (* <- bad implicit flow! *)
     else
       Y := 2 * Y
     end }>.

Lemma interferent_insecure_com_implicit :
  ~noninterferent_no_while LXP insecure_com_implicit.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** We will return to explicit and implicit flows in the [StaticIFC] chapter. *)

(* ################################################################# *)
(** * Optional: SME for Imp programs without loops *)

(** We can use [sme_state] on such insecure programs to obtain a
    noninterferent state transformer which runs programs 2 times, once
    on a state where the secrets are zeroed out and once on the
    original input state, and then merging the final states. *)

Print sme_state.
(*  fun f L s => merge_states (f (split_state s L public)) (f s) L. *)

Definition sme_no_while (c:com) : label_map -> state -> state :=
  sme_state (cinterp c).

(** The result of applying [sme_no_while] to a program is not a
    program, but a state transformer. *)

(** We prove noninterference and transparency for the state
    transformers obtained by [sme_no_while] using our noninterference
    and transparency theorems about [sme_state]: *)

Theorem noninterferent_sme_no_while : forall c L,
  noninterferent_state L (sme_no_while c L).
Proof. intros c p. apply noninterferent_sme_state. Qed.

Theorem transparent_sme_no_while : forall c L,
    noninterferent_state L (cinterp c) ->
    forall s, cinterp c s = sme_no_while c L s.
Proof.
  unfold sme_no_while. intros c L NI.
  apply transparent_sme_state. apply NI.
Qed.

(** Perhaps more interesting is to look at how [sme_no_while]
    changes the behavior of some insecure commands: *)

Print insecure_com1. (* <{ X := Y + 1; Y := X - 1 + Y * 2 }> *)
Definition secure_com1 : com :=
  <{ X := 1; (* no explicit flow *)
     Y := Y*3 (* but Y has to be computed in a different way *) }>.

Lemma sme_insecure_com1 :
  sme_no_while insecure_com1 LXP = cinterp secure_com1.
Proof.
  apply functional_extensionality. intros st.
  unfold sme_no_while, sme_state, insecure_com1, secure_com1. simpl.
  (* Both runs update the secret [Y]; the merge keeps the secret run's. *)
  rewrite merge_states_update_sec; try reflexivity.
  (* Both runs update the public [X]; the merge keeps the public run's. *)
  rewrite merge_states_update_pub; try reflexivity.
  (* Merging the public projection with [st] gives back [st]. *)
  rewrite merge_state_pub_equiv; try apply pub_equiv_split_state.
  (* Both sides update [X] then [Y] over [st].  The values of [X]
     agree definitionally (they are both [1]), so [f_equal] leaves
     only the values of [Y], which we show are the same in the two runs: *)
  f_equal.
  repeat rewrite t_update_eq.
  repeat (rewrite t_update_neq; try (intro c; discriminate)).
  lia.
Qed.

(** The example above shows that the effect of applying [sme_no_while]
    is hard to predict statically and it is not just a simple
    syntactic transformation of the original command. *)

(** Here is another example of that: *)

Definition insecure_com2' : com :=
  <{ if Y = 0 then
       X := 42  (* <- bad implicit flow! *)
     else
       X := X + 1 (* <- bad implicit flow! *)
     end }>.

Definition secure_com2' : com :=
  <{ X := 42 (* <- no implicit flow (no branching) *) }>.

Lemma sme_insecure_com2' :
  sme_no_while insecure_com2' LXP = cinterp secure_com2'.
Proof.
  apply functional_extensionality. intros st.
  unfold sme_no_while, sme_state, insecure_com2', secure_com2'. simpl.
  (* The public run takes the [then] branch (it sees [Y = 0]); the secret
     run branches on [st Y].  Either way both runs update [X], and the
     merge keeps the public run's value [42]. *)
  destruct (st Y =? 0)%nat.
  - rewrite merge_states_update_pub; [|reflexivity].
    rewrite merge_state_pub_equiv; [reflexivity|].
    apply pub_equiv_split_state.
  - rewrite merge_states_update_pub; [|reflexivity].
    rewrite merge_state_pub_equiv; [reflexivity|].
    apply pub_equiv_split_state.
Qed.

(** For simplicity, above we looked at a modified [insecure_com2'].
    What about the effect of [sme_no_while] on the _original_ [insecure_com2]? *)
Print insecure_com2.
  (* <{ if Y = 0 then *)
  (*      Y := 42  <- updating Y here *)
  (*    else *)
  (*      X := X+1 <- bad implicit flow! *)
  (*    end }>. *)

(** This is more challenging, but it turns out there is a general and
    systematic way to characterize the effect of [sme_no_while] as a single
    program. We borrow ideas from _self-composition_ [Barthe et al 2004] (in Bib.v)
    and construct one program that captures two executions of the
    original program. In our case the two executions are the ones
    performed by [sme_no_while]: first a secret execution on the unmodified
    initial state and then a public execution with zeroed out secret
    variables. Finally, we merge the results of these two executions. *)

Definition pX := "pX"%string.
Definition pY := "pY"%string.
Definition secure_com2 :=
  <{ (* we save a copy of the initial values of public variables *)
     pX := X;
     (* we run the original program to simulate the secret run *)
     if Y = 0 then Y := 42
              else X := X+1 end; (* <- X later overwritten *)
     (* for the public run we zero the [p]-version of secret variables *)
     pY := 0;
     (* we simulate the effect of the public run using the [p] variables *)
     if pY = 0 then pY := 42
               else pX := pX+1 end; (* <- the branching is on pY *)
     (* we merge the results of the two runs *)
     X := pX
}>.

(** Because in our simple Imp language we have no way to restore the
    [pX] and [pY] variables to their original state, the equivalence
    lemma below needs to account for the fact that their values will be
    different. We do this by reusing our old friend [pub_equiv]: *)

Definition psecret := (pX !-> secret; pY !-> secret; __ !-> public).

Lemma sme_insecure_com2 : forall st,
    pub_equiv psecret (sme_no_while insecure_com2 LXP st)
                      (cinterp secure_com2 st).
Proof.
  intros st.
  (* The left side collapses directly: the public run takes the [then]
     branch and updates the secret [Y], and the merge keeps secret
     variables from the secret run and public ones from the public run.
     We reuse the [merge_states_update_*] lemmas. *)
  assert (HL : sme_no_while insecure_com2 LXP st
               = if (st Y =? 0)%nat then (Y !-> 42; st) else st).
  { unfold sme_no_while, sme_state, insecure_com2. simpl.
    destruct (st Y =? 0)%nat.
    - rewrite merge_states_update_sec; [|reflexivity].
      rewrite merge_state_pub_equiv; [reflexivity|].
      apply pub_equiv_split_state.
    - rewrite merge_states_update_sec_fst; [|reflexivity].
      rewrite merge_states_update_pub_snd; [|reflexivity].
      rewrite merge_state_pub_equiv; [reflexivity|].
      apply pub_equiv_split_state. }
  rewrite HL.
  (* It remains to compare with [secure_com2], which also writes
     the auxiliary secret variables [pX] and [pY].  This part is an
     ordinary variable-by-variable check. *)
  unfold pub_equiv. intros x PSEC.
  assert (HpXY: x <> pX /\ x <> pY).
  { unfold psecret in PSEC.
    destruct (eqb x pX) eqn:HpX.
    - rewrite eqb_eq in HpX. subst.
      rewrite t_update_eq in PSEC. discriminate.
    - destruct (eqb x pY) eqn:HpY.
      + rewrite eqb_eq in HpY. subst.
        rewrite t_update_neq in PSEC; discriminate.
      + rewrite eqb_neq in HpX. rewrite eqb_neq in HpY. auto. }
  destruct HpXY as [HpX HpY].
  unfold secure_com2. simpl.

  (* The interpreter's inner branch also tests [st Y] (read via [pX := X]). *)
  assert (HcY : (pX !-> st X; st) Y = st Y).
  { apply t_update_neq. intro c. discriminate. }
  rewrite HcY.

  (* Both sides now branch on [st Y =? 0]; check each variable. *)
  destruct (st Y =? 0)%nat; destruct (String.eqb_spec x X);
  destruct (String.eqb_spec x Y); subst;
  (repeat rewrite t_update_eq);
  (repeat (rewrite t_update_neq; [| congruence]));
  reflexivity.
Qed.

(** By optimizing the [secure_com2] program above quite a bit we
    can finally figure out what [sme_no_while] does for [insecure_com2]: *)

Definition secure_com2_simple :=
  <{ if Y = 0 then
       Y := 42
     else
       skip (* <- implicit flow gone *)
     end
}>.

Lemma sme_insecure_com2_simple :
  sme_no_while insecure_com2 LXP = cinterp secure_com2_simple.
Proof.
  apply functional_extensionality. intros st.
  unfold sme_no_while, sme_state, insecure_com2, secure_com2_simple. simpl.
  (* The public run always takes the [then] branch (it sees [Y = 0]) and
     updates the secret [Y]; the secret run branches on [st Y]. *)
  destruct (st Y =? 0)%nat.
  - (* Both runs update the secret [Y]; the merge keeps the secret run's. *)
    rewrite merge_states_update_sec; [|reflexivity].
    rewrite merge_state_pub_equiv; [reflexivity|].
    apply pub_equiv_split_state.
  - (* The public run updated the secret [Y] (dropped by the merge) and
       the secret run updated the public [X] (also dropped), leaving [st]. *)
    rewrite merge_states_update_sec_fst; [|reflexivity].
    rewrite merge_states_update_pub_snd; [|reflexivity].
    rewrite merge_state_pub_equiv; [reflexivity|].
    apply pub_equiv_split_state.
Qed.

(** As mentioned above, to construct [secure_com2] we used ideas
    from self-composition [Barthe et al 2004] (in Bib.v).  Self-composition
    and the more general concept of a _product program_
    [Barthe et al 2011] (in Bib.v) are generally useful techniques of their
    own (e.g., for reducing relational properties proved by Relational
    Hoare Logic to regular properties proved by standard Hoare Logic),
    but we will not discuss them here any further. *)

(* ################################################################# *)
(** * Noninterference for Imp programs with loops *)

(** In the presence of loops, we need to define noninterference using the
    evaluation relation of Imp ([ceval]): *)

Definition noninterferent_com L c := forall s1 s2 s1' s2',
  pub_equiv L s1 s2 ->
  s1 =[ c ]=> s1' ->
  s2 =[ c ]=> s2' ->
  pub_equiv L s1' s2'.

Ltac invert H := inversion H; subst; clear H.

(** We re-prove noninterference of [secure_com] for this new definition: *)

Print secure_com. (* = <{ X := X+1; Y := (X-1)+Y*2 }> *)

Lemma noninterferent_secure_com_a_bit_harder :
  noninterferent_com LXP secure_com.
Proof.
  unfold noninterferent_com, secure_com, pub_equiv.
  intros s1 s2 s1' s2' H H1 H2 x Hx.
  apply LXP_public in Hx. subst.
  (* the proof is the same, but with additional ugly [invert]s *)
  invert H1. invert H4. invert H7.
  invert H2. invert H3. invert H6. simpl.
  rewrite (H X LXPX). reflexivity.
Qed.

(** Before turning to loops, here are two exercises on applying the
    new [noninterferent_com] definition to a couple other simple
    loop-free programs. *)

(** **** Exercise: 2 stars, standard (noninterferent_incX) *)
Lemma noninterferent_incX :
  noninterferent_com LXP <{ X := X + 1 }>.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard (interferent_YtoX_com) *)
Lemma interferent_YtoX_com :
  ~ noninterferent_com LXP <{ X := Y }>.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** The advantage of the new definition is that it also says
    something meaningful about programs with while loops, since it
    uses a proper semantics for such loops. *)

(** For instance, we can prove that [subtract_slowly] from
    [Imp] does not leak the initial value of [Z] to [X]: *)

Print subtract_slowly.
(* = <{ while X <> 0 do *)
(*        Z := Z - 1;   *)
(*        X := X - 1    *)
(*      end }>.         *)

(** To prove this we use the fact that in this example the final
    value of [X] is constant [0].  The general observation is that a
    [while] loop can only stop once its guard has become false: *)

Lemma while_ends_guard_false : forall b c s s',
  s =[ while b do c end ]=> s' -> beval s' b = false.
Proof.
  intros b c s s' H.
  remember <{ while b do c end }> as loopdef eqn:Eq.
  generalize dependent Eq.
  induction H; intros; try discriminate Eq.
  - (* E_WhileFalse: the loop stopped, so the guard is false *)
    invert Eq. assumption.
  - (* E_WhileTrue: the IH gives the guard false after the rest *)
    invert Eq. apply IHceval2. reflexivity.
Qed.

(** For [subtract_slowly] the guard is [X <> 0], so once the
    loop stops [X] must be [0]: *)

Lemma subtract_slowly_leaves_X_eq_0 : forall s s',
  s =[ subtract_slowly ]=> s' -> s' X = 0.
Proof.
  intros s s' H. unfold subtract_slowly in H.
  apply while_ends_guard_false in H.
  simpl in H. rewrite negb_false_iff in H.
  rewrite Nat.eqb_eq in H. apply H.
Qed.

Lemma noninterferent_subtract_slowly_LXP :
  noninterferent_com LXP subtract_slowly.
Proof.
  unfold noninterferent_com, pub_equiv.
  intros s1 s2 s1' s2' H H1 H2 x Hx.
  apply LXP_public in Hx. subst.
  apply subtract_slowly_leaves_X_eq_0 in H1. rewrite H1.
  apply subtract_slowly_leaves_X_eq_0 in H2. rewrite H2.
  reflexivity.
Qed.

Print subtract_slowly.
(* = <{ while X <> 0 do *)
(*        Z := Z - 1;   *)
(*        X := X - 1    *)
(*      end }>.         *)

(** We now change to a different label map [LZP], for which
    [subtract_slowly] is not secure. This is a nice example of leakage
    through an implicit flow: the number of loop iterations depends on
    the secret [X], and each iteration decreases the public [Z], so
    the final value of [Z] leaks the initial value of [X]. *)

Definition LZP : label_map := (Z !-> public; __ !-> secret).

Lemma LZP_public : forall x, LZP x = public -> x = Z.
Proof.
  unfold LZP. intros x Hx.
  destruct (eqb_spec x Z).
  - subst. reflexivity.
  - rewrite t_update_neq in Hx.
    + rewrite t_apply_empty in Hx. discriminate.
    + intro contra. subst. contradiction.
Qed.

Lemma interferent_subtract_slowly_LZP :
  ~noninterferent_com LZP subtract_slowly.
Proof.
  unfold noninterferent_com, subtract_slowly, pub_equiv.
  intros Hc.
  remember (X !-> 1; Z !-> 2) as s1.
  remember (X !-> 0; Z !-> 2) as s2.
  (* [s1] (with [X = 1]) runs the loop body once and ends in [s1']... *)
  remember (X !-> 0; Z !-> 1; X !-> 1; Z !-> 2) as s1'.
  (* ... while [s2] (with [X = 0]) doesn't enter the loop, so [s2' = s2]. *)
  remember (X !-> 0; Z !-> 2) as s2'.
  specialize (Hc s1 s2 s1' s2').
  assert (contra: s1' Z = s2' Z).
  { eapply Hc.
    - intros. eapply LZP_public in H. subst.
      rewrite t_update_neq; [| discriminate].
      rewrite t_update_eq.
      rewrite t_update_neq; [| discriminate].
      rewrite t_update_eq. reflexivity.
    - eapply E_WhileTrue with (st':= s1').
      + subst. simpl. reflexivity.
      + unfold subtract_slowly_body. eapply E_Seq.
        * eapply E_Asgn. reflexivity.
        * subst. simpl. eapply E_Asgn. reflexivity.
      + eapply E_WhileFalse. subst. simpl. reflexivity.
    - subst. eapply E_WhileFalse. simpl. reflexivity.
    - unfold LZP. rewrite t_update_eq. reflexivity. }
  subst. rewrite t_update_neq in contra; [| discriminate].
  rewrite t_update_eq in contra.
  rewrite t_update_neq in contra; [| discriminate].
  rewrite t_update_eq in contra. discriminate contra.
Qed.

(** **** Exercise: 2 stars, standard, optional (noninterferent_fact_in_coq_LXP)

    As an exercise, we prove that [fact_in_coq] from [Imp] does
    not leak the initial value of [Y] or [Z] to [X]: *)

Print fact_in_coq.
(* = <{ Z := X;                    *)
(*      Y := 1;                    *)
(*      while Z <> 0 do            *)
(*        Y := Y * Z;              *)
(*        Z := Z - 1               *)
(*      end }>.                    *)

(** One reason for this is that the variable [X] is never assigned.
    We capture this once and for all: a command leaves unchanged every
    variable to which it does not assign: *)

Fixpoint assigned_in (c : com) (x : string) : bool :=
  match c with
  | <{ skip }> => false
  | <{ y := _ }> => (x =? y)%string
  | <{ c1 ; c2 }> => assigned_in c1 x || assigned_in c2 x
  | <{ if _ then c1 else c2 end }> =>
      assigned_in c1 x || assigned_in c2 x
  | <{ while _ do c1 end }> => assigned_in c1 x
  end.

Lemma ceval_preserves_unassigned : forall c s s' x,
  s =[ c ]=> s' -> assigned_in c x = false -> s x = s' x.
Proof.
  intros c s s' x Heval. induction Heval; simpl; intros Hna.
  - reflexivity.
  - apply String.eqb_neq in Hna.
    rewrite t_update_neq; [reflexivity | congruence].
  - apply orb_false_iff in Hna. destruct Hna as [H1 H2].
    rewrite IHHeval1; [| assumption]. apply IHHeval2. assumption.
  - apply orb_false_iff in Hna. apply IHHeval. apply Hna.
  - apply orb_false_iff in Hna. apply IHHeval. apply Hna.
  - reflexivity.
  - rewrite IHHeval1; [| assumption]. apply IHHeval2. assumption.
Qed.

(** Hence [fact_in_coq] leaves [X] unchanged: it only assigns [Z] and
    [Y], never [X]. *)
Lemma fact_in_coq_preserves_X : forall s s',
  s =[ fact_in_coq ]=> s' -> s X = s' X.
Proof.
  intros s s' H. eapply ceval_preserves_unassigned.
  - apply H.
  - reflexivity.
Qed.

Lemma noninterferent_fact_in_coq_LXP :
  noninterferent_com LXP fact_in_coq.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (noninterferent_fact_in_coq_LZP)

    The same [fact_in_coq] is _also_ noninterferent under the labeling
    [LZP], where [Z] is public and [X], [Y] are secret -- but for a very
    different reason than under [LXP].  Here [Z] _is_ assigned (indeed
    [Z := X] even copies the secret [X] into it!), yet the loop
    [while Z <> 0 do ...; Z := Z - 1 end] then drives [Z] back down to
    [0], so the final [Z] is [0] no matter what the secrets were.
    (This is analogous to [subtract_slowly] leaving [X] equal to [0].) *)

Lemma fact_in_coq_leaves_Z_eq_0 : forall s s',
  s =[ fact_in_coq ]=> s' -> s' Z = 0.
Proof.
  unfold fact_in_coq. intros s s' H0. invert H0. invert H5.
  apply while_ends_guard_false in H6.
  simpl in H6. rewrite negb_false_iff in H6.
  rewrite Nat.eqb_eq in H6. apply H6.
Qed.

Lemma noninterferent_fact_in_coq_LZP :
  noninterferent_com LZP fact_in_coq.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ################################################################# *)
(** * SME for Imp programs with loops *)

(** The definition of SME in the presence of while loops also needs to
    be a relation, of a similar type to [ceval]: *)

Check ceval : com -> state -> state -> Prop.

Definition sme_com (L:label_map) (c:com) (s s':state) : Prop :=
  exists ps ss, split_state s L public =[ c ]=> ps /\
    s =[ c ]=> ss /\
    merge_states ps ss L = s'.

(** **** Exercise: 2 stars, standard (sme_com_YtoX)

    As a warm-up, here is a concrete computation showing how
    [sme_com] changes the behavior of a leaky program:
    running [X := Y] under SME sets [X] to [0],
    because the secret [Y] is zeroed out in the public run.

    (Hint: For extra elegance [merge_states_update_pub],
    [merge_state_pub_equiv], and [pub_equiv_split_state] let you
    discharge the final [merge_states] goal without unfolds.) *)

Lemma sme_com_YtoX :
  sme_com LXP <{ X := Y }> (Y !-> 5) (X !-> 0; Y !-> 5).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** To state that [sme_com] is secure, we need to generalize our noninterference
    definition, so that we can apply it not only to [ceval], but to
    any evaluation relation, including [sme_com L]. *)

Definition noninterferent_com_R (R:com->state->state->Prop) L c :=
  forall s1 s2 s1' s2',
  pub_equiv L s1 s2 ->
  R c s1 s1' ->
  R c s2 s2' ->
  pub_equiv L s1' s2'.

(** The proof that [sme_com] is noninterferent is as before, but now it relies
    on the determinism of [ceval], which was obvious for state transformer
    functions, but is not obvious for evaluation relations. *)

Check ceval_deterministic : forall (c : com) (st st1 st2 : state),
    st =[ c ]=> st1 ->
    st =[ c ]=> st2 ->
    st1 = st2.

Theorem noninterferent_com_sme : forall L c,
  noninterferent_com_R (sme_com L) L c.
Proof.
  unfold noninterferent_com_R, sme_com.
  intros L c s1 s2 s1' s2' H [ps1 [ss1 [H1p [H1s H1m]]]]
                             [ps2 [ss2 [H2p [H2s H2m]]]].
  subst. rewrite pub_equiv_split_iff in H. unfold pub_equiv_split in H.
  apply functional_extensionality in H. rewrite H in H1p.
  rewrite (ceval_deterministic _ _ _ _ H1p H2p).
  apply pub_equiv_merge_states.
Qed.

(** Turns out we can only prove a weak version of transparency for
    noninterferent programs, and this has to do with nontermination
    (more later). *)

(** More specifically, we can only prove that an [sme_com] execution
    implies a [ceval] execution: *)

Theorem somewhat_transparent_sme_com : forall L c,
  noninterferent_com L c ->
  (forall s s', (sme_com L) c s s' -> s =[ c ]=> s').
Proof.
  unfold noninterferent_com, sme_com.
  intros L c Hni s s' [ps [ss [Hp [Hs Hm]]]]. subst s'.
    assert(H:pub_equiv L s (split_state s L public)).
    { apply pub_equiv_sym. apply pub_equiv_split_state. }
    specialize (Hni s (split_state s L public) ss ps H Hs Hp).
    apply pub_equiv_sym in Hni. apply merge_state_pub_equiv in Hni.
    rewrite Hni. apply Hs.
Qed.

(** But we cannot prove the reverse implication, since a command
    terminating when starting in state [s], does not necessarily still
    terminate when starting in state [split_state s L public], as
    would be needed for proving [sme_com]. *)

(** The _program partitioning_ mechanism from [StaticIFC] will
    overcome precisely this limitation: instead of running the whole
    program on the state with the secrets zeroed out, it runs only its
    _public slice_, which drops the code guarded by secrets, and thus
    terminates whenever the original program terminates. This will
    make partitioned execution enforce noninterference for all
    programs, while being _fully transparent_ for the well-typed ones. *)

(** Yet it seems we can still do most of the things as in the setting
    without while loops, including SME (just not fully transparent).
    So is there anything special about loops and nontermination?

    Yes, there is! Let's look at our noninterference definition again:

Definition noninterferent_com L c := forall s1 s2 s1' s2',
  pub_equiv L s1 s2 ->
  s1 =[ c ]=> s1' ->
  s2 =[ c ]=> s2' ->
  pub_equiv L s1' s2'.

    It says that for any two _terminating_ executions, if the initial states
    agree on their public variables, then so do the final states. This is
    traditionally called _termination-insensitive_ noninterference (TINI),
    since it doesn't consider nontermination to be observable to an attacker. *)

(** In particular, the following program is _secure_ wrt TINI: *)

Definition termination_leak : com :=
  <{ if Y = 0                    (* Y is a secret variable *)
     then while true do skip end (* if Y = 0 run forever *)
     else skip                   (* if Y <> 0 terminate immediately *)
     end }>.

(** We use a lemma that is a homework exercise in Imp: *)
Check loop_never_stops : forall st st',
  ~(st =[ loop ]=> st').

Definition tini_secure_termination_leak :
  noninterferent_com LXP termination_leak.
Proof.
  unfold noninterferent_com, termination_leak, pub_equiv.
  intros s1 s2 s1' s2' H H1 H2 x Hx. apply LXP_public in Hx.
  subst. specialize (H X LXPX).
  invert H1.
  + apply loop_never_stops in H8. contradiction.
  + invert H8. invert H2.
    * apply loop_never_stops in H8. contradiction.
    * invert H8. assumption.
Qed.

(* ################################################################# *)
(** * Termination-Sensitive Noninterference *)

(** We can give a stronger definition of security that disallows such
    nontermination leaks. It is traditionally called
    _termination-sensitive noninterference_ (TSNI) and it is defined
    as follows: *)

Definition tsni_com_R (R:com->state->state->Prop) L c :=
  forall s1 s2 s1',
  R c s1 s1' ->
  pub_equiv L s1 s2 ->
  (exists s2', R c s2 s2' /\ pub_equiv L s1' s2').

(** First a simple program that does satisfy TSNI.  Note that, unlike for
    [noninterferent_com], you now have to _exhibit_ the second run and
    show it terminates (the [exists s2']). *)

(** **** Exercise: 2 stars, standard (tsni_incX) *)
Lemma tsni_incX : tsni_com_R ceval LXP <{ X := X + 1 }>.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** We can prove that [termination_leak] doesn't satisfy TSNI: *)

Definition tsni_insecure_termination_leak :
  ~tsni_com_R ceval LXP termination_leak.
Proof.
  unfold tsni_com_R, termination_leak.
  intros Hc.
  specialize (Hc (X !-> 0 ; Y !-> 1) (X !-> 0 ; Y !-> 0)
                 (X !-> 0 ; Y !-> 1)).
  assert (HH : (X !-> 0; Y !-> 1) =[ termination_leak ]=>
               (X !-> 0; Y !-> 1)).
  { clear. unfold termination_leak. apply E_IfFalse.
    - reflexivity.
    - apply E_Skip. }
  specialize (Hc HH). clear HH.
  assert (H: forall x, LXP x = public ->
                       (X !-> 0; Y !-> 1) x = (X !-> 0; Y !-> 0) x).
  { clear Hc. intros x H. apply LXP_public in H. subst. reflexivity. }
  specialize (Hc H). clear H.
  destruct Hc as [s2' [Hc _]].
  invert Hc.
  - apply loop_never_stops in H5. contradiction.
  - simpl in H4. discriminate.
Qed.

(** More generally, we can prove that TSNI is strictly stronger than
    TINI (noninterferent_com). *)

Lemma tsni_noninterferent : forall L c,
  tsni_com_R ceval L c ->
  noninterferent_com_R ceval L c.
Proof.
  unfold noninterferent_com_R, tsni_com_R.
  intros L c Htsni s1 s2 s1' s2' Hequiv H1 H2.
  specialize (Htsni s1 s2 s1' H1 Hequiv).
  destruct Htsni as [s2'' [H2' Hequiv']].
  rewrite (ceval_deterministic _ _ _ _ H2 H2').
  apply Hequiv'.
Qed.

(** The reverse direction of the implication doesn't hold in general,
    and we already proved above that the program called
    [termination_leak] is a counterexample: *)

Lemma noninterferent_not_tsni :
  ~ (forall L c, noninterferent_com_R ceval L c ->
                 tsni_com_R ceval L c).
Proof.
  intros H. apply tsni_insecure_termination_leak.
  apply H. apply tini_secure_termination_leak.
Qed.

(** The reverse direction of the implication only holds for programs
    that always terminate (such as most of our simple examples above,
    except [termination_leak]). *)

Lemma terminating_noninterferent_tsni: forall L c,
  (forall s, exists s', s =[ c ]=> s') ->
  noninterferent_com_R ceval L c ->
  tsni_com_R ceval L c.
Proof.
  unfold noninterferent_com_R, tsni_com_R.
  intros L c Hterminating Hni s1 s2 s1' H Eq.
  destruct (Hterminating s2) as [s2' H'].
  exists s2'; split; [assumption|].
  apply Hni with (s1 := s1) (s2 := s2); assumption.
Qed.

(** For instance, since [subtract_slowly] terminates on every initial
    state ([X] counts down to [0]), TSNI follows from
    [terminating_noninterferent_tsni]. *)

Lemma subtract_slowly_terminates : forall s,
  exists s', s =[ subtract_slowly ]=> s'.
Proof.
  unfold subtract_slowly. intros s. remember (s X) as n eqn:Hn.
  generalize dependent s. induction n as [| n IH]; intros s Hn.
  - exists s. apply E_WhileFalse. simpl. rewrite <- Hn. reflexivity.
  - assert (Hn'' : n = (X !-> s X - 1; Z !-> s Z - 1; s) X).
    { rewrite t_update_eq. lia. }
    destruct (IH _ Hn'') as [s' Hs'].
    exists s'. eapply E_WhileTrue with (st' := (X !-> s X - 1; Z !-> s Z - 1; s)).
    + simpl. rewrite <- Hn. reflexivity.
    + unfold subtract_slowly_body. eapply E_Seq.
      * eapply E_Asgn. reflexivity.
      * eapply E_Asgn. reflexivity.
    + apply Hs'.
Qed.

Definition tsni_secure_subtract_slowly :
  tsni_com_R ceval LXP subtract_slowly.
Proof.
  apply terminating_noninterferent_tsni.
  - apply subtract_slowly_terminates.
  - apply noninterferent_subtract_slowly_LXP.
Qed.

(** Now for a more interesting use of TSNI: it turns out that
    [sme_com] is fully transparent for programs satisfying TSNI. *)

Theorem tsni_transparent_sme_com : forall L c,
  tsni_com_R ceval L c ->
  (forall s s', s =[ c ]=> s' <-> (sme_com L) c s s').
Proof.
  unfold tsni_com_R, sme_com.
  intros L c Hni s s'.
  assert(HH:pub_equiv L s (split_state s L public)).
    { apply pub_equiv_sym. apply pub_equiv_split_state. }
  split.
  - intros H. specialize (Hni s (split_state s L public) s' H HH).
    destruct Hni as [s'' [Heval Hequiv]].
    exists s''. exists s'. split.
    + assumption.
    + split.
      * assumption.
      * apply merge_state_pub_equiv. apply pub_equiv_sym. assumption.
  - intros [ps [ss [Hp [Hs Hm]]]]. subst s'.
    specialize (Hni s (split_state s L public) ss Hs HH).
    destruct Hni as [s' [Hp' Hni]].
    rewrite (ceval_deterministic _ _ _ _ Hp Hp').
    apply pub_equiv_sym in Hni. apply merge_state_pub_equiv in Hni.
    rewrite Hni. apply Hs.
Qed.

(** Unfortunately [sme_com] does not _enforce_ TSNI and this is hard
    to fix in our current setting, where programs only return a result
    in the end, a final state, which for [sme_com] merges the results
    of the public and the secret executions. Instead, SME is commonly
    defined in a setting with interactive IO, in which public outputs
    and secret outputs can be performed independently, during the
    execution [Devriese and Piessens 2010] (in Bib.v). In that setting,
    an SME version was proved to transparently enforce a version of
    noninterference called Indirect TSNI [Ngo et al 2018] (in Bib.v). *)

(* ================================================================= *)
(** ** Optional: Counterexample showing that SME doesn't enforce TSNI *)

(** We build a counterexample command that does not satisfy TSNI and
    for which the same publicly equivalent initial states [s1] and
    [s2] can be used to show that it still does not satisfy TSNI when
    run with [sme_com].

    In particular, we choose [s1] below so that the command terminates
    and so that zeroing out the secret variable Y has no effect on [s1].
    We choose [s2] so that the command loops, which implies that it
    will still loop on [s2] also when executed with [sme_com]. *)

Section TSNICOUNTER.

Definition counter : com := <{ while (Y = 1) do skip end; X := 1 }>.

Definition s1: state := X !-> 0; Y !-> 0; empty_st.
Definition s2: state := X !-> 0; Y !-> 1; empty_st.
Definition s1': state := X !-> 1; s1.

Lemma counter_s1_terminates_s1': s1 =[ counter ]=> s1'.
Proof.
  unfold counter, s1. eapply E_Seq.
  - eapply E_WhileFalse. simpl. reflexivity.
  - eapply E_Asgn. simpl. reflexivity.
Qed.

Lemma counter_s2_loops : forall s2',
  ~ (s2 =[ counter ]=> s2').
Proof.
  unfold counter. intros s2' Hcontra.

  assert (NSTOP: forall s s', s Y = 1 ->
                         s =[ while Y = 1 do skip end ]=> s' ->
                         False).
  { clear. intros.
    remember <{ while Y = 1 do skip end }> as loopdef
             eqn:Heqloopdef.
    generalize dependent H.
    induction H0; try (discriminate Heqloopdef).
    (* E_WhileFalse *)
    - intros HY.
      injection Heqloopdef as H0 H1. subst.
      simpl in H. rewrite HY in H. discriminate H.
    (* E_WhileTrue *)
    - intros HY.
      injection Heqloopdef as H0 H1. subst.
      inversion H0_; subst. eapply IHceval2; eauto. }

  inversion Hcontra; subst. eapply NSTOP in H1; auto.
Qed.

Lemma initial_pub_equiv: pub_equiv LXP s1 s2.
Proof.
  unfold s1, s2, pub_equiv. intros.
  eapply LXP_public in H. subst.
  repeat rewrite t_update_eq. reflexivity.
Qed.

Lemma not_tsni_counter :
  ~ (tsni_com_R ceval LXP counter).
Proof.
  intros Htsni. unfold tsni_com_R in Htsni.
  specialize (Htsni _ _ _ counter_s1_terminates_s1' initial_pub_equiv).
  destruct Htsni as [s2' [D _]].
  eapply counter_s2_loops. eassumption.
Qed.

Lemma sme_counter_s1_terminates_s1' : sme_com LXP counter s1 s1'.
Proof.
  unfold sme_com, counter.
  exists s1', s1'.
  split; [|split].
  - assert (Hsplit: split_state s1 LXP public = s1).
    { apply functional_extensionality. intros x.
      destruct (LXP x) eqn:Hx.
      - apply split_state_public_id. assumption.
      - (* [x] is secret, and [s1] is zero on all secret variables *)
        rewrite split_state_secret_zero; try assumption.
        unfold s1. symmetry.
        destruct (String.eqb_spec X x).
        + subst. apply t_update_eq.
        + rewrite t_update_neq; try assumption.
          destruct (String.eqb_spec Y x).
          * subst. apply t_update_eq.
          * rewrite t_update_neq; try assumption. apply t_apply_empty. }
    rewrite Hsplit. eapply counter_s1_terminates_s1'.
  - eapply counter_s1_terminates_s1'.
  - eapply functional_extensionality. intros x.
    unfold merge_states, LXP.
    destruct ((X !-> public; __ !-> secret) x); reflexivity.
Qed.

Lemma sme_counter_s2_loops: forall s2',
  ~ (sme_com LXP counter s2 s2').
Proof.
  unfold not, sme_com. intros s2' H.
  destruct H as [ps [ss [A [B C]]]].
  eapply counter_s2_loops. eassumption.
Qed.

Lemma not_tsni_sme_com :
  ~ (tsni_com_R (sme_com LXP) LXP counter).
Proof.
  intros Htsni. unfold tsni_com_R in Htsni.
  specialize (Htsni _ _ _ sme_counter_s1_terminates_s1' initial_pub_equiv).
  destruct Htsni as [s2' [D _]].
  eapply sme_counter_s2_loops. eassumption.
Qed.

End TSNICOUNTER.

(* 2026-08-23 16:10 *)
