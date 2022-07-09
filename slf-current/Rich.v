(** * Rich: Assertions, Loops, N-ary Functions *)

Set Implicit Arguments.
From SLF Require Import LibSepReference LibSepTLCbuffer.
From SLF Require Basic Repr.

Implicit Types P : Prop.
Implicit Types H : hprop.
Implicit Types Q : val->hprop.
Implicit Type p q : loc.
Implicit Type k : nat.
Implicit Type i n : int.
Implicit Type v : val.
Implicit Types b : bool.
Implicit Types L : list val.

(* ################################################################# *)
(** * First Pass *)

(** This chapter introduces support for additional language constructs:
    - assertions,
    - if-statements that are not in A-normal form (needed for loops)
    - while-loops,
    - n-ary functions (bonus contents).

    Regarding assertions, we present a reasoning rule such that:
    - assertions may access to mutable data,
    - assertions may perform local side-effects,
    - the program remains correct whether assertions are executed or not.

    Regarding loops, we explain why traditional Hoare-style reasoning rules
    based on loop invariants are limited, in that they prevent useful
    applications of the frame rule. We present alternative reasoning rules
    compatible with the frame rule, and demonstrate their benefits on
    practical examples.

    Regarding n-ary functions, that is, functions with several arguments,
    there are essentially three possible approaches:

    - native n-ary functions, e.g., [function(x, y) { t } ] in C syntax;
    - curried functions, e.g., [fun x => fun y => t] in OCaml syntax;
    - tupled functions, e.g., [fun (x,y) => t] in OCaml syntax.

    In this chapter, we describe the first two approaches. The third
    approach (tupled functions) would require product data types in
    the source language. *)

(* ================================================================= *)
(** ** Reasoning Rule for Assertions *)

Module Assertions.

(** Assume an additional primitive operation, allowing to write terms
    of the form [val_assert t], to dynamically check at runtime that the
    term [t] produces the boolean value [true], equivalently to the
    OCaml expression [assert(t)]. *)

Parameter val_assert : prim.

(** The reasoning rule for assertions should ensure that:

    - the body of the assertion always evaluates to [true],
    - the program remains correct if the assertion is not evaluated.

    Let us introduce a boolean flag to control the evaluation of
    assertions. The value of this flag is purposely left unspecified. *)

Parameter evaluate_assertions : bool.

(** The program should be correct for both possible values of
    [evaluate_assertions]. The semantics of the evaluation of assertions
    is formally captured by the following two rules.

    - The rule [eval_assert_enabled] applies when [evaluate_assertions]
      is set to [true]. The rule describes the evaluation of the body of
      the assertion, and the check that the output value is [true].
    - The rule [eval_assert_disabled] applies when [evaluate_assertions]
      is set to [false]. The rule totally ignores the body of the assertion.
      It treats the assertion as immediately returning the [unit] value,
      in the current state. *)

Parameter eval_assert_enabled : forall s t s',
  evaluate_assertions = true ->
  eval s t s' (val_bool true) ->
  eval s (val_assert t) s' val_unit.

Parameter eval_assert_disabled : forall s t,
  evaluate_assertions = false ->
  eval s (val_assert t) s val_unit.

(** Note that it might be tempting to consider a "unifying" evaluation rule
    that evaluates the body of the assertion, checks that the result is [true],
    and, moreover, imposes that the assertion does not modify the state. *)

Parameter eval_assert_no_effect : forall s t v,
  eval s t s (val_bool true) ->
  eval s (val_assert t) s val_unit.

(** Yet, such a rule would be overly restrictive, for two reasons. First, it
    might be useful for an assertion to allocate local data for evaluating
    a particular property. Second, there are useful examples of assertions
    that do modify existing cells from the heap. For example, an assertion
    that appears in real programs is [assert (find x = find y)], where the
    [find] operation finds the representative of a node from a Union-Find
    data structure, an operation that performs path compression. *)

(** At this point, our goal is to state a reasoning rule for [val_assert t]
    that does not depend on the value of the boolean flag [evaluate_assertions].
    In other words, we are seeking for a rule that is correct both with respect
    to [eval_assert_enabled] and with respect to [eval_assert_disabled].

    Consider the evaluation of [val_assert t] in a state described by [H].
    The output state should still be described by [H], although the internal
    representation of the state might have changed (e.g., for path compression
    in the case of a Union-Find data structure). The body of the assertion
    should evaluate correctly in a state described by [H], and should return
    the value [true], in an output state still described by [H].

    As usual for primitive operations, we first establish a rule for
    Hoare triples, then deduce a rule for Separation Logic triples. *)

Lemma hoare_assert : forall t H,
  hoare t H (fun r => \[r = true] \* H) ->
  hoare (val_assert t) H (fun _ => H).
Proof using.
  introv M. intros s K. forwards (s'&v&R&N): M K.
  rewrite hstar_hpure_l in N. destruct N as (->&K').
  (* There are two cases, depending on whether assertions are evaluated. *)
  case_eq evaluate_assertions; intros C.
  (* Case 1: assertions are enabled. *)
  { exists s' val_unit. split.
    { applys eval_assert_enabled C R. }
    { applys K'. } }
  (* Case 2: assertions are disabled. *)
  { exists s val_unit. split.
    { applys eval_assert_disabled C. }
    { applys K. } }
Qed.

Lemma triple_assert : forall t H,
  triple t H (fun r => \[r = true] \* H) ->
  triple (val_assert t) H (fun _ => H).
Proof using.
  introv M. intros H'. specializes M H'. applys hoare_assert.
  applys hoare_conseq M. { xsimpl. } { xsimpl. auto. }
Qed.

End Assertions.

(* ================================================================= *)
(** ** Semantics of Conditionals not in Administrative Normal Form *)

(** To state reasoning rule for while-loops in a concise manner, it is useful
    to generalize the construct [if b then t1 else t2] to the form
    [if t0 then t1 else t2]. *)

(** To specify the behavior of a term of the form [if t0 then t1 else t2],
    let us assume the evaluation rule shown below. This rule generalizes
    the rule [eval_if]. It first evaluates [t0] into a value [v0], then it
    evaluates the term [if v0 then t1 else t2]. *)

Parameter eval_if_trm : forall s1 s2 s3 v0 v t0 t1 t2,
  eval s1 t0 s2 v0 ->
  eval s2 (trm_if v0 t1 t2) s3 v ->
  eval s1 (trm_if t0 t1 t2) s3 v.

(** With respect to this evaluation rule [eval_if_trm], we can prove a
    correpsonding reasoning rule. We first state it in Hoare-logic, then
    in Separation Logic, following the usual proof pattern. *)

Lemma hoare_if_trm : forall Q' t0 t1 t2 H Q,
  hoare t0 H Q' ->
  (forall v, hoare (trm_if v t1 t2) (Q' v) Q) ->
  hoare (trm_if t0 t1 t2) H Q.
Proof using.
  introv M1 M2. intros s1 K1. lets (s2&v0&R2&K2): M1 K1.
  forwards (s3&v&R3&K3): M2 K2. exists s3 v. splits.
  { applys eval_if_trm R2 R3. }
  { applys K3. }
Qed.

Lemma triple_if_trm : forall Q' t0 t1 t2 H Q,
  triple t0 H Q' ->
  (forall v, triple (trm_if v t1 t2) (Q' v) Q) ->
  triple (trm_if t0 t1 t2) H Q.
Proof using.
  introv M1 M2. intros HF. applys hoare_if_trm (Q' \*+ HF).
  { applys hoare_conseq. applys M1 HF. { xsimpl. } { xsimpl. } }
  { intros v. applys M2. }
Qed.

(** The reasoning rule can also be reformulated in weakest-precondition form.
    The rule below generalizes the rule [wp_if]. *)

Lemma wp_if_trm : forall t0 t1 t2 Q,
  wp t0 (fun v => wp (trm_if v t1 t2) Q) ==> wp (trm_if t0 t1 t2) Q.
Proof using.
  intros. unfold wp. xsimpl; intros H M H'. applys hoare_if_trm.
  { applys M. }
  { intros v. simpl. rewrite hstar_hexists. applys hoare_hexists. intros HF.
    rewrite (hstar_comm HF). rewrite hstar_assoc. applys hoare_hpure.
    intros N. applys N. }
Qed.

(* ================================================================= *)
(** ** Semantics and Basic Evaluation Rules for While-Loops *)

Module WhileLoops.

(** Assume the grammar of term to be extended with a loop construct
    [trm_while t1 t2], corresponding to the OCaml expression
    [while t1 do t2], and written [While t1 Do t2 Done] in our
    example programs. *)

Parameter trm_while : trm -> trm -> trm.

Notation "'while' t1 'do' t2 'done'" :=
  (trm_while t1 t2)
  (in custom trm at level 0,
   t1 custom trm at level 99,
   t2 custom trm at level 99,
   format "'[v' 'while'  t1  'do'  '/' '['   t2 ']' '/'  'done' ']'")
   : trm_scope.

(** The semantics of this loop construct can be described in terms of the
    one-step unfolding of the loop: [while t1 do t2] is a term that
    behaves exactly like the term [if t1 then (t2; while t1 do t2) else ()]. *)

Parameter eval_while : forall s1 s2 t1 t2 v,
  eval s1 (trm_if t1 (trm_seq t2 (trm_while t1 t2)) val_unit) s2 v ->
  eval s1 (trm_while t1 t2) s2 v.

(** This evaluation rule translates directly into a reasoning rule:
    to prove a triple for the term [while t1 do t2], it suffices to
    prove a triple for the term [if t1 then (t2; while t1 do t2) else ()].

    There is a catch in that reasoning principle, namely the fact that
    the loop [while t1 do t2] appears again inside the term
    [if t1 then (t2; while t1 do t2) else ()]. Nevertheless, this is not
    a problem if the user is carrying out a proof by induction. In that
    case, an induction hypothesis about the behavior of [while t1 do t2]
    is available. We show an example proof further on.

    For the moment, let us state the reasoning rules. *)

Lemma hoare_while : forall t1 t2 H Q,
  hoare (trm_if t1 (trm_seq t2 (trm_while t1 t2)) val_unit) H Q ->
  hoare (trm_while t1 t2) H Q.
Proof using.
  introv M K. forwards* (s'&v&R1&K1): M.
  exists s' v. splits*. { applys* eval_while. }
Qed.

Lemma triple_while : forall t1 t2 H Q,
  triple (trm_if t1 (trm_seq t2 (trm_while t1 t2)) val_unit) H Q ->
  triple (trm_while t1 t2) H Q.
Proof using.
  introv M. intros H'. apply hoare_while. applys* M.
Qed.

Lemma wp_while : forall t1 t2 Q,
      wp (trm_if t1 (trm_seq t2 (trm_while t1 t2)) val_unit) Q
  ==> wp (trm_while t1 t2) Q.
Proof using.
  intros. repeat unfold wp. xsimpl; intros H M H'.
  applys hoare_while. applys M.
Qed.

(* ================================================================= *)
(** ** Separation-Logic-friendly Reasoning Rule for While-Loops *)

(** One may be tempted to introduce an invariant-based reasoning rule
    for while loops. Traditional invariant-based rules from Hoare
    logic usually admit a relatively simple statement, because they only
    target partial correctness, and because the termination condition
    is restricted to a simple expression that does not alter the state.

    In our set up, targeting total correctness and a construct of the
    form [trm_while t1 t2], the invariant-based reasoning rule can
    be stated as shown below.

    An invariant [I] describes the state at the entry and exit point
    of the loop. This invariant is actually of the form [I b X], where
    the boolean value [b] is [false] to indicate that the loop has terminated,
    and where the value [X] belongs to a type [A] used to express the
    decreasing measure that justifies the termination of the loop. *)

Lemma triple_while_inv_not_framable :
  forall (A:Type) (I:bool->A->hprop) (R:A->A->Prop) t1 t2,
  wf R ->
  (forall b X, triple t1 (I b X) (fun r => \exists b', \[r = b'] \* I b' X)) ->
  (forall b X, triple t2 (I b X) (fun _ => \exists b' Y, \[R Y X] \* I b' Y)) ->
  triple (trm_while t1 t2) (\exists b X, I b X) (fun r => \exists Y, I false Y).
Proof using.
  introv WR M1 M2. applys triple_hexists. intros b.
  applys triple_hexists. intros X.
  gen b. induction_wf IH: WR X. intros. applys triple_while.
  applys triple_if_trm (fun (r:val) => \exists b', \[r = b'] \* I b' X).
  { applys M1. }
  { intros v. applys triple_hexists. intros b'. applys triple_hpure. intros ->.
    applys triple_if. case_if.
    { applys triple_seq.
      { applys M2. }
      { applys triple_hexists. intros b''. applys triple_hexists. intros Y.
        applys triple_hpure. intros HR. applys IH HR. } }
    { applys triple_val. xsimpl. } }
Qed.

(** The above rule is correct yet limited, because it precludes the possibility
    to apply the frame rule "over the remaining iterations of the loop".

    This possibility can be exploited by carrying a proof by induction and
    invoking the rule [triple_while], which unfolds the loop body. In that
    scheme, the frame rule can be applied to the term [while t1 do t2] that
    occurs in the [if t1 then (t2; (while t1 do t2)) else ()]. *)

(** We can reduce the noise associated with applying the rule [triple_while]
    by assigning a name, say [t], to denote the term [while t1 do t2].
    The correpsonding rule, shown below, asserts that [t] admits the same
    behavior as the term [if t1 then (t2; t) else ()]. *)

Lemma triple_while' : forall t1 t2 H Q,
  (forall t,
     (forall H' Q', triple (trm_if t1 (trm_seq t2 t) val_unit) H' Q' ->
                    triple t H' Q') ->
    triple t H Q) ->
  triple (trm_while t1 t2) H Q.
Proof using.
  introv M. applys M. introv K. applys triple_while. applys K.
Qed.

(** The proof scheme that consists of setting up an induction then applying
    the reasoning rule [triple_while'] can be factored into the following lemma,
    which is stated using an invariant that appears only in the precondition.
    The postcondition is an abstract [Q]. With this presentation, the rule
    features an "invariant", yet it remains possible to invoke the frame rule
    over the "remaining iterations" of the loop. *)

Lemma triple_while_inv :
  forall (A:Type) (I:bool->A->hprop) (R:A->A->Prop) t1 t2,
  let Q := (fun r => \exists Y, I false Y) in
  wf R ->
  (forall t b X,
    (forall b' Y, R Y X -> triple t (I b' Y) Q) ->
    triple (trm_if t1 (trm_seq t2 t) val_unit) (I b X) Q) ->
  triple (trm_while t1 t2) (\exists b X, I b X) Q.
Proof using.
  introv WR M. applys triple_hexists. intros b0.
  applys triple_hexists. intros X0.
  gen b0. induction_wf IH: WR X0. intros. applys triple_while.
  applys M. intros b' Y HR'. applys IH HR'.
Qed.

(** The rule [triple_while_inv] admits a constrained precondition of the form
    [(\exists b X, I b X)]. To exploit this rule, one almost always needs
    to first invoke the consequence-frame rule.

    The rule [triple_while_inv_conseq_frame], shown below, conveniently bakes in
    frame and consequence rules into the statement of [triple_while_inv]. *)

Lemma triple_while_inv_conseq_frame :
  forall (A:Type) (I:bool->A->hprop) (R:A->A->Prop) H' t1 t2 H Q,
  let Q' := (fun r => \exists Y, I false Y) in
  wf R ->
  (H ==> (\exists b X, I b X) \* H') ->
  (forall t b X,
      (forall b' Y, R Y X -> triple t (I b' Y) Q') ->
      triple (trm_if t1 (trm_seq t2 t) val_unit) (I b X) Q') ->
  Q' \*+ H' ===> Q ->
  triple (trm_while t1 t2) H Q.
Proof using.
  introv WR WH M WQ. applys triple_conseq_frame WH WQ.
  applys triple_while_inv WR M.
Qed.

(** The above rule can be equivalently reformulated in weakest-precondition
    style. *)

Lemma wp_while_inv_conseq :
  forall (A:Type) (I:bool->A->hprop) (R:A->A->Prop) t1 t2,
  let Q := (fun r => \exists Y, I false Y) in
  wf R ->
     (\exists b X, I b X)
  \* \[forall t b X,
      (forall b' Y, R Y X -> (I b' Y) ==> wp t Q) ->
       (I b X) ==> wp (trm_if t1 (trm_seq t2 t) val_unit) Q]
   ==> wp (trm_while t1 t2) Q.
Proof using.
  introv WR. sets H: (\exists b X, I b X). xpull. intros M.
  rewrite wp_equiv. applys triple_while_inv WR.
  introv N. rewrite <- wp_equiv. applys M.
  introv HR. rewrite wp_equiv. applys N HR.
Qed.

(* ################################################################# *)
(** * More Details *)

(* ================================================================= *)
(** ** Semantics and Basic Evaluation Rules for For-Loops *)

Module ForLoops.

(** In the previous section, we have focused on while loops and presented
    encodings, evaluation rules, and reasoning rules. In this section, we
    present a similar construction for for-loops.

    A for loop takes the form [trm_for x n1 n2 t3], matching the OCaml
    syntax [for x = n1 to n2 do t3 done]. We assume the bounds [n1] and [n2]
    to be already evaluated to integers---i.e., we assume A-normal form. *)

Parameter trm_for : var -> trm -> trm -> trm -> trm.

Notation "'for' x '=' t1 'to' t2 'do' t3 'done'" :=
  (trm_for x t1 t2 t3)
  (in custom trm at level 0,
   x at level 0,
   t1 custom trm at level 99,
   t2 custom trm at level 99,
   t3 custom trm at level 99,
   format "'[v' 'for'  x  '='  t1  'to'  t2  'do'  '/' '['   t3 ']' '/'  'done' ']'")
   : trm_scope.

Close Scope trm_scope.

(** The semantics of [for x = n1 to n2 do t3] is encoded using a conditional.
    If [n1 <= n2], then we execute the body [t3] with [x] bound to [n1] (that
    is, [subst x n1 t3]), and continue with the remainig iterations, which are
    described by [for x = n1+1 to n2 do t3 done]. Eventually, we reach a
    situation where [n1 > n2]. At this point, the loop terminates, and returns
    the unit value. *)

Parameter eval_for : forall s1 s2 x n1 n2 t3 v,
  eval s1 (trm_if (val_le n1 n2) (trm_seq (trm_let x n1 t3)
            (trm_for x (n1+1) n2 t3)) val_unit) s2 v ->
  eval s1 (trm_for x n1 n2 t3) s2 v.

(** The direct reasoning rules for for-loops w.r.t. Hoare triples and
    Separation Logic triples simply unfold the encoding. *)

Lemma hoare_for : forall x n1 n2 t3 H Q,
  hoare (trm_if (val_le n1 n2) (trm_seq (trm_let x n1 t3)
            (trm_for x (n1+1) n2 t3)) val_unit) H Q ->
  hoare (trm_for x n1 n2 t3) H Q.
Proof using.
  introv M K. forwards* (s'&v&R1&K1): M.
  exists s' v. splits*. { applys* eval_for. }
Qed.

Lemma triple_for : forall x n1 n2 t3 H Q,
  triple (trm_if (val_le n1 n2) (trm_seq (trm_let x n1 t3)
            (trm_for x (n1+1) n2 t3)) val_unit) H Q ->
  triple (trm_for x n1 n2 t3) H Q.
Proof using. introv M. intros H'. apply hoare_for. applys* M. Qed.

(** Just like for while loops, we can reduce the noise associated with applying
    the rule [triple_for], by pre-processing the encoding based on the
    conditional. This rule may be useful for carrying out proofs by induction.

    Follow carefully through the proof, as it exhibits reasoning patterns that
    are useful for the follow-up exercises. *)

Lemma triple_for' : forall x n1 n2 t3 H Q,
  (forall (tloop:int->trm) (n:int),
     (forall i H' Q',
        (If i <= n2
           then (exists H1, triple (subst x i t3) H' (fun v => H1)
                         /\ triple (tloop (i+1)) H1 Q')
           else (H' ==> Q' val_unit)) ->
        triple (tloop i) H' Q') ->
    triple (tloop n) H Q) ->
  triple (trm_for x n1 n2 t3) H Q.
Proof using.
  introv M. applys M (fun n => trm_for x n n2 t3). introv K.
  applys triple_for. applys triple_if_trm.
  { applys triple_conseq_frame triple_le. xsimpl. xsimpl. }
  { intros v. applys triple_hpure. intros ->. applys triple_if.
    do 2 case_if; try solve [ false; math ].
    { forwards (H1&K1&K2):K. applys triple_seq H1.
      { applys triple_let_val. applys K1. }
      { applys K2. } }
    { applys triple_val. applys K. } }
Qed.

(** We can derive a simpler rule for the case of loops with no iterations. *)

(** **** Exercise: 4 stars, standard, optional (triple_for_ge)

    Prove the specification of for loops in the case where the lower bound
    of the loop exceeds the upper bound of the loop.
    Hint: the proof shares similarities with that of [triple_for']. *)

Lemma triple_for_ge : forall x n1 n2 t3 H Q,
  n1 > n2 ->
  H ==> Q val_unit ->
  triple (trm_for x n1 n2 t3) H Q.
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** We can derive an reasoning rule expressed using a loop invariant: if [I n1]
    holds before the loop, and each iteration takes the state from [I i] to
    [I (i+1)], then [I (n2+1)] holds after the last iteration. The benefits
    of this presentation, compared with [triple_for'], is that it bakes in the
    application of the induction principle. *)

(** **** Exercise: 5 stars, standard, especially useful (triple_for_inv_conseq_frame)

    Prove the invariant-based reasoning rule for for-loops.
    Hint: the proof shares similarities with that of [triple_for']. *)

Lemma triple_for_inv_conseq_frame : forall (I:int->hprop) H' x n1 n2 t3 H Q,
  n1 <= n2+1 ->
  (H ==> I n1 \* H') ->
  (forall i, n1 <= i <= n2+1 ->
     triple (subst x i t3) (I i) (fun u => I (i+1))) ->
  (fun v => I (n2+1) \* H') ===> Q ->
  triple (trm_for x n1 n2 t3) H Q.
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

End ForLoops.

(* ================================================================= *)
(** ** Treatment of Generalized Conditionals and Loops in [wpgen] *)

Close Scope wp_scope.

(** The formula generator [wpgen] may be extended to take into account
    the generalized form [if t0 then t1 else t2]. The corresponding formula is
    [wpgen_let (aux t0) (fun v => mkstruct (wpgen_if v (aux t1) (aux t2))],
    where [wpgen_let] is used to compute the [wpgen] of the argument of the
    conditional, and where [wpgen_if] is used to compute the [wpgen] of a
    conditional with a argument already evaluated to a value.

    This pattern is captured by the auxiliary definition [wpgen_if_trm].

    Fixpoint wpgen (E:ctx) (t:trm) : hprop :=
      mkstruct match t with
      ...
      | trm_if t0 t1 t2 => wpgen_if_trm (wpgen t0) (wpgen t1) (wpgen t2)
      ...

    where [wpgen_if_trm] is defined as shown below. *)

Definition wpgen_if_trm (F0 F1 F2:formula) : formula :=
  wpgen_let F0 (fun v => mkstruct (wpgen_if v F1 F2)).

(** The soundness of this extension of [wpgen] is captured by the
    following lemma. *)

Lemma wpgen_if_trm_sound : forall F0 F1 F2 t0 t1 t2,
  formula_sound t0 F0 ->
  formula_sound t1 F1 ->
  formula_sound t2 F2 ->
  formula_sound (trm_if t0 t1 t2) (wpgen_if_trm F0 F1 F2).
Proof using.
  introv S0 S1 S2. unfold wpgen_if_trm. intros Q. unfold wpgen_let.
  applys himpl_trans S0. applys himpl_trans; [ | applys wp_if_trm ].
  applys wp_conseq. intros v. applys mkstruct_sound.
  intros Q'. applys wpgen_if_sound S1 S2.
Qed.

(** To handle while loops in [wpgen], we introduce the auxiliary
    definition [wpgen_while].

    Fixpoint wpgen (E:ctx) (t:trm) : hprop :=
      mkstruct match t with
      ...
      | trm_while t1 t2 => wpgen_while (wpgen t1) (wpgen t2)
      ...

  The definition of [wpgen_while] quantifies over an abstract formula [F],
  while denotes the behavior of the while loop. The weakest precondition
  for the loop w.r.t. postcondition [Q] is described as [F Q], or, more
  precisely [mkstruct F Q], to keep track of the fact that [F] denotes a
  formula on which one may apply any structural reasoning rule.

  To establish that [mkstruct F Q] is entailed by the heap predicate that
  describes the current state, the user is provided with an assumption:
  the fact that [mkstruct F Q'] can be proved from the weakest precondition
  of the term [if t1 then (t2; t3) else ()], where the weakest precondition
  of [t3], which denotes the recursive call to the loop, is described by [F]. *)

Definition wpgen_while (F1 F2:formula) : formula := fun Q =>
  \forall F,
     \[forall Q',     mkstruct (wpgen_if_trm F1
                                  (mkstruct (wpgen_seq F2 (mkstruct F)))
                                  (mkstruct (wpgen_val val_unit))) Q'
                  ==> mkstruct F Q']
  \-* (mkstruct F Q).

(** Let us axiomatize the fact that [wpgen] is generalized to handle the new
    term construct [trm_while t1 t2]. *)

Parameter wpgen_while_eq : forall E t1 t2,
  wpgen E (trm_while t1 t2) = mkstruct (wpgen_while (wpgen E t1) (wpgen E t2)).

(** The soundness proof of [wpgen] with respect to the treatment of
    while-loops goes as follows. *)

Lemma wpgen_while_sound : forall t1 t2 F1 F2,
  formula_sound t1 F1 ->
  formula_sound t2 F2 ->
  formula_sound (trm_while t1 t2) (wpgen_while F1 F2).
Proof using.
  introv S1 S2. intros Q. unfolds wpgen_while.
  applys himpl_hforall_l (wp (trm_while t1 t2)).
  applys himpl_trans. 2:{ rewrite* <- mkstruct_wp. }
  rewrite hwand_hpure_l. { auto. } intros Q'.
  applys mkstruct_monotone. intros Q''.
  applys himpl_trans. 2:{ applys wp_while. }
  applys himpl_trans.
  2:{ applys wpgen_if_trm_sound.
    { applys S1. }
    { applys mkstruct_sound. applys wpgen_seq_sound.
      { applys S2. }
      { applys mkstruct_sound. applys wp_sound. } }
    { applys mkstruct_sound. applys wpgen_val_sound. } }
  { auto. }
Qed.

(* ================================================================= *)
(** ** Notation and Tactics for Manipulating While-Loops *)

(** The associated piece of notation for displaying characteristic formulae
    are defined as follows. *)

Notation "'If_trm' F0 'Then' F1 'Else' F2" :=
  ((wpgen_if_trm F0 F1 F2))
  (in custom wp at level 69) : wp_scope.

Declare Scope wpgen_scope.

Notation "'While' F1 'Do' F2 'Done'" :=
  ((wpgen_while F1 F2))
  (in custom wp at level 69, F2 at level 68,
   format "'[v' 'While'  F1  'Do'  '/' '['   F2 ']' '/' 'Done' ']'")
   : wp_scope.

(** The tactic [xapply] is useful for applying an assumption of the form
    [H ==> mkstruct F Q] to a goal of the form [H' ==> mkstruct F Q'],
    with the ramified frame rule relating [H], [H'], [Q] and [Q'].
    In essence, [xapply] applies an hypothesis "modulo consequence-frame". *)

Lemma mkstruct_apply : forall H1 H2 F Q1 Q2,
  H1 ==> mkstruct F Q1 ->
  H2 ==> H1 \* (Q1 \--* protect Q2) ->
  H2 ==> mkstruct F Q2.
Proof using.
  introv M1 M2. xchange M2. xchange M1. applys mkstruct_ramified.
Qed.

Tactic Notation "xapply" constr(E) :=
  applys mkstruct_apply; [ applys E | xsimpl; unfold protect ].

(** The tactic [xwhile] is useful for reasoning about a while-loop.
    In essence, the tactic [while] applies the reasoning rule [wp_while]. *)

Lemma xwhile_lemma : forall F1 F2 H Q,
  (forall F,
    (forall Q', mkstruct (wpgen_if_trm F1 (mkstruct (wpgen_seq F2 (mkstruct F)))
                                          (mkstruct (wpgen_val val_unit))) Q'
                ==> mkstruct F Q')
     -> H ==> mkstruct F Q) ->
  H ==> mkstruct (wpgen_while F1 F2) Q.
Proof using.
  introv M. applys himpl_trans. 2:{ applys mkstruct_erase. }
  unfold wpgen_while. xsimpl. intros F N. applys M. applys N.
Qed.

Tactic Notation "xwhile" :=
  xseq_xlet_if_needed; applys xwhile_lemma.

(** Note: a similar construction could be set up for dealing with for loops. *)

(* ================================================================= *)
(** ** Example of the Application of Frame During Loop Iterations *)

Section DemoLoopFrame.
Import ProgramSyntax Basic Repr.
Global Opaque MList.

(** Consider the following function, which computes the length of a linked
    list with head at location [p], using a while loop and a reference named
    [a] to count the number of cells being traversed.

OCaml:

    let mlength_loop p =
      let a = ref 0 in
      let r = ref p in
      while !r != null do
        incr a;
        r := (!r).tail;
      done;
      let n = !a in
      free a;
      free r;
      n
*)

Definition mlength_loop : val :=
  <{ fun 'p =>
       let 'a = ref 0 in
       let 'r = ref 'p in
       while let 'p1 = !'r in ('p1 <> null) do
         incr 'a;
         let 'p1 = !'r in
         let 'q = 'p1`.tail in
         'r := 'q
       done;
       let 'n = !'a in
       free 'a;
       free 'r;
       'n }>.

(** This function is specified and verified as follows. *)

Lemma triple_mlength_loop : forall L p,
  triple (mlength_loop p)
    (MList L p)
    (fun r => \[r = length L] \* MList L p).
Proof using.
(** Let's compute the weakest precondition and pretend that
    [xwpgen] includes support for loops. *)
  xwp. xapp. intros a. xapp. intros r.
  rewrite wpgen_while_eq. xwp_simpl.
(** We call the [xwhile] tactic to handle the loop.
    The formula [F] then denotes "the behavior of the loop". *)
  xwhile. intros F HF.
(** We next state the induction principle for the loop, in the
    form [I p n ==> F Q], where [I p n] denotes the loop invariant,
    and [Q] describes the final output of the loop. *)
  asserts KF: (forall p n,
         r ~~> p \* a ~~> n \* MList L p
     ==> mkstruct F (fun _ => r ~~> null \* a ~~> (length L + n) \* MList L p)).
(** We carry out a proof by induction on the length of the list [L]. *)
  { induction_wf IH: list_sub L. intros.
    applys himpl_trans HF. clear HF. xlet.
    xapp. xapp. xchange MList_if. xif; intros C; case_if.
    { xpull. intros x q L' ->. xseq. xapp. xapp. xapp. xapp.
(** At this point, we reason about the recursive call.
    We use the tactic [xapply] to apply the induction
    hypothesis modulo the frame rule. Here, the head cell
    of the list is framed out over the scope of the recursive
    call, which operates only on the tail of the list. *)
      xapply (IH L'). { auto. } intros _.
      xchange <- MList_cons. { xsimpl. rew_list. math. }  }
    { xpull. intros ->. xval. xsimpl. { congruence. }
      subst. xchange* <- (MList_nil null). } }
  xapply KF. xpull. xapp. xapp. xapp. xval. xsimpl. math.
Qed.

End DemoLoopFrame.

(* ================================================================= *)
(** ** Reasoning Rule for Loops in an Affine Logic *)

Module LoopRuleAffine.

(** Recall from [Affine] the combined structural rule that includes
    the affine top predicate [\GC]. *)

Parameter triple_conseq_frame_hgc : forall H2 H1 Q1 t H Q,
  triple t H1 Q1 ->
  H ==> H1 \* H2 ->
  Q1 \*+ H2 ===> Q \*+ \GC ->
  triple t H Q.

(** In that setting, it is useful to integrate [\GC] into the rule
    [triple_while_inv_conseq_frame], to allow discarding the data
    allocated by the loop iterations but not described in the final
    postcondition. *)

Lemma triple_while_inv_conseq_frame_hgc :
  forall (A:Type) (I:bool->A->hprop) (R:A->A->Prop) H' t1 t2 H Q,
  let Q' := (fun r => \exists Y, I false Y) in
  wf R ->
  (H ==> (\exists b X, I b X) \* H') ->
  (forall t b X,
      (forall b' Y, R Y X -> triple t (I b' Y) Q') ->
      triple (trm_if t1 (trm_seq t2 t) val_unit) (I b X) Q') ->
  Q' \*+ H' ===> Q \*+ \GC ->
  triple (trm_while t1 t2) H Q.
Proof using.
  introv WR WH M WQ. applys triple_conseq_frame_hgc WH WQ.
  applys triple_while_inv WR M.
Qed.

End LoopRuleAffine.

End WhileLoops.

(* ================================================================= *)
(** ** Curried Functions of Several Arguments *)

Module CurriedFun.
Open Scope liblist_scope.
Implicit Types f : var.

(** We next give a quick presentation of the notation, lemmas and
    tactics involved in the manipulation of curried functions of
    several arguments.

    We focus here on the particular case of recursive functions with 2
    arguments, to illustrate the principles at play. Set up for non-recursive
    and recursive functions of arity 2 and 3 can be found in the file
    [LibSepReference].

    One may attempt to generalize these definitions to handle arbitrary
    arities. Yet, to obtain an arity-generic treatment of functions, it
    appears simpler to work with primitive n-ary functions, whose treatment
    is presented in the next section.

    Consider a curried recursive functions that expects two arguments:
    [val_fix f x1 (trm_fun x2 t)] describes such a function, where [f]
    denotes the name of the function for recursive calls, [x1] and [x2]
    denote the arguments, and [t] denotes the body. Observe that the
    inner function, the one that expects [x2], is not recursive, and that
    it is not a value but a term (because it may refer to the variable [x1]
    bound outside of it).

    We introduce the notation [Fix f x1 x2 := t] for such a recursive
    function with two arguments. *)

Notation "'Fix' f x1 x2 ':=' t" :=
  (val_fix f x1 (trm_fun x2 t))
  (at level 69, f, x1, x2 at level 0,
  format "'Fix'  f  x1  x2  ':='  t").

(** An application of a function with two arguments takes the form
    [f v1 v2], which is actually parsed as [trm_app (trm_app f v1) v2].

    This expression is an application of a term to a value, and not of
    a value to a value. Thus, this expression cannot be evaluated using
    the rule [eval_app_fun]. We therefore need a distinct rule for first
    evaluating the arguments of a function application to values, before
    we can evaluate the application of a value to a value.

    The rule [eval_app_args] serves that purpose. To state it, we first
    need to characterize whether a term is a value or not, using the
    predicate [trm_is_val t] defined next. *)

Definition trm_is_val (t:trm) : Prop :=
  match t with trm_val v => True | _ => False end.

(** The statement of [eval_app_args] is as shown below. For an expression
    of the form [trm_app t1 t2], where either [t1] or [t2] is
    not a value, it enables reducing both [t1] and [t2] to values,
    leaving a premise describing the evaluation of a term of the form
    [trm_app v1 v2], for which the rule [eval_app_fun] applies. *)

Parameter eval_app_args : forall s1 s2 s3 s4 t1 t2 v1 v2 r,
  (~ trm_is_val t1 \/ ~ trm_is_val t2) ->
  eval s1 t1 s2 v1 ->
  eval s2 t2 s3 v2 ->
  eval s3 (trm_app v1 v2) s4 r ->
  eval s1 (trm_app t1 t2) s4 r.

(** Using the above rule, we can establish an evaluation rule for the
    term [v0 v1 v2]. There, [v0] denotes a recursive function of two
    arguments named [x1] and [x2], the values [v1] and [v2] denote
    the two arguments, and [f] denotes the name of the function available
    for making recursive calls from the body [t1].

    The key idea is that the behavior of [v0 v1 v2] is similar to
    that of the term [subst x2 v2 (subst x1 v1 (subst f v0 t1))].
    We state this property using the predicate [eval_like], introduced
    in the chapter [Rules]. *)

Lemma eval_like_app_fix2 : forall v0 v1 v2 f x1 x2 t1,
  v0 = val_fix f x1 (trm_fun x2 t1) ->
  (x1 <> x2 /\ f <> x2) ->
  eval_like (subst x2 v2 (subst x1 v1 (subst f v0 t1))) (v0 v1 v2).
Proof using.
  introv E (N1&N2). introv R. applys* eval_app_args.
  { applys eval_app_fix E. simpl. do 2 (rewrite var_eq_spec; case_if).
    applys eval_fun. }
  { applys* eval_val. }
  { applys* eval_app_fun. }
Qed.

(** We next derive the specification triple for applications of
    the form [v0 v1 v2]. *)

Lemma triple_app_fix2 : forall f x1 x2 v0 v1 v2 t1 H Q,
  v0 = val_fix f x1 (trm_fun x2 t1) ->
  (x1 <> x2 /\ f <> x2) ->
  triple (subst x2 v2 (subst x1 v1 (subst f v0 t1))) H Q ->
  triple (v0 v1 v2) H Q.
Proof using.
  introv E N M1. applys triple_eval_like M1. applys* eval_like_app_fix2.
Qed.

(** The reasoning rule above can be reformulated in weakest-precondition
    style. *)

Lemma wp_app_fix2 : forall f x1 x2 v0 v1 v2 t1 Q,
  v0 = val_fix f x1 (trm_fun x2 t1) ->
  (x1 <> x2 /\ f <> x2) ->
  wp (subst x2 v2 (subst x1 v1 (subst f v0 t1))) Q ==> wp (trm_app v0 v1 v2) Q.
Proof using. introv EQ1 N. applys wp_eval_like. applys* eval_like_app_fix2. Qed.

(** Finally, it is useful to extend the tactic [xwp], so that it exploits
    the rule [wp_app_fix2] in the same way as it exploits [wp_app_fix].

    To that end, we state a lemma featuring a conclusion expressed
    as a [triple], and a premise expressed using [wpgen]. Observe the
    substitution context associated with [wpgen]: it is instantiated as
    [(f,v0)::(x1,v1)::(x2,v2)::nil], so as to perform the relevant
    substitutions. Note also how the side-condition expressing the freshness
    conditions on the variables, using a comparison function for variables
    that computes in Coq. *)

Lemma xwp_lemma_fix2 : forall f v0 v1 v2 x1 x2 t H Q,
  v0 = val_fix f x1 (trm_fun x2 t) ->
  (var_eq x1 x2 = false /\ var_eq f x2 = false) ->
  H ==> wpgen ((f,v0)::(x1,v1)::(x2,v2)::nil) t Q ->
  triple (v0 v1 v2) H Q.
Proof using.
  introv M1 N M2. repeat rewrite var_eq_spec in N. rew_bool_eq in *.
  rewrite <- wp_equiv. xchange M2.
  xchange (>> wpgen_sound
    (((f,v0)::nil) ++ ((x1,v1)::nil) ++ ((x2,v2)::nil)) t Q).
  do 2 rewrite isubst_app. do 3 rewrite <- subst_eq_isubst_one.
  applys* wp_app_fix2.
Qed.

(** The lemma gets integrated into the implementation of [xwp] as follows. *)

Tactic Notation "xwp" :=
  intros;
  first [ applys xwp_lemma_fun; [ reflexivity | ]
        | applys xwp_lemma_fix; [ reflexivity | ]
        | applys xwp_lemma_fix2; [ reflexivity | splits; reflexivity | ] ];
  xwp_simpl.

(** This tactic [xwp] also appears in the file [LibSepReference.v]. It is
    exploited in several examples from the chapter [Basic]. *)

End CurriedFun.

(* ================================================================= *)
(** ** Primitive n-ary Functions *)

Module PrimitiveNaryFun.

(** We next present an alternative treatment to functions of several
    arguments. The idea is to represent function arguments using lists.
    The verification tool CFML is implemented following this approach.

    On the one hand, the manipulation of lists adds a little bit of
    boilerplate. On the other hand, when using this representation, all
    the definitions and lemmas are inherently arity-generic, that is,
    they work for any number of arguments.

    We introduce the short names [vars], [vals] and [trms] to denote lists
    of variables, lists of values, and lists of terms, respectively.

    These names are not only useful to improve conciseness, they also enable
    the set up of useful coercions, as illustrated further on. *)

Definition vars : Type := list var.
Definition vals : Type := list val.
Definition trms : Type := list trm.

Implicit Types xs : vars.
Implicit Types vs : vals.
Implicit Types ts : trms.

(** We assume the grammar of terms and values to include primitive n-ary
    functions and primitive n-ary applications, featuring list of arguments.

    Thereafter, for conciseness, we focus on the treatment of recursive
    functions, and do not describe the simpler case of non-recursive
    functions. *)

Parameter val_fixs : var -> vars -> trm -> val.
Parameter trm_fixs : var -> vars -> trm -> trm.
Parameter trm_apps : trm -> trms -> trm.

(** The substitution function is a bit tricky to update for dealing with
    list of variables. A definition along the following lines computes well,
    and is recognized as structurally recursive by Coq.

    Fixpoint subst (y:var) (w:val) (t:trm) : trm :=
      let aux t := (subst y w t) in
      let aux_no_captures xs t := (If List.In y xs then t else aux t) in
      match t with
      | trm_fixs f xs t1 => trm_fixs f xs (If f = y then t1 else
                                            aux_no_captures xs t1)
      | trm_apps t0 ts => trm_apps (aux t0) (List.map aux ts)
      ...
     end.
*)

(** The evaluation rules also need to be updated to handle list of
    arguments. A n-ary function from the grammar of terms evaluates to
    the corresponding n-ary function from the grammar of values. *)

Parameter eval_fixs : forall m f xs t1,
  xs <> nil ->
  eval m (trm_fixs f xs t1) m (val_fixs f xs t1).

(** Note that, for technical reasons, we need to ensure that list of
    arguments is nonempty. Indeed, a function with zero arguments
    would beta-reduce to its body as soon as it is defined, because
    it is not waiting for any argument, resulting in an infinite
    sequence of reductions. *)

(** The application of a n-ary function to values takes the form
    [trm_apps (trm_val v0) ((trm_val v1):: .. ::(trm_val vn)::nil)].

    If the function [v0] is defined as [val_fixs f xs t1], where [xs]
    denotes the list [x1::x2::...::xn::nil], then the beta-reduction
    of the function application triggers the evaluation of the
    term [subst xn vn (... (subst x1 v1 (subst f v0 t1)) ...)].

    To describe the evaluation rule in an arity-generic way, we need to
    introduce the list [vs] made of the values provided as arguments,
    that is, the list [v1::v2::..::vn::nil].

    With this list [vs], the n-ary application can then be written as the
    term [trm_apps (trm_val v0) (trms_vals vs)], where the operation
    [trms_vals] converts a list of values into a list of terms by
    applying the constructor [trm_val] to every value from the list. *)

Coercion trms_vals (vs:vals) : trms :=
  LibList.map trm_val vs.

(** Note that we declare the operation [trms_vals] as a coercion, just
    like [trm_val] is a coercion. Doing so enables us to write a n-ary
    application in the form [v0 vs]. *)

(** To describe the iterated substitution
    [subst xn vn (... (subst x1 v1 (subst f v0 t1)) ...)], we introduce
    the operation [substn xs vs t], which substitutes the variables [xs]
    with the values [vs] inside the [t]. It is defined recursively,
    by iterating calls to the function [subst] for substituting the
    variables one by one. *)

Fixpoint substn (xs:list var) (vs:list val) (t:trm) : trm :=
  match xs,vs with
  | x::xs', v::vs' => substn xs' vs' (subst x v t)
  | _,_ => t
  end.

(** This substitution operation is well-behaved only if the list [xs]
    and the list [vs] have the same lengths. It is also needed for
    reasoning about the evaluation rule to guarantee that the list of
    variables [xs] contains variables that are distinct from each others
    and distinct from [f], and to guarantee that the list [xs] is not empty.

    To formally capture all these invariants, we introduce the predicate
    [var_fixs f xs n], where [n] denotes the number of arguments the
    function is being applied to. Typically, [n] is equal to the length
    of the list of arguments [vs]. *)

Definition var_fixs (f:var) (xs:vars) (n:nat) : Prop :=
     LibList.noduplicates (f::xs)
  /\ length xs = n
  /\ xs <> nil.

(** The evaluation of a recursive function [v0] defined as [val_fixs f xs t1]
    on a list of arguments [vs] triggers the evaluation of the term
    [substn xs vs (subst f v0 t1)], same as [substn (f::xs) (v0::vs) t1].
    The evaluation rule is stated as follows, using the predicate [var_fixs]
    to enforce the appropriate invariants on the variable names. *)

Parameter eval_apps_fixs : forall v0 vs f xs t1 s1 s2 r,
  v0 = val_fixs f xs t1 ->
  var_fixs f xs (LibList.length vs) ->
  eval s1 (substn (f::xs) (v0::vs) t1) s2 r ->
  eval s1 (trm_apps v0 (trms_vals vs)) s2 r.

(** The corresponding reasoning rule admits a somewhat similar statement. *)

Lemma triple_apps_fixs : forall v0 vs f xs t1 H Q,
  v0 = val_fixs f xs t1 ->
  var_fixs f xs (LibList.length vs)->
  triple (substn (f::xs) (v0::vs) t1) H Q ->
  triple (trm_apps v0 vs) H Q.
Proof using.
  introv E N M. applys triple_eval_like M.
  introv R. applys* eval_apps_fixs.
Qed.

(** The statement of the above lemma applies only to terms that are
    of the form [trm_apps (trm_val v0) (trms_vals vs)]. Yet, in practice,
    goals are generally of the form
    [trm_apps (trm_val v0) ((trm_val v1):: .. :: (trm_val vn)::nil)].

    The two forms are convertible. Yet, in most cases, Coq is not able to
    synthesize the list [vs] during the unification process.

    Fortunately, it is possible to reformulate the lemma using an auxiliary
    conversion function named [trms_to_vals], whose evaluation by Coq's
    unification process is able to synthesize the list [vs].

    The operation [trms_to_vals ts], if all the terms in [ts] are of the
    form [trm_val vi], returns a list of values [vs] such that [ts] is
    equal to [trms_vals vs]. Otherwise, the operation returns [None].
    The definition and specification of the operation [trms_to_vals]
    are as follows. *)

Fixpoint trms_to_vals (ts:trms) : option vals :=
  match ts with
  | nil => Some nil
  | (trm_val v)::ts' =>
      match trms_to_vals ts' with
      | None => None
      | Some vs' => Some (v::vs')
      end
  | _ => None
  end.

(** The specification of the function [trms_to_vals] asserts that if
    [trms_to_vals ts] produces some list of values [vs], then [ts] is
    equal to [trms_vals vs]. *)

Lemma trms_to_vals_spec : forall ts vs,
  trms_to_vals ts = Some vs ->
  ts = trms_vals vs.
Proof using.
  intros ts. induction ts as [|t ts']; simpl; introv E.
  { inverts E. auto. }
  { destruct t; inverts E as E. cases (trms_to_vals ts') as C; inverts E.
    rename v0 into vs'. rewrite* (IHts' vs'). }
Qed.

(** Here is a demo showing how [trms_to_vals] computes in practice. *)

Lemma demo_trms_to_vals : forall v1 v2 v3,
  exists vs,
     trms_to_vals ((trm_val v1)::(trm_val v2)::(trm_val v3)::nil) = Some vs
  /\ vs = vs.
Proof using.
  (* Activate the display of coercions to play this demo *)
  intros. esplit. split. simpl. eauto. (* Observe how [vs] is inferred. *)
Abort.

(** Using [trms_to_vals], we can reformulate the rule [triple_apps_fixs]
    in such a way that the rule can be smoothly applied on goals of the
    form [trm_apps (trm_val v0) ((trm_val v1):: .. :: (trm_val vn)::nil)]. *)

Lemma triple_apps_fixs' : forall v0 ts vs f xs t1 H Q,
  v0 = val_fixs f xs t1 ->
  trms_to_vals ts = Some vs ->
  var_fixs f xs (LibList.length vs)->
  triple (substn (f::xs) (v0::vs) t1) H Q ->
  triple (trm_apps v0 ts) H Q.
Proof using.
  introv E T N M. rewrites (@trms_to_vals_spec _ _ T).
  applys* triple_apps_fixs.
Qed.

(** Finally, let us show how to integrate the rule [triple_apps_fixs'] into
    the tactic [xwp]. To that end, we reformulate the rule by making two
    small changes.

    The first change consists of replacing the predicate [var_fixs] which checks
    the well-formedness properties of the list of variables [xs] by an
    executable version of this predicate, with a result in [bool]. This way,
    the tactic [reflexivity] can prove all the desired facts, when the lemma
    in invoked on a concrete function. We omit the details, and simply
    state the type of the boolean function [var_fixs_exec]. *)

Parameter var_fixs_exec : var -> vars -> nat -> bool.

(** The second change consists of introducing the [wpgen] function for
    reasoning about the body of the function. Concretely, the substitution
    [substn (f::xs) (v0::vs)] is described by the substitution context
    [List.combine (f::xs) (v0::vs)].

    The statement of the lemma for [xwp] is as follows. We omit the proof
    details. (They may be found in the implementation of the CFML tool.) *)

Parameter xwp_lemma_fixs : forall v0 ts vs f xs t1 H Q,
  v0 = val_fixs f xs t1 ->
  trms_to_vals ts = Some vs ->
  var_fixs_exec f xs (LibList.length vs) ->
  H ==> (wpgen (combine (f::xs) (v0::vs)) t1) Q ->
  triple (trm_apps v0 ts) H Q.

(* ################################################################# *)
(** * Optional Material *)

(* ================================================================= *)
(** ** A Coercion for Parsing Primitive N-ary Applications *)

(** One last practical detail for working with primitive n-ary functions
    in a smooth way consists of improving the parsing of applications.

    Writing an application in the form [trm_apps f (x::y::nil)] to denote
    the application of a function [f] to two arguments [x] and [y] is
    fairly verbose, in comparison with the syntax [f x y], which we were able
    to set up by declaring [trm_app] as a [Funclass] coercion---recall chapter
    [Rules].

    If we simply declare [trm_apps] as a [Funclass] coercion, then we can
    write [f (x::y::nil)] in place of [trm_apps f (x::y::nil)], however we
    still need to write the arguments in the form [x::y::nil].

    Fortunately, there is a trick that allows the expression [f x y] to be
    interpreted by Coq as [trm_apps f (x::y::nil)]. This trick is arity-generic:
    it works for any number of arguments. It is described next. *)

Module NarySyntax.

(** To explain the working of our coercion trick, let us consider a simplified
    grammar of terms, including only the constructor [trm_apps] for n-ary
    applications, and the construct [trm_val] for values. *)

Inductive trm : Type :=
  | trm_val : val -> trm
  | trm_apps : trm -> list trm -> trm.

(** We introduce the data type [apps], featuring two constructors named
    [apps_init] and [apps_next], to represent the syntax tree. *)

Inductive apps : Type :=
  | apps_init : trm -> trm -> apps
  | apps_next : apps -> trm -> apps.

(** For example, the term [trm_apps f (x::y::z::nil)] is represented
    as the expression [apps_next (apps_next (apps_init f x) y) z].

    Internally, the parsing proceeds as follows.

    - The application of a term to a term, that is, [t1 t2], gets interpreted
      via a [Funclass] coercion as [apps_init t1 t2], which is an expression
      of type [apps].
    - The application of an object of type [apps] to a term, that is [a1 t2],
      gets interpreted via another [Funclass] coercion as [apps_next a1 t2].

*)

Coercion apps_init : trm >-> Funclass.
Coercion apps_next : apps >-> Funclass.

(** From a term of the form [apps_next (apps_next (apps_init f x) y) z],
    the corresponding application [trm_apps f (x::y::z::nil)] can be computed
    by a Coq function, called [apps_to_trm], that processes the syntax tree
    of the [apps] expression. This function is implemented recursively.

    - In the base case, [apps_init t1 t2] describes the application
      of a function to one argument: [trm_apps t1 (t2::nil)].
    - In the "next" case, if an apps structure [a1] describes a term
      [trm_apps t0 ts], then [apps_next a1 t2] describes the term
      [trm_apps t0 (ts++t2::nil)], that is, an application to one more
      argument. *)

Fixpoint apps_to_trm (a:apps) : trm :=
  match a with
  | apps_init t1 t2 => trm_apps t1 (t2::nil)
  | apps_next a1 t2 =>
      match apps_to_trm a1 with
      | trm_apps t0 ts => trm_apps t0 (List.app ts (t2::nil))
      | t0 => trm_apps t0 (t2::nil)
      end
  end.

(** The function [apps_to_trm] is declared as a coercion from [apps]
    to [trm], so that any iterated application can be interpreted as
    the corresponding [trm_apps] term. Coq raises an "ambiguous coercion
    path" warning, but this warning may be safely ignored here. *)

Coercion apps_to_trm : apps >-> trm.

(** The following demo shows how the term [f x y z] is parsed as
    [apps_to_trm (apps_next (apps_next (apps_init f x) y) z)], which
    then simplifies by [simpl] to [trm_apps f (x::y::z::nil)]. *)

Lemma apps_demo : forall (f x y z:trm),
  (f x y z : trm) = trm_apps f (x::y::z::nil).
Proof using. intros. (* activate display of coercions *) simpl. Abort.

End NarySyntax.

End PrimitiveNaryFun.

(* ================================================================= *)
(** ** Historical Notes *)

(** Regarding while loops, the possibility to frame over the remaining
    iterations, as illustrated with the example of [triple_mlength_loop],
    is inherently available when a loop is encoded as a recursive functions,
    or when a loop is presented in CPS-style (typical with assembly-level
    code). The statement of a reasoning rule directly applicable to a
    non-encoded loop construct, and allowing to frame over the remaining
    iterations, has appeared independently in work by [Charguéraud 2010] (in Bib.v)
    and [Tuerk 2010] (in Bib.v). *)

(* 2022-07-09 20:37 *)
