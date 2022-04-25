(** * Partial: Triples for Partial Correctness *)

Set Implicit Arguments.
From SLF Require Export Nondet.
Close Scope val_scope.
Close Scope trm_scope.

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

(** In this chapter, we investigate definitions of Hoare triples and Separation
    Logic triples with respect to partial correctness, that is, without imposing
    termination.

    Partial correctness is a weaker property than total correctness. However,
    it may be suited for reasoning about programs that are not meant to
    terminate, and may be interesting to consider as an intermediate target
    when reasoning about programs for which termination is much harder to
    establish than correctness.

    This chapter is organized as follows:

    - Partial correctness with respect to big-step semantics.
    - Bonus contents: partial correctness with respect to small-step semantics.

    This chapter, like the previous chapter [Nondet], omits sequences and
    non-recursive functions, as these features can be encoded. *)

(* ================================================================= *)
(** ** Big-Step Characterization of Partial Correctness *)

(** For total correctness, the judgment [evals s t Q] asserts that any
    execution of the program [(s,t)] terminates on an output satisfying [Q].
    In contrast, the partial correctness judgment [evalnp s t Q] asserts that
    any execution of the program [(s,t)] either terminates on an output
    satisfying [Q], or diverges (that is, executes forever).

    The definition of the predicate [evalnp] is obtained by taking the
    constructors from the inductive definition of [evaln], and considering
    the coinductive interpretation of these constructors. The coinductive
    interpretation allows for infinite derivation. It thereby introduces the
    possibility of diverging executions. Importantly, the predicate [evalnp]
    still disallows executions that get stuck. *)

CoInductive evalnp : state -> trm -> (val->state->Prop) -> Prop :=
  | evalnp_val : forall s v Q,
      Q v s ->
      evalnp s (trm_val v) Q
  | evalnp_fix : forall s f x t1 Q,
      Q (val_fix f x t1) s ->
      evalnp s (trm_fix f x t1) Q
  | evalnp_app_fix : forall s1 v1 v2 f x t1 Q,
      v1 = val_fix f x t1 ->
      evalnp s1 (subst x v2 (subst f v1 t1)) Q ->
      evalnp s1 (trm_app v1 v2) Q
  | evalnp_let : forall Q1 s1 x t1 t2 Q,
      evalnp s1 t1 Q1 ->
      (forall v1 s2, Q1 v1 s2 -> evalnp s2 (subst x v1 t2) Q) ->
      evalnp s1 (trm_let x t1 t2) Q
  | evalnp_if : forall s1 b t1 t2 Q,
      evalnp s1 (if b then t1 else t2) Q ->
      evalnp s1 (trm_if (val_bool b) t1 t2) Q
  | evalnp_add : forall s n1 n2 Q,
      Q (val_int (n1 + n2)) s ->
      evalnp s (val_add (val_int n1) (val_int n2)) Q
  | evalnp_rand : forall s n Q,
      n > 0 ->
      (forall n1, 0 <= n1 < n -> Q n1 s) ->
      evalnp s (val_rand (val_int n)) Q
  | evalnp_ref : forall s v Q,
      (forall p, ~ Fmap.indom s p ->
         Q (val_loc p) (Fmap.update s p v)) ->
      evalnp s (val_ref v) Q
  | evalnp_get : forall s p Q,
      Fmap.indom s p ->
      Q (Fmap.read s p) s ->
      evalnp s (val_get (val_loc p)) Q
  | evalnp_set : forall s p v Q,
      Fmap.indom s p ->
      Q val_unit (Fmap.update s p v) ->
      evalnp s (val_set (val_loc p) v) Q
  | evalnp_free : forall s p Q,
      Fmap.indom s p ->
      Q val_unit (Fmap.remove s p) ->
      evalnp s (val_free (val_loc p)) Q.

(** The judgment [hoarenp t H Q] captures partial correctness, in terms of
    [evalnp]. It is defined through the usual pattern for Hoare triples. *)

Definition hoarenp (t:trm) (H:hprop) (Q:val->hprop) : Prop :=
  forall s, H s -> evalnp s t Q.

(** One key property is the covariance of [evalnp], which induces the rule
    of consequence for [hoarenp]. An interesting about the proof of covariance
    is that it is not carried out by induction, like [evaln_conseq], but by
    coinduction. Observe carefully the details of that proof. *)

Lemma evalnp_conseq : forall s t Q1 Q2,
  evalnp s t Q1 ->
  Q1 ===> Q2 ->
  evalnp s t Q2.
Proof using.
  introv M W. unfolds qimpl, himpl.
  gen s t Q1 Q2. cofix IH. intros. inverts M; try solve [ constructors* ].
Qed.

(** **** Exercise: 3 stars, standard, optional (evalnp_inv_eval)

    Assume [evalnp s t Q] to hold. Prove that the postcondition [Q] holds of
    any output that [(s,t)] may evaluate to according to the judgment [eval]. *)

Lemma evalnp_inv_eval : forall s t v s' Q,
  evalnp s t Q ->
  eval s t s' v ->
  Q v s'.
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(* ================================================================= *)
(** ** From Total to Partial Correctness *)

(** Total correctness is a stronger property than partial correctness:
    [hoaren t H Q] entails [hoarenp t H Q]. To formalize this result, we first
    establish that [evaln s t Q], which is defined inductively, entails
    [evalnp s t Q], which is defined coinductively.

    The proof is a straightforward induction, reflecting on the fact that a
    coinductive interpretation of a set of rules is always derivable from an
    inductive interpretation of a same set of derivation rules. *)

Lemma evalnp_of_evaln : forall s t Q,
  evaln s t Q ->
  evalnp s t Q.
Proof using. introv M. induction M; try solve [ constructors* ]. Qed.

Lemma hoaren_of_cohoare : forall t H Q,
  hoaren t H Q ->
  hoarenp t H Q.
Proof using.
  introv M. intros s K. specializes M K. applys evalnp_of_evaln M.
Qed.

(* ================================================================= *)
(** ** Characterization of Divergence *)

(** The judgment partial correctness judgment [evalnp s t Q] asserts that
    any execution of the program [(s,t)] either terminates on an output
    satisfying [Q], or diverge. By instantiating [Q] as the predicate that is
    always false, we are thus able to assert that "every possible execution of
    the program [(s,t)] diverges".

    Let us name [Empty] this "empty" postcondition, which characterizes an
    empty set of output configurations. *)

Definition Empty : val->state->Prop :=
  fun v s => False.

(** The judgment [divn s t], defined as [evalnp s t Empty], asserts that every
    possible execution of the program [(s,t)] diverges. *)

Definition divn (s:state) (t:trm) : Prop :=
  evalnp s t Empty.

(* ================================================================= *)
(** ** Big-Step-Based Reasoning Rules *)

(** For the partial correctness triple ([hoarenp]), we can derive all the usual
    reasoning rules. The proofs are the same as for the reasoning rules for
    deriving total correctness triples ([hoaren]). *)

(** Structural rules *)

Lemma hoarenp_conseq : forall t H' Q' H Q,
  hoarenp t H' Q' ->
  H ==> H' ->
  Q' ===> Q ->
  hoarenp t H Q.
Proof using.
  unfolds hoarenp. introv M MH MQ HF. applys* evalnp_conseq.
Qed.

Lemma hoarenp_hexists : forall t (A:Type) (J:A->hprop) Q,
  (forall x, hoarenp t (J x) Q) ->
  hoarenp t (hexists J) Q.
Proof using. introv M. intros h (x&Hh). applys M Hh. Qed.

Lemma hoarenp_hpure : forall t (P:Prop) H Q,
  (P -> hoarenp t H Q) ->
  hoarenp t (\[P] \* H) Q.
Proof using.
  introv M. intros h (h1&h2&M1&M2&D&U). destruct M1 as (M1&HP).
  lets E: hempty_inv HP. subst. rewrite Fmap.union_empty_l. applys~ M.
Qed.

(** Rules for term constructs *)

Lemma hoarenp_val : forall v H Q,
  H ==> Q v ->
  hoarenp (trm_val v) H Q.
Proof using. introv M. intros h K. applys* evalnp_val. Qed.

Lemma hoarenp_fix : forall f x t1 H Q,
  H ==> Q (val_fix f x t1) ->
  hoarenp (trm_fix f x t1) H Q.
Proof using. introv M. intros h K. applys* evalnp_fix. Qed.

Lemma hoarenp_app_fix : forall v1 v2 f x t1 H Q,
  v1 = val_fix f x t1 ->
  hoarenp (subst x v2 (subst f v1 t1)) H Q ->
  hoarenp (trm_app v1 v2) H Q.
Proof using. introv E M. intros h K. applys* evalnp_app_fix. Qed.

Lemma hoarenp_let : forall x t1 t2 H Q Q1,
  hoarenp t1 H Q1 ->
  (forall v1, hoarenp (subst x v1 t2) (Q1 v1) Q) ->
  hoarenp (trm_let x t1 t2) H Q.
Proof using. introv M1 M2. intros h K. applys* evalnp_let. Qed.

Lemma hoarenp_if : forall (b:bool) t1 t2 H Q,
  hoarenp (if b then t1 else t2) H Q ->
  hoarenp (trm_if b t1 t2) H Q.
Proof using. introv M. intros h K. applys* evalnp_if. Qed.

(** Rules for primitive operations *)

Lemma hoarenp_add : forall H n1 n2,
  hoarenp (val_add n1 n2)
    H
    (fun r => \[r = val_int (n1 + n2)] \* H).
Proof using.
  intros. intros h K. applys* evalnp_add. rewrite* hstar_hpure_l.
Qed.

Lemma hoarenp_rand : forall n,
  n > 0 ->
  hoarenp (val_rand n)
    \[]
    (fun r => \exists n1, \[0 <= n1 < n] \* \[r = val_int n1]).
Proof using.
  introv N. intros h K. applys* evalnp_rand.
  lets ->: hempty_inv K.
  intros n1 H1. applys* hexists_intro n1. rewrite* hstar_hpure_l.
  split*. applys* hpure_intro.
Qed.

Lemma hoarenp_ref : forall H v,
  hoarenp (val_ref v)
    H
    (fun r => (\exists p, \[r = val_loc p] \* p ~~> v) \* H).
Proof using.
  intros. intros s1 K. applys evalnp_ref. intros p D.
  unfolds update. applys hstar_intro K.
  { applys hexists_intro p. rewrite hstar_hpure_l.
    split*. applys hsingle_intro. }
  { applys* disjoint_single_of_not_indom. }
Qed.

Lemma hoarenp_get : forall H v p,
  hoarenp (val_get p)
    ((p ~~> v) \* H)
    (fun r => \[r = v] \* (p ~~> v) \* H).
Proof using.
  intros. intros s K.
  lets (h1&h2&P1&P2&D&->): hstar_inv (rm K).
  lets E1: hsingle_inv P1. lets I1: indom_single p v.
  applys evalnp_get.
  { applys* Fmap.indom_union_l. subst. applys indom_single. }
  { rewrite hstar_hpure_l. split.
    { subst h1. rewrite* Fmap.read_union_l. rewrite* Fmap.read_single. }
    { applys* hstar_intro. } }
Qed.

Lemma hoarenp_set : forall H w p v,
  hoarenp (val_set (val_loc p) v)
    ((p ~~> w) \* H)
    (fun r => \[r = val_unit] \* (p ~~> v) \* H).
Proof using.
  intros. intros s1 K.
  lets (h1&h2&P1&P2&D&->): hstar_inv (rm K).
  lets E1: hsingle_inv P1. lets I1: indom_single p v.
  applys evalnp_set.
  { applys* Fmap.indom_union_l. subst. applys indom_single. }
  { rewrite hstar_hpure_l. split*.
    { subst h1. rewrite Fmap.update_union_l.
      2:{ applys indom_single. }
      rewrite update_single. applys hstar_intro.
      { applys hsingle_intro. }
      { applys P2. }
      { applys Fmap.disjoint_single_set D. } } }
Qed.

Lemma hoarenp_free : forall H p v,
  hoarenp (val_free (val_loc p))
    ((p ~~> v) \* H)
    (fun r => \[r = val_unit] \* H).
Proof using.
  intros. intros s1 K.
  lets (h1&h2&P1&P2&D&->): hstar_inv (rm K).
  lets E1: hsingle_inv P1. lets I1: indom_single p v.
  applys evalnp_free.
  { applys* Fmap.indom_union_l. subst. applys indom_single. }
  { rewrite hstar_hpure_l. split*.
    { subst h1. rewrite* Fmap.remove_union_single_l.
      { intros Dl. applys* Fmap.disjoint_inv_not_indom_both D Dl. } } }
Qed.

(* ================================================================= *)
(** ** Big-Step-Based Reasoning Rules for Divergence *)

(** In a partial correctness setting, it is also interesting to derive
    reasoning rules for establishing that a program diverges. These rules
    are stated and proved next. *)

Lemma divn_app_fix : forall s1 v1 v2 f x t1,
  v1 = val_fix f x t1 ->
  divn s1 (subst x v2 (subst f v1 t1)) ->
  divn s1 (trm_app v1 v2).
Proof using. introv E M. unfolds divn. applys* evalnp_app_fix. Qed.

(** **** Exercise: 2 stars, standard, especially useful (divn_let_ctx)

    Prove the divergence rule for a let-binding covering the case where the
    first subterm diverges. *)

Lemma divn_let_ctx : forall s1 x t1 t2,
  divn s1 t1 ->
  divn s1 (trm_let x t1 t2).
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

Lemma divn_let : forall s1 x t1 t2 Q1,
  evalnp s1 t1 Q1 ->
  (forall s2 v1, divn s2 (subst x v1 t2)) ->
  divn s1 (trm_let x t1 t2).
Proof using. introv M1 M2. unfolds divn. applys* evalnp_let M1. Qed.

Lemma divn_if : forall s1 b t1 t2,
  divn s1 (if b then t1 else t2) ->
  divn s1 (trm_if (val_bool b) t1 t2).
Proof using. introv M. unfolds divn. applys* evalnp_if. Qed.

(* ################################################################# *)
(** * Optional Material *)

(* ================================================================= *)
(** ** Interpretation of [evalnp] w.r.t. [eval] and [safe] *)

(** The predicate [safe s t] asserts that an execution of the configuration
    [t/s] can never get stuck. Its definition is a simplified version of
    [evalnp] where all occurences of [Q] are removed. In the rule for let-
    bindings, namely [safe_let], the quantification over the configuration
    [v1/s2] is done by refering to the big-step judgment [eval]. *)

CoInductive safe : state -> trm -> Prop :=
  | safe_val : forall s v,
      safe s (trm_val v)
  | safe_fix : forall s f x t1,
      safe s (trm_fix f x t1)
  | safe_app_fix : forall s v1 v2 f x t1,
      v1 = val_fix f x t1 ->
      safe s (subst x v2 (subst f v1 t1)) ->
      safe s (trm_app v1 v2)
  | safe_let : forall s x t1 t2,
      safe s t1 ->
      (forall v1 s2, eval s t1 s2 v1 -> safe s2 (subst x v1 t2)) ->
      safe s (trm_let x t1 t2)
  | safe_if : forall s b t1 t2,
      safe s (if b then t1 else t2) ->
      safe s (trm_if (val_bool b) t1 t2)
  | safe_add : forall s n1 n2,
      safe s (val_add (val_int n1) (val_int n2))
  | safe_rand : forall s n,
      n > 0 ->
      safe s (val_rand (val_int n))
  | safe_ref : forall s v,
      safe s (val_ref v)
  | safe_get : forall s p,
      Fmap.indom s p ->
      safe s (val_get (val_loc p))
  | safe_set : forall s p v,
      Fmap.indom s p ->
      safe s (val_set (val_loc p) v)
  | safe_free : forall s p,
      Fmap.indom s p ->
      safe s (val_free (val_loc p)).

Section EvalnpSafe.
Hint Constructors eval evalnp.

(** **** Exercise: 5 stars, standard, especially useful (evalnp_iff_safe_and_post)

    Prove that [evalnp s t Q] is equivalent to the conjunction of [safe s t]
    and to a partial correctness result asserting that if an evaluation of
    [t/s] terminates on a particular result, then this result satisfies [Q].
    Hint: make sure to split the equivalence and the conjunction before
    entering the coinductive proofs. *)

Lemma evalnp_iff_safe_and_post : forall s t Q,
  evalnp s t Q <-> (safe s t /\ (forall v s', eval s t s' v -> Q v s')).
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** Let [Any] denotes the postcondition that accepts any result. *)

Definition Any : val->state->Prop :=
  fun v s => True.

Hint Unfold Any.

(** **** Exercise: 2 stars, standard, especially useful (safe_iff_evalnp_any)

    Prove that [safe s t] is equivalent to [evalnp s t Any].
    Hint: a direct proof fails---why?
    The solution is to exploit [evalnp_iff_safe_and_post]. *)

Lemma safe_iff_evalnp_any : forall s t,
  safe s t <-> evalnp s t Any.
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

End EvalnpSafe.

(* ================================================================= *)
(** ** Small-Step Characterization of Partial Correctness *)

(** So far, this chapter has focused on handling partial correctness using
    a big-step semantics. In this bonus section, we investigate the treatment
    of partial correctness using a small-step semantics. *)

(** Before we get started, let us state and prove a basic lemma asserting
    that values cannot take a step. It will useful throughout the section. *)

Lemma exists_step_val_inv : forall s v,
  (exists s' t', step s v s' t') ->
  False.
Proof using. introv (s'&t'&S). inverts S. Qed.

(** In the chapter [Nondet], we presented a definition named
    [evals_attempt_3] that defined a small-step characterization of partial
    correctness. Let us rename this definition to [evalnps].

    The judgment [evalnps s t Q] asserts that, for any configuration
    [(s',t')] that can be reached from [(s',t')], either [t'] is a value that,
    together with [s'], satisfy the postcondition [Q]; or the configuration
    [(s',t')] can take a step, that is, it is not a stuck configuration. *)

Definition evalnps (s:state) (t:trm) (Q:val->state->Prop) : Prop :=
  forall s' t', evals s t s' t' ->
       (exists v, t' = trm_val v /\ Q v s')
    \/ (exists s'' t'', step s' t' s'' t'').

(** On top of [evalnps], we define a partial correctness Hoare triple
    judgment [hoarenps] in the usual way. *)

Definition hoarenps (t:trm) (H:hprop) (Q:val->hprop) : Prop :=
  forall s, H s -> evalnps s t Q.

(** The property [evalnps s t Q] may be viewed as a form of typing:
    the configuration [(s,t)] admits the "type" [Q].

    - Base case: if [t] is a value, we assert that a configuration [(s,v)] has
      type [Q] iff [Q v s] holds.

    - Preservation property: if the configuration [(s,t)] has type [Q] and
      reduces to [(s',t')], then the configuration [(s',t')] also admits the
      same type [Q].

    - Progress property: if the configuration [(s,t)] has type [Q], then
      either [t] is of the form [trm_val v] and [(s,v)] admits type [Q],
      or the configuration [(s,t)] can take a reduction step to some
      configuration [(s',t')].

    The progress property is, in essence, a partial correctness
    property. Indeed, it ensures that programs never get stuck, yet without
    imposing termination.

    In what follows, we formally state and prove the three properties
    associated with the judgment [evalnps s t Q]: the characterization of the
    base case, the preservation property, and the progress property. *)

(** First, let's prove an introduction lemma and an inversion lemma for the
    base case, that is, the characteriation of values. *)

Lemma evalnps_val : forall s v Q,
  Q v s ->
  evalnps s v Q.
Proof using.
  introv M R. inverts R as.
  { left*. }
  { intros s1 t1 R1 R2. false. inverts R1. }
Qed.

Lemma evalnps_val_inv : forall s v Q,
  evalnps s v Q ->
  Q v s.
Proof using.
  introv M. forwards N: M s v. { applys evals_refl. }
  destruct N as [(v1&E1&P1)|(s2&t2&R)].
  { inverts* E1. }
  { inverts R. }
Qed.

(** Second, let's prove the preservation property. *)

(** **** Exercise: 3 stars, standard, especially useful (evalnps_inv_step)

    Prove that the property [evalnps] for a given postcondition [Q] is
    preserved when a program takes a reduction step. *)

Lemma evalnps_inv_step : forall s1 t1 s2 t2 Q,
  evalnps s1 t1 Q ->
  step s1 t1 s2 t2 ->
  evalnps s2 t2 Q.
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** Third, let's prove the progress property. *)

(** **** Exercise: 4 stars, standard, especially useful (evalnps_not_val_inv)

    Prove that if the property [evalnps] holds for a given postcondition [Q],
    and for a configuration that has not already reached a value, then this
    configuration can take a step. Moreover, the configuration reached also
    satisfies the property [evalnps] for that same [Q]. *)

Lemma evalnps_not_val_inv : forall s1 t1 Q,
  evalnps s1 t1 Q ->
  (forall v, t1 <> trm_val v) ->
  exists s2 t2, step s1 t1 s2 t2 /\ evalnps s2 t2 Q.
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(* ================================================================= *)
(** ** Reasoning Rules w.r.t. Small-Step Characterization *)

(** We present two proofs of reasoning rules established with respect to the
    judgment [hoarenps]. The first proof targets the rule of consequence. This
    result leverages the covariance property for [evalnps]. *)

Lemma evalnps_conseq : forall s t Q Q',
  evalnps s t Q' ->
  Q' ===> Q ->
  evalnps s t Q.
Proof using.
  introv M WQ. introv R. lets [(v&E&P)|N]: M R.
  { left. exists v. split~. applys* WQ. }
  { right*. }
Qed.

Lemma hoarenps_conseq : forall t H' Q' H Q,
  hoarenps t H' Q' ->
  H ==> H' ->
  Q' ===> Q ->
  hoarenps t H Q.
Proof using.
  introv M WH WQ. intros h K. applys evalnps_conseq WQ.
  applys M. applys WH K.
Qed.

(** The second proof targets the reasoning rule for let-bindings, stated
    for the judgment [hoarenps]. This result leverages as key intermediate
    lemma an introduction rule for let-bindings with respect to [evalnps]. *)

(** **** Exercise: 5 stars, standard, especially useful (evalnps_let)

    Prove the reasoning rule for let-bindings for [evalnps].
    Hint: in the proof, you can use [tests C: (exists v1, t1 = trm_val v1)]
    to make a case analysis on whether [t1] is a value or not. *)

Lemma evalnps_let : forall s x t1 t2 Q1 Q,
  evalnps s t1 Q1 ->
  (forall s1 v1, Q1 v1 s1 -> evalnps s1 (subst x v1 t2) Q) ->
  evalnps s (trm_let x t1 t2) Q.
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

Lemma hoarenps_let : forall x t1 t2 H Q Q1,
  hoarenps t1 H Q1 ->
  (forall v1, hoarenps (subst x v1 t2) (Q1 v1) Q) ->
  hoarenps (trm_let x t1 t2) H Q.
Proof using.
  introv M1 M2. intros h K. applys* evalnps_let.
  { introv K'. applys* M2. }
Qed.

(* ================================================================= *)
(** ** Small-Step Characterization of Divergence *)

(** Recall the definition of [evalnps].

    Definition evalnps (s:state) (t:trm) (Q:val->state->Prop) : Prop :=
      forall s' t', evals s t s' t' ->
           (exists v, t' = trm_val v /\ Q v s')
        \/ (exists s'' t'', step s' t' s'' t'').

    The judgment [evalnps s t Q] can be specialized with the empty post-
    condition [Q := Empty] to express divergence, just like we did earlier on
    for setting up the definition of [divn].

    Recall that [Empty v s] is equivalent to [False]. Thus, let's take the
    definition of [evalnps s t Q] and replace [Q v s'] with [False]. The
    first clause of the disjunction, [exists v, t' = trm_val v /\ Q v s']
    is never satisfiable and thus may be removed. What remains is a simpler,
    direct characterization of the property that "all executions diverge".

    The corresponding predicate, named [divns s t] below, asserts that any
    execution prefix can be extended by at least one step. *)

Definition divns (s:state) (t:trm) : Prop :=
  forall s' t', evals s t s' t' ->
  exists s'' t'', step s' t' s'' t''.

(** **** Exercise: 3 stars, standard, optional (divns_iff_evalnps_Empty)

    Prove the equivalence between [divns] and the specialization
    of [evalnps] to [Empty]. *)

Lemma divns_iff_evalnps_Empty : forall s t,
  divns s t <-> evalnps s t Empty.
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** The three exercises that follow can be proved trivially by exploiting
    the equivalence [divns_iff_evalnps_Empty] then exploiting the already
    established properties of [evalnps]. However, it is interesting to
    know how to carry out proofs directly with respect to the definition
    [divns]. *)

(** **** Exercise: 2 stars, standard, optional (divns_inv_step)

    Prove that if a diverging configuration takes a step, then it reaches a
    configuration that also diverges. *)

Lemma divns_inv_step : forall s1 t1 s2 t2,
  divns s1 t1 ->
  step s1 t1 s2 t2 ->
  divns s2 t2.
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 2 stars, standard, optional (divns_val_inv)

    Prove that the execution of a value does not diverge. *)

Lemma divns_val_inv : forall s v,
  ~ divns s v.
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 5 stars, standard, optional (divns_let_ctx)

    Prove the divergence rule for a let-binding covering the case where the
    first subterm diverges, with respect to the definition [divns]. *)

Lemma divns_let_ctx : forall s1 x t1 t2,
  divns s1 t1 ->
  divns s1 (trm_let x t1 t2).
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(* ================================================================= *)
(** ** Coinductive, Small-Step Characterization of Partial Correctness *)

(** In the previous section, we characterized partial correctness using the
    judgment [evalnps], which is defined in terms of the transitive closure
    of the small-step relation [evals]. In this section, we present an
    alternative definition, based on a coinductive definition.

    Concretely, we start from the inductively defined judgment [evalns],
    which characterizes total correctness, and we consider the coinductive
    intrepretation of the same rules. The resulting judgment is written
    [evalnpz s t Q]. This coinductive definition, because it allows for
    infinite derivations, covers the case of diverging computations that
    take involve infinitely many reduction steps. *)

CoInductive evalnpz : state->trm->(val->hprop)->Prop :=
  | evalnpz_val : forall s v Q,
      Q v s ->
      evalnpz s v Q
  | evalnpz_step : forall s t Q,
      (exists s' t', step s t s' t') ->
      (forall s' t', step s t s' t' -> evalnpz s' t' Q) ->
      evalnpz s t Q.

(** We name [hoarenpz] the associated Hoare triple definition. *)

Definition hoarenpz (t:trm) (H:hprop) (Q:val->hprop) : Prop :=
  forall s, H s -> evalnpz s t Q.

(** Here again, we focus on the proofs of two particular reasoning rules,
    established with respect to [evalnpz]. *)

(** Firstly, let's prove the rule of consequence. The key intermediate result is
    to establish the covariance of [evalnpz]. Observe that this proof is to
    be conducted by coinduction. *)

Lemma evalnpz_conseq : forall s t Q Q',
  evalnpz s t Q' ->
  Q' ===> Q ->
  evalnpz s t Q.
Proof using.
  introv M WQ. gen s t Q'. cofix IH; intros. destruct M.
  { applys evalnpz_val. applys* WQ. }
  { applys evalnpz_step.
    { eauto. }
    { introv R'. lets M': H0 R'. applys IH M' WQ. } }
Qed.

Lemma hoarenpz_conseq : forall t H' Q' H Q,
  hoarenpz t H' Q' ->
  H ==> H' ->
  Q' ===> Q ->
  hoarenpz t H Q.
Proof using.
  introv M WH WQ. intros h K. applys evalnpz_conseq WQ.
  applys M. applys WH K.
Qed.

(** Secondly, we let's prove the reasoning rule for let-bindings. Here again,
    the key intermediate result is to establish a rule for [evalnpz]. *)

(** **** Exercise: 5 stars, standard, especially useful (hoarenpz_let)

    Prove the reasoning rule for let-bindings stated for [evalnpz].
    Hint: to set up the coinductive proof, follow the template that appears
    at the beginning of the proof of [evalnpz_conseq]. *)

Lemma evalnpz_let : forall s x t1 t2 Q1 Q,
  evalnpz s t1 Q1 ->
  (forall s1 v1, Q1 v1 s1 -> evalnpz s1 (subst x v1 t2) Q) ->
  evalnpz s (trm_let x t1 t2) Q.
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

Lemma hoarenpz_let : forall x t1 t2 H Q Q1,
  hoarenpz t1 H Q1 ->
  (forall v1, hoarenpz (subst x v1 t2) (Q1 v1) Q) ->
  hoarenpz (trm_let x t1 t2) H Q.
Proof using.
  introv M1 M2. intros h K. applys* evalnpz_let.
  { introv K'. applys* M2. }
Qed.

(** To express diverge, the judgment [evalnp s t Q] may be specialized with
    the postcondition [Q := Empty]. Starting from the definition of
    [evalnpz], replacing [Q v s] with [False] is equivalent to removing
    the constructor [evalnpz_val] altogether. Thus, divergence of a
    configuration [(s,t)] may be characterized directly by the coinductive
    judgment [divnz s t] defined below, featuring a single constructor. *)

CoInductive divnz : state -> trm -> Prop :=
  | divnz_step : forall s1 t1,
      (exists s2 t2, step s1 t1 s2 t2) ->
      (forall s2 t2, step s1 t1 s2 t2 -> divnz s2 t2) ->
      divnz s1 t1.

(** **** Exercise: 4 stars, standard, optional (divnz_iff_evalnpz_Empty)

    Prove the equivalence between [divnz] and the specialization of the
    judgment [evalnp] to [Empty]. *)

Lemma divnz_iff_evalnpz_Empty : forall s t,
  divnz s t <-> evalnpz s t Empty.
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(* ================================================================= *)
(** ** Equivalence Between the Two Small-Step Charact. of Partial Correctness *)

(** This section establishes that [hoarenpz] is equivalent to [hoarenps].
    The key result is to prove [evalnpz] equivalent to [evalnps]. *)

Lemma evalnpz_eq_evalnps :
  evalnpz = evalnps.
Proof using.
  extens. intros s t Q. iff M.
  { introv R. gen M. induction R; intros.
    { inverts M as M1 M2.
      { left*. }
      { right. applys M1. } }
    { rename H into R1, R into R2. inverts M as M1 M2.
      { false. inverts R1. }
      { applys IHR. applys M2 R1. } } }
  { gen s t Q. cofix IH. intros.
    tests C: (exists v, t = trm_val v).
    { destruct C as (v&->). applys evalnpz_val. applys evalnps_val_inv M. }
    { lets (s2&t2&R2&RS): evalnps_not_val_inv M C. applys evalnpz_step.
      { exists* s2 t2. }
      { intros s' t' R'. applys IH. applys evalnps_inv_step M R'. } } }
Qed.

Lemma hoarenpz_eq_hoarenps :
  hoarenpz = hoarenps.
Proof using. unfold hoarenps, hoarenpz. rewrite* evalnpz_eq_evalnps. Qed.

(** As a corollary, we can establish the equivalence between the two small-step
    characterization of divergence. Indeed, both characterizations are obtained
    by specializing the postcondition of their underlying evaluation jugment to
    the empty postcondition, namely [Empty]. *)

Lemma divnz_eq_divns :
  divnz = divns.
Proof using.
  extens. intros s t.
  rewrite divns_iff_evalnps_Empty.
  rewrite divnz_iff_evalnpz_Empty.
  rewrite* evalnpz_eq_evalnps.
Qed.

(* ================================================================= *)
(** ** Equivalence Between Small-Step and Big-Step Partial Correctness Semantics *)

(** We end this chapter with the proof of equivalence between [hoarenps] and
    [hoarenp], establishing a formal relationship between partial correctness
    triples defined with respect to a small-step semantics and those defined
    with respect to a big-step semantics.

    The first step of the proof is to formally relate [evalnpz] and [evalnp],
    which are both defined coinductively. Then, we can derive the equality
    between [hoarenpz] and [hoarenp], and conclude using the equality
    [hoarenpz_eq_hoarenps], which was established earlier on. *)

(** The first direction is from [evalnpz] to [evalnp]. To establish it, we
    need 3 inversion lemmas for let-bindings. *)

Lemma evalnpz_let_inv_ctx : forall x s1 t1 t2 Q Q1,
  evalnpz s1 (trm_let x t1 t2) Q ->
  (fun v s => evals s1 t1 s v) ===> Q1 ->
  evalnpz s1 t1 Q1.
Proof using.
  cofix IH. introv M WQ. inverts M as M0 M'.
  tests C: (exists v1, t1 = trm_val v1).
  { destruct C as (v1&->). applys evalnpz_val.
    applys WQ. applys evals_refl. }
  { applys evalnpz_step.
    { destruct M0 as (s'&t'&S). inverts S as. 2:{ false* C. }
      intros S. exists. applys S. }
    { intros s2 t1' S. applys IH.
      { applys M'. applys step_let_ctx S. }
      { intros v s R. applys WQ. applys evals_step S R. } } }
Qed.

Lemma evalnpz_let_inv_cont : forall s1 s2 v1 x t1 t2 Q,
  evalnpz s1 (trm_let x t1 t2) Q ->
  evals s1 t1 s2 v1 ->
  evalnpz s2 (subst x v1 t2) Q.
Proof using.
  introv M R. gen_eq t1': (trm_val v1). induction R; intros; subst.
  { inverts M as _ M'. applys M'. applys step_let. }
  { rename H into S, R into R', t0 into t1'.
    inverts M as _ M'. applys* IHR. applys M'.
    applys step_let_ctx S. }
Qed.

Lemma evalnpz_let_inv : forall s1 x t1 t2 Q,
  evalnpz s1 (trm_let x t1 t2) Q ->
  exists Q1, evalnpz s1 t1 Q1
          /\ (forall v1 s2, Q1 v1 s2 -> evalnpz s2 (subst x v1 t2) Q).
Proof using.
  introv M. exists (fun v s => evals s1 t1 s (trm_val v)). split.
  { applys* evalnpz_let_inv_ctx M. }
  { introv K. applys* evalnpz_let_inv_cont M K. }
Qed.

(** Using these inversion lemmas, we can prove by induction the first
    direction, from [evalnpz] to [evalnp]. *)

Lemma evalnp_of_evalnpz : forall s t Q,
  evalnpz s t Q ->
  evalnp s t Q.
Proof using.
  cofix IH. introv M. destruct t; try solve [ inverts M; false_invert ].
  { inverts M as.
    { intros R. applys evalnp_val R. }
    { intros (s'&t'&S) _. inverts S. } }
  { inverts M as.
    { intros (s'&t'&S) _. inverts S. } }
  { inverts M as (s'&t'&S) M'. inverts S. } (* not included in semantics *)
  { rename v into f, v0 into x, t into t1.
    inverts M as (s'&t'&S) M1. inverts S.
    applys evalnp_fix.
    forwards M1': M1. { applys step_fix. }
    inverts M1' as. { auto. } { intros. false* exists_step_val_inv. } }
  { inverts M as (s'&t'&S) M1. inverts S as.
    { applys evalnp_app_fix. { reflexivity. } applys IH.
      applys M1. applys* step_app_fix. }
    { applys evalnp_add.
      forwards M1': M1. { applys step_add. }
      inverts M1' as. { auto. } { intros. false* exists_step_val_inv. } }
    { introv N. applys* evalnp_rand. { math. }
      intros n1' N1.
      forwards M1': M1. { applys* step_rand n1'. }
      inverts M1' as. { auto. } { intros. false* exists_step_val_inv. } }
    { introv D. applys* evalnp_ref. intros p' D'.
      forwards M1': M1. { applys* step_ref p'. }
      inverts M1' as. { auto. } { intros. false* exists_step_val_inv. } }
    { introv D. applys* evalnp_get.
      forwards M1': M1. { applys* step_get. }
      inverts M1' as. { auto. } { intros. false* exists_step_val_inv. } }
    { introv D. applys* evalnp_set.
      forwards M1': M1. { applys* step_set. }
      inverts M1' as. { auto. } { intros. false* exists_step_val_inv. } }
    { introv D. applys* evalnp_free.
      forwards M1': M1. { applys* step_free. }
      inverts M1' as. { auto. } { intros. false* exists_step_val_inv. } } }
  { inverts M as (s'&t'&S) M'. inverts S. } (* not included in semantics *)
  { lets (Q1&M1&M2): evalnpz_let_inv M. applys evalnp_let.
    { applys IH. applys M1. }
    { introv R. applys IH. applys M2 R. } }
  { inverts M as (s'&t'&S) M1. inverts S. applys evalnp_if.
    applys IH. applys M1. applys step_if. }
Qed.

(** For the reciprocal direction, we also need one key inversion lemma. It
    is stated below. Its hypothesis is [evalnp s t Q], and its conclusion
    corresponds to the disjunction of the constructors of the inductive
    definition of [evalnpz s t Q]. *)

Lemma evalnp_inv_step : forall s t Q,
  evalnp s t Q ->
     (exists v, t = trm_val v /\ Q v s)
  \/ ((exists s' t', step s t s' t' /\ evalnp s' t' Q)
      /\ (forall s' t', step s t s' t' -> evalnp s' t' Q)).
Proof using.
  introv M. gen s Q. induction t; intros; inverts M as.
  { introv R. left. eauto. }
  { introv R. right. split.
    { exists. split. { applys step_fix. } { applys* evalnp_val. } }
    { intros s' t' S. inverts S. applys* evalnp_val. } }
  { introv M1. right. split.
    { exists. split. { applys* step_app_fix. } { auto. } }
    { intros s' t' S. inverts S as E. inverts E. auto. } }
  { introv R. right. split.
    { exists. split. { applys step_add. } { applys* evalnp_val. } }
    { intros s' t' S. inverts S. applys* evalnp_val. } }
  { introv N R. right. split.
    { exists. split. { applys* step_rand 0. math. }
       { applys* evalnp_val. applys R. math. } }
    { intros s' t' S. inverts S; tryfalse. applys* evalnp_val. } }
  { introv R. right. split.
    { forwards~ (p&D&N): (exists_fresh null s).
      exists. split. { applys* step_ref. } { applys* evalnp_val. } }
    { intros s' t' S. inverts S; tryfalse. applys* evalnp_val. } }
  { introv D R. right. split.
    { exists. split. { applys* step_get. } { applys* evalnp_val. } }
    { intros s' t' S. inverts S; tryfalse. applys* evalnp_val. } }
  { introv D R. right. split.
    { exists. split. { applys* step_set. } { applys* evalnp_val. } }
    { intros s' t' S. inverts S; tryfalse. applys* evalnp_val. } }
  { introv D R. right. split.
    { exists. split. { applys* step_free. } { applys* evalnp_val. } }
    { intros s' t' S. inverts S; tryfalse. applys* evalnp_val. } }
  { introv M1 M2. rename v into x. right. split.
    { forwards [(v1&->&HQ1)|((s'&t'&S'&M')&_)]: IHt1 M1.
      { exists. split. { applys step_let. } { applys* M2. } }
      { exists. split.
        { applys step_let_ctx S'. }
        { applys evalnp_let M'. applys M2. } } }
    { intros s' t' S. inverts S as S.
      { forwards [(v1&->&HQ1)|(_&M3)]: IHt1 M1.
        { inverts S. }
        { specializes M3 S. applys evalnp_let M3 M2. } }
      { inverts M1 as R. applys* M2. } } }
  { introv M1. right. split.
    { exists. split. { applys step_if. } { auto. } }
    { intros s' t' S. inverts S. auto. } }
Qed.

(** Using this inversion lemma, it is straightforward to derive the
    implication from [evalnp] to [evalnpz]. *)

Lemma evalnpz_of_coeval : forall s t Q,
  evalnp s t Q ->
  evalnpz s t Q.
Proof.
  cofix IH. introv M. lets C: evalnp_inv_step M.
  destruct C as [(v&->&HQ)|((s'&t'&S&M1)&M2)].
  { applys evalnpz_val HQ. }
  { applys evalnpz_step.
    { exists. applys S. }
    { intros s1 t1 S'. applys IH. applys M2 S'. } }
Qed.

(** Combining the two directions yields the equality between [evalnpz] and
    [evalnp], and that between [evalnps] and [evalnp]. *)

Lemma evalnpz_eq_evalnp :
   evalnpz = evalnp.
Proof using.
  extens. intros s t Q. iff M.
  { applys* evalnp_of_evalnpz. }
  { applys* evalnpz_of_coeval. }
Qed.

Lemma hoarenpcso_eq_hoarenp :
  hoarenpz = hoarenp.
Proof using. unfold hoarenp, hoarenpz. rewrite* evalnpz_eq_evalnp. Qed.

Lemma hoarenps_eq_hoarenp :
   hoarenps = hoarenp.
Proof using.
  rewrite <- hoarenpz_eq_hoarenps. rewrite* hoarenpcso_eq_hoarenp.
Qed.

(** As another corollary, we can establish the equivalence between the big-step
    and the small-step characterization of divergence. Indeed, both are
    obtained by specializing the postcondition to [Empty]. *)

Lemma divns_eq_divn :
  divns = divn.
Proof using.
  extens. intros s t. unfold divn.
  rewrite divns_iff_evalnps_Empty.
  rewrite <- evalnpz_eq_evalnp.
  rewrite* evalnpz_eq_evalnps.
Qed.

(* ================================================================= *)
(** ** Historical Notes *)

(** Many program verification tools target partial correctness only, or provide
    separate tooling for justifying termination.

    The soundness of program logics delivering partial correctness is nearly
    always justified with respect to a small-step semantics of the programming
    language. Partial correctness is generally chosen because it appears better
    suited for reasoning about programs that involve some amount of
    concurrency, and for programs that are not meant to terminate (e.g., system
    kernels).

    Capturing partial correctness using a coinductive big-step judgment, as done
    in this chapter with the predicate [evalnp], appears to be novel as of Jan.
    2021. *)

(* 2022-04-25 18:29 *)
