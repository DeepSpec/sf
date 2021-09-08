(** * LibSepMinimal: Appendix - Minimalistic Soundness Proof *)

(** This file contains a stand-alone, minimalistic formalization of the
    soundness of Separation Logic reasoning rules with respect to the big-step
    semantics of an imperative lambda-calculus. This formalization accompanies
    the ICFP'20 paper _Separation Logic for Sequential Programs_:
    http://www.chargueraud.org/research/2020/seq_seplogic/seq_seplogic.pdf . *)

(* ################################################################# *)
(** * Source Language *)

(* ================================================================= *)
(** ** Syntax *)

Set Implicit Arguments.
From SLF Require Export LibString LibCore.
From SLF Require Export LibSepTLCbuffer LibSepFmap.
Module Fmap := LibSepFmap.

(** Variables are defined as strings, [var_eq] denotes boolean comparison. *)

Definition var : Type := string.

Definition var_eq := String.string_dec.

(** Locations are defined as natural numbers. *)

Definition loc : Type := nat.

(** Primitive operations include memory operations, as well as addition and
    division to illustrate a total and a partial arithmetic operations. *)

Inductive prim : Type :=
  | val_ref : prim
  | val_get : prim
  | val_set : prim
  | val_free : prim
  | val_add : prim
  | val_div : prim.

(** The grammar of closed values (assumed to contain no free variables)
    includes values of ground types, primitive operations, and closures. *)

Inductive val : Type :=
  | val_unit : val
  | val_bool : bool -> val
  | val_int : int -> val
  | val_loc : loc -> val
  | val_prim : prim -> val
  | val_fix : var -> var -> trm -> val

(** The grammar of terms includes closed values, variables, functions,
    applications, let-binding and conditional. *)

with trm : Type :=
  | trm_val : val -> trm
  | trm_var : var -> trm
  | trm_fix : var -> var -> trm -> trm
  | trm_app : trm -> trm -> trm
  | trm_let : var -> trm -> trm -> trm
  | trm_if : trm -> trm -> trm -> trm.

(** Coercions are used to improve conciseness in the statment of evaluation
    rules. *)

Coercion val_bool : bool >-> val.
Coercion val_int : Z >-> val.
Coercion val_loc : loc >-> val.
Coercion val_prim : prim >-> val.
Coercion trm_val : val >-> trm.
Coercion trm_var : var >-> trm.
Coercion trm_app : trm >-> Funclass.

(** The type of values is inhabited (useful for finite map operations). *)

Global Instance Inhab_val : Inhab val.
Proof. apply (Inhab_of_val val_unit). Qed.

(** A heap, a.k.a. state, consists of a finite map from location to values.
    Finite maps are formalized in the file [LibSepFmap.v]. (We purposely do not
    use TLC's finite map library to avoid complications with typeclasses.) *)

Definition heap : Type := fmap loc val.

(** Implicit types associate meta-variable with types. *)

Implicit Types f : var.
Implicit Types b : bool.
Implicit Types p : loc.
Implicit Types n : int.
Implicit Types v w r : val.
Implicit Types t : trm.
Implicit Types s h : heap.

(* ================================================================= *)
(** ** Semantics *)

(** The standard capture-avoiding substitution is written [subst y w t]. *)

Fixpoint subst (y:var) (w:val) (t:trm) : trm :=
  let aux t := subst y w t in
  let if_y_eq x t1 t2 := if var_eq x y then t1 else t2 in
  match t with
  | trm_val v => trm_val v
  | trm_var x => if_y_eq x (trm_val w) t
  | trm_fix f x t1 => trm_fix f x (if_y_eq f t1 (if_y_eq x t1 (aux t1)))
  | trm_app t1 t2 => trm_app (aux t1) (aux t2)
  | trm_let x t1 t2 => trm_let x (aux t1) (if_y_eq x t2 (aux t2))
  | trm_if t0 t1 t2 => trm_if (aux t0) (aux t1) (aux t2)
  end.

(** The big-step evaluation judgement, written [eval s t s' v], asserts that
    the evaluation of term [t] in state [s] terminates on a value [v] in a
    state [s']. *)

Inductive eval : heap -> trm -> heap -> val -> Prop :=
  | eval_val : forall s v,
      eval s (trm_val v) s v
  | eval_fix : forall s f x t1,
      eval s (trm_fix f x t1) s (val_fix f x t1)
  | eval_app : forall s1 s2 v1 v2 f x t1 v,
      v1 = val_fix f x t1 ->
      eval s1 (subst x v2 (subst f v1 t1)) s2 v ->
      eval s1 (trm_app v1 v2) s2 v
  | eval_let : forall s1 s2 s3 x t1 t2 v1 r,
      eval s1 t1 s2 v1 ->
      eval s2 (subst x v1 t2) s3 r ->
      eval s1 (trm_let x t1 t2) s3 r
  | eval_if : forall s1 s2 b v t1 t2,
      eval s1 (if b then t1 else t2) s2 v ->
      eval s1 (trm_if (val_bool b) t1 t2) s2 v
  | eval_add : forall m n1 n2,
      eval m (val_add (val_int n1) (val_int n2)) m (val_int (n1 + n2))
  | eval_div : forall m n1 n2,
       n2 <> 0 ->
     eval m (val_div (val_int n1) (val_int n2)) m (val_int (Z.quot n1 n2))
  | eval_ref : forall s v p,
      ~ Fmap.indom s p ->
      eval s (val_ref v) (Fmap.update s p v) (val_loc p)
  | eval_get : forall s p,
      Fmap.indom s p ->
      eval s (val_get (val_loc p)) s (Fmap.read s p)
  | eval_set : forall s p v,
      Fmap.indom s p ->
      eval s (val_set (val_loc p) v) (Fmap.update s p v) val_unit
  | eval_free : forall s p,
      Fmap.indom s p ->
      eval s (val_free (val_loc p)) (Fmap.remove s p) val_unit.

(* ================================================================= *)
(** ** Automation for Heap Equality and Heap Disjointness *)

(** For goals asserting equalities between heaps, i.e., of the form [h1 = h2],
    we set up automation so that it performs some tidying: substitution,
    removal of empty heaps, normalization with respect to associativity. *)

Hint Rewrite union_assoc union_empty_l union_empty_r : fmap.
Hint Extern 1 (_ = _ :> heap) => subst; autorewrite with fmap.

(** For goals asserting disjointness between heaps, i.e., of the form
    [Fmap.disjoint h1 h2], we set up automation to perform simplifications:
    substitution, exploit distributivity of the disjointness predicate over
    unions of heaps, and exploit disjointness with empty heaps. The tactic
    [jauto_set] used here comes from the TLC library; essentially, it destructs
    conjunctions and existentials. *)

Hint Resolve Fmap.disjoint_empty_l Fmap.disjoint_empty_r.
Hint Rewrite disjoint_union_eq_l disjoint_union_eq_r : disjoint.
Hint Extern 1 (Fmap.disjoint _ _) =>
  subst; autorewrite with rew_disjoint in *; jauto_set.

(* ################################################################# *)
(** * Heap Predicates and Entailment *)

(* ================================================================= *)
(** ** Extensionality Axioms *)

(** Extensionality axioms are essential to assert equalities between heap
    predicates of type [hprop], and between postconditions, of type
    [val->hprop]. *)

Axiom functional_extensionality : forall A B (f g:A->B),
  (forall x, f x = g x) ->
  f = g.

Axiom propositional_extensionality : forall (P Q:Prop),
  (P <-> Q) ->
  P = Q.

(* ================================================================= *)
(** ** Core Heap Predicates *)

(** The type of heap predicates is named [hprop]. *)

Definition hprop := heap -> Prop.

(** We bind a few more meta-variables. *)

Implicit Types P : Prop.
Implicit Types H : hprop.
Implicit Types Q : val->hprop.

(** Core heap predicates, and their associated notations:

    - [\[]] denotes the empty heap predicate
    - [\[P]] denotes a pure fact
    - [p ~~> v] denotes a singleton heap
    - [H1 \* H2] denotes the separating conjunction
    - [Q1 \*+ H2] denotes the separating conjunction extending a postcondition
    - [\exists x, H] denotes an existential
    - [\forall x, H] denotes a universal. *)

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

Definition hpure (P:Prop) : hprop := (* encoded as [\exists (p:P), \[]] *)
  hexists (fun (p:P) => hempty).

Declare Scope hprop_scope.

Notation "\[]" := (hempty)
  (at level 0) : hprop_scope.

Notation "\[ P ]" := (hpure P)
  (at level 0, format "\[ P ]") : hprop_scope.

Notation "p '~~>' v" := (hsingle p v) (at level 32) : hprop_scope.

Notation "H1 '\*' H2" := (hstar H1 H2)
  (at level 41, right associativity) : hprop_scope.

Notation "Q \*+ H" := (fun x => hstar (Q x) H)
  (at level 40) : hprop_scope.

Notation "'\exists' x1 .. xn , H" :=
  (hexists (fun x1 => .. (hexists (fun xn => H)) ..))
  (at level 39, x1 binder, H at level 50, right associativity,
   format "'[' '\exists' '/ '  x1  ..  xn , '/ '  H ']'") : hprop_scope.

Notation "'\forall' x1 .. xn , H" :=
  (hforall (fun x1 => .. (hforall (fun xn => H)) ..))
  (at level 39, x1 binder, H at level 50, right associativity,
   format "'[' '\forall' '/ '  x1  ..  xn , '/ '  H ']'") : hprop_scope.

(* ================================================================= *)
(** ** Entailment *)

Declare Scope hprop_scope.
Open Scope hprop_scope.

(** Entailment for heap predicates, written [H1 ==> H2]. *)

Definition himpl (H1 H2:hprop) : Prop :=
  forall h, H1 h -> H2 h.

Notation "H1 ==> H2" := (himpl H1 H2) (at level 55) : hprop_scope.

(** Entailment between postconditions, written [Q1 ===> Q2] *)

Definition qimpl A (Q1 Q2:A->hprop) : Prop :=
  forall (v:A), Q1 v ==> Q2 v.

Notation "Q1 ===> Q2" := (qimpl Q1 Q2) (at level 55) : hprop_scope.

(** Entailment defines an order on heap predicates *)

Lemma himpl_refl : forall H,
  H ==> H.
Proof. introv M. auto. Qed.

Lemma himpl_trans : forall H2 H1 H3,
  (H1 ==> H2) ->
  (H2 ==> H3) ->
  (H1 ==> H3).
Proof. introv M1 M2. unfolds* himpl. Qed.

Lemma himpl_antisym : forall H1 H2,
  (H1 ==> H2) ->
  (H2 ==> H1) ->
  (H1 = H2).
Proof. introv M1 M2. applys pred_ext_1. intros h. iff*. Qed.

Lemma qimpl_refl : forall Q,
  Q ===> Q.
Proof. intros Q v. applys himpl_refl. Qed.

Hint Resolve himpl_refl qimpl_refl.

(* ================================================================= *)
(** ** Properties of [hstar] *)

Lemma hstar_intro : forall H1 H2 h1 h2,
  H1 h1 ->
  H2 h2 ->
  Fmap.disjoint h1 h2 ->
  (H1 \* H2) (Fmap.union h1 h2).
Proof. intros. exists* h1 h2. Qed.

Lemma hstar_comm : forall H1 H2,
   H1 \* H2 = H2 \* H1.
Proof.
  unfold hprop, hstar. intros H1 H2. applys himpl_antisym.
  { intros h (h1&h2&M1&M2&D&U).
    rewrite* Fmap.union_comm_of_disjoint in U. exists* h2 h1. }
  { intros h (h1&h2&M1&M2&D&U).
    rewrite* Fmap.union_comm_of_disjoint in U. exists* h2 h1. }
Qed.

Lemma hstar_assoc : forall H1 H2 H3,
  (H1 \* H2) \* H3 = H1 \* (H2 \* H3).
Proof.
  intros H1 H2 H3. applys himpl_antisym; intros h.
  { intros (h'&h3&(h1&h2&M3&M4&D'&U')&M2&D&U). subst h'.
    exists h1 (h2 \+ h3). splits*. { applys* hstar_intro. } }
  { intros (h1&h'&M1&(h2&h3&M3&M4&D'&U')&D&U). subst h'.
    exists (h1 \+ h2) h3. splits*. { applys* hstar_intro. } }
Qed.

Lemma hstar_hempty_l : forall H,
  \[] \* H = H.
Proof.
  intros. applys himpl_antisym; intros h.
  { intros (h1&h2&M1&M2&D&U). hnf in M1. subst. rewrite* Fmap.union_empty_l. }
  { intros M. exists (@Fmap.empty loc val) h. splits*. { hnfs*. } }
Qed.

Lemma hstar_hexists : forall A (J:A->hprop) H,
  (hexists J) \* H = hexists (fun x => (J x) \* H).
Proof.
  intros. applys himpl_antisym; intros h.
  { intros (h1&h2&(x&M1)&M2&D&U). exists* x h1 h2. }
  { intros (x&(h1&h2&M1&M2&D&U)). exists h1 h2. splits*. { exists* x. } }
Qed.

Lemma hstar_hforall : forall H A (J:A->hprop),
  (hforall J) \* H ==> hforall (J \*+ H).
Proof.
  intros. intros h M. destruct M as (h1&h2&M1&M2&D&U). intros x. exists* h1 h2.
Qed.

Lemma himpl_frame_l : forall H2 H1 H1',
  H1 ==> H1' ->
  (H1 \* H2) ==> (H1' \* H2).
Proof. introv W (h1&h2&?). exists* h1 h2. Qed.

(** Additional, symmetric results, useful for tactics *)

Lemma hstar_hempty_r : forall H,
  H \* \[] = H.
Proof.
  applys neutral_r_of_comm_neutral_l. applys* hstar_comm. applys* hstar_hempty_l.
Qed.

Lemma himpl_frame_r : forall H1 H2 H2',
  H2 ==> H2' ->
  (H1 \* H2) ==> (H1 \* H2').
Proof.
  introv M. do 2 rewrite (@hstar_comm H1). applys* himpl_frame_l.
Qed.

(* ================================================================= *)
(** ** Properties of [hpure] *)

Lemma hstar_hpure_l : forall P H h,
  (\[P] \* H) h = (P /\ H h).
Proof.
  intros. apply prop_ext. unfold hpure.
  rewrite hstar_hexists. rewrite* hstar_hempty_l.
  iff (p&M) (p&M). { split*. } { exists* p. }
Qed.

Lemma himpl_hstar_hpure_r : forall P H H',
  P ->
  (H ==> H') ->
  H ==> (\[P] \* H').
Proof. introv HP W. intros h K. rewrite* hstar_hpure_l. Qed.

Lemma himpl_hstar_hpure_l : forall P H H',
  (P -> H ==> H') ->
  (\[P] \* H) ==> H'.
Proof. introv W Hh. rewrite hstar_hpure_l in Hh. applys* W. Qed.

(* ================================================================= *)
(** ** Properties of [hexists] *)

Lemma himpl_hexists_l : forall A H (J:A->hprop),
  (forall x, J x ==> H) ->
  (hexists J) ==> H.
Proof. introv W. intros h (x&Hh). applys* W. Qed.

Lemma himpl_hexists_r : forall A (x:A) H J,
  (H ==> J x) ->
  H ==> (hexists J).
Proof. introv W. intros h. exists x. apply* W. Qed.

Lemma himpl_hexists : forall A (J1 J2:A->hprop),
  J1 ===> J2 ->
  hexists J1 ==> hexists J2.
Proof.
  introv W. applys himpl_hexists_l. intros x. applys himpl_hexists_r W.
Qed.

(* ================================================================= *)
(** ** Properties of [hforall] *)

Lemma himpl_hforall_r : forall A (J:A->hprop) H,
  (forall x, H ==> J x) ->
  H ==> (hforall J).
Proof. introv M. intros h Hh x. apply* M. Qed.

Lemma himpl_hforall_l : forall A x (J:A->hprop) H,
  (J x ==> H) ->
  (hforall J) ==> H.
Proof. introv M. intros h Hh. apply* M. Qed.

Lemma himpl_hforall : forall A (J1 J2:A->hprop),
  J1 ===> J2 ->
  hforall J1 ==> hforall J2.
Proof.
  introv W. applys himpl_hforall_r. intros x. applys himpl_hforall_l W.
Qed.

(* ================================================================= *)
(** ** Properties of [hsingle] *)

Lemma hstar_hsingle_same_loc : forall p v1 v2,
  (p ~~> v1) \* (p ~~> v2) ==> \[False].
Proof.
  intros. unfold hsingle. intros h (h1&h2&E1&E2&D&E). false.
  subst. applys* Fmap.disjoint_single_single_same_inv.
Qed.

(* ================================================================= *)
(** ** Basic Tactics for Simplifying Entailments *)

(** [xsimpl] performs immediate simplifications on entailment relations. *)

Hint Rewrite hstar_assoc hstar_hempty_l hstar_hempty_r : hstar.

Tactic Notation "xsimpl" :=
  try solve [ apply qimpl_refl ];
  try match goal with |- _ ===> _ => intros ? end;
  autorewrite with hstar; repeat match goal with
  | |- ?H \* _ ==> ?H \* _ => apply himpl_frame_r
  | |- _ \* ?H ==> _ \* ?H => apply himpl_frame_l
  | |- _ \* ?H ==> ?H \* _ => rewrite hstar_comm; apply himpl_frame_r
  | |- ?H \* _ ==> _ \* ?H => rewrite hstar_comm; apply himpl_frame_l
  | |- ?H ==> ?H => apply himpl_refl
  | |- ?H ==> ?H' => is_evar H'; apply himpl_refl end.

Tactic Notation "xsimpl" "*" := xsimpl; auto_star.

(** [xchange] helps rewriting in entailments. *)

Lemma xchange_lemma : forall H1 H1',
  H1 ==> H1' -> forall H H' H2,
  H ==> H1 \* H2 ->
  H1' \* H2 ==> H' ->
  H ==> H'.
Proof.
  introv M1 M2 M3. applys himpl_trans M2. applys himpl_trans M3.
  applys himpl_frame_l. applys M1.
Qed.

Tactic Notation "xchange" constr(M) :=
  forwards_nounfold_then M ltac:(fun K =>
    eapply xchange_lemma; [ eapply K | xsimpl | ]).

(* ================================================================= *)
(** ** Reformulation of the Evaluation Rules for Primitive Operations. *)

Lemma eval_ref_sep : forall s1 s2 v p,
  s2 = Fmap.single p v ->
  Fmap.disjoint s2 s1 ->
  eval s1 (val_ref v) (Fmap.union s2 s1) (val_loc p).
Proof.
  introv -> D. forwards Dv: Fmap.indom_single p v.
  rewrite <- Fmap.update_eq_union_single. applys* eval_ref.
  { intros N. applys* Fmap.disjoint_inv_not_indom_both D N. }
Qed.

Lemma eval_get_sep : forall s s2 p v,
  s = Fmap.union (Fmap.single p v) s2 ->
  eval s (val_get (val_loc p)) s v.
Proof.
  introv ->. forwards Dv: Fmap.indom_single p v. applys_eq eval_get.
  { rewrite* Fmap.read_union_l. rewrite* Fmap.read_single. }
  { applys* Fmap.indom_union_l. }
Qed.

Lemma eval_set_sep : forall s1 s2 h2 p v1 v2,
  s1 = Fmap.union (Fmap.single p v1) h2 ->
  s2 = Fmap.union (Fmap.single p v2) h2 ->
  Fmap.disjoint (Fmap.single p v1) h2 ->
  eval s1 (val_set (val_loc p) v2) s2 val_unit.
Proof.
  introv -> -> D. forwards Dv: Fmap.indom_single p v1. applys_eq eval_set.
  { rewrite* Fmap.update_union_l. fequals. rewrite* Fmap.update_single. }
  { applys* Fmap.indom_union_l. }
Qed.

Lemma eval_free_sep : forall s1 s2 v p,
  s1 = Fmap.union (Fmap.single p v) s2 ->
  Fmap.disjoint (Fmap.single p v) s2 ->
  eval s1 (val_free p) s2 val_unit.
Proof.
  introv -> D. forwards Dv: Fmap.indom_single p v. applys_eq eval_free.
  { rewrite* Fmap.remove_union_single_l. intros Dl.
    applys Fmap.disjoint_inv_not_indom_both D Dl. applys Fmap.indom_single. }
  { applys* Fmap.indom_union_l. }
Qed.

(* ################################################################# *)
(** * Hoare Logic *)

(* ================================================================= *)
(** ** Definition of Total Correctness Hoare Triples *)

Definition hoare (t:trm) (H:hprop) (Q:val->hprop) :=
  forall h, H h -> exists h' v, eval h t h' v /\ Q v h'.

(* ================================================================= *)
(** ** Structural Rules for Hoare Triples *)

Lemma hoare_conseq : forall t H' Q' H Q,
  hoare t H' Q' ->
  H ==> H' ->
  Q' ===> Q ->
  hoare t H Q.
Proof.
  introv M MH MQ HF. forwards (h'&v&R&K): M h. { applys* MH. }
  exists h' v. splits*. { applys* MQ. }
Qed.

Lemma hoare_hexists : forall t (A:Type) (J:A->hprop) Q,
  (forall x, hoare t (J x) Q) ->
  hoare t (hexists J) Q.
Proof. introv M. intros h (x&Hh). applys M Hh. Qed.

Lemma hoare_hpure : forall t (P:Prop) H Q,
  (P -> hoare t H Q) ->
  hoare t (\[P] \* H) Q.
Proof.
  introv M. intros h (h1&h2&(M1&HP)&M2&D&U). hnf in HP. subst.
  rewrite Fmap.union_empty_l. applys* M.
Qed.

(* ================================================================= *)
(** ** Reasoning Rules for Terms, for Hoare Triples *)

Lemma hoare_val : forall v H Q,
  H ==> Q v ->
  hoare (trm_val v) H Q.
Proof.
  introv M. intros h K. exists h v. splits.
  { applys eval_val. }
  { applys* M. }
Qed.

Lemma hoare_fix : forall f x t1 H Q,
  H ==> Q (val_fix f x t1) ->
  hoare (trm_fix f x t1) H Q.
Proof.
  introv M. intros h K. exists h (val_fix f x t1). splits.
  { applys* eval_fix. }
  { applys* M. }
Qed.

Lemma hoare_app : forall v1 v2 f x t1 H Q,
  v1 = val_fix f x t1 ->
  hoare (subst x v2 (subst f v1 t1)) H Q ->
  hoare (trm_app v1 v2) H Q.
Proof.
  introv E M. intros s K0. forwards (s'&v&R1&K1): (rm M) K0.
  exists s' v. splits. { applys eval_app E R1. } { applys K1. }
Qed.

Lemma hoare_let : forall x t1 t2 H Q Q1,
  hoare t1 H Q1 ->
  (forall v1, hoare (subst x v1 t2) (Q1 v1) Q) ->
  hoare (trm_let x t1 t2) H Q.
Proof.
  introv M1 M2 Hh. forwards* (h1'&v1&R1&K1): (rm M1).
  forwards* (h2'&v2&R2&K2): (rm M2).
  exists h2' v2. splits*. { applys* eval_let. }
Qed.

Lemma hoare_if : forall (b:bool) t1 t2 H Q,
  hoare (if b then t1 else t2) H Q ->
  hoare (trm_if b t1 t2) H Q.
Proof.
  introv M1. intros h Hh. forwards* (h1'&v1&R1&K1): (rm M1).
  exists h1' v1. splits*. { applys* eval_if. }
Qed.

(* ================================================================= *)
(** ** Specification of Primitive Operations, for Hoare Triples. *)

Lemma hoare_add : forall H n1 n2,
  hoare (val_add n1 n2)
    H
    (fun r => \[r = val_int (n1 + n2)] \* H).
Proof.
  intros. intros s K0. exists s (val_int (n1 + n2)). split.
  { applys eval_add. }
  { rewrite* hstar_hpure_l. }
Qed.

Lemma hoare_div : forall H n1 n2,
  n2 <> 0 ->
  hoare (val_div n1 n2)
    H
    (fun r => \[r = val_int (Z.quot n1 n2)] \* H).
Proof.
  introv N. intros s K0. exists s (val_int (Z.quot n1 n2)). split.
  { applys eval_div N. }
  { rewrite* hstar_hpure_l. }
Qed.

Lemma hoare_ref : forall H v,
  hoare (val_ref v)
    H
    (fun r => (\exists p, \[r = val_loc p] \* p ~~> v) \* H).
Proof.
  intros. intros s1 K0. forwards* (p&D&N): (Fmap.single_fresh 0%nat s1 v).
  exists (Fmap.union (Fmap.single p v) s1) (val_loc p). split.
  { applys* eval_ref_sep D. }
  { applys* hstar_intro.
    { exists p. rewrite* hstar_hpure_l. split*. { hnfs*. } } }
Qed.

Lemma hoare_get : forall H v p,
  hoare (val_get p)
    ((p ~~> v) \* H)
    (fun r => \[r = v] \* (p ~~> v) \* H).
Proof.
  intros. intros s K0. exists s v. split.
  { destruct K0 as (s1&s2&->&P2&D&U). applys eval_get_sep U. }
  { rewrite* hstar_hpure_l. }
Qed.

Lemma hoare_set : forall H w p v,
  hoare (val_set (val_loc p) w)
    ((p ~~> v) \* H)
    (fun r => (p ~~> w) \* H).
Proof.
  intros. intros s1 (h1&h2&->&P2&D&U).
  exists (Fmap.union (Fmap.single p w) h2) val_unit. split.
  { applys eval_set_sep U D. auto. }
  { applys* hstar_intro.
    { hnfs*. }
    { applys Fmap.disjoint_single_set D. } }
Qed.

Lemma hoare_free : forall H p v,
  hoare (val_free (val_loc p))
    ((p ~~> v) \* H)
    (fun r => H).
Proof.
  intros. intros s1 (h1&h2&->&P2&D&U). exists h2 val_unit. split.
  { applys eval_free_sep U D. }
  { auto. }
Qed.

(** From now on, all operators have opaque definitions *)

Global Opaque hempty hpure hstar hsingle hexists hforall.

(* ################################################################# *)
(** * Separation Logic *)

(* ================================================================= *)
(** ** Definition of Separation Logic triples *)

Definition triple (t:trm) (H:hprop) (Q:val->hprop) : Prop :=
  forall (H':hprop), hoare t (H \* H') (Q \*+ H').

(* ================================================================= *)
(** ** Structural Rules *)

Lemma triple_conseq : forall t H' Q' H Q,
  triple t H' Q' ->
  H ==> H' ->
  Q' ===> Q ->
  triple t H Q.
Proof.
  introv M MH MQ. intros HF. applys hoare_conseq M.
  { xchange MH. xsimpl. }
  { intros x. xchange (MQ x). xsimpl. }
Qed.

Lemma triple_frame : forall t H Q H',
  triple t H Q ->
  triple t (H \* H') (Q \*+ H').
Proof.
  introv M. intros HF. applys hoare_conseq (M (HF \* H')); xsimpl.
Qed.

Lemma triple_hexists : forall t (A:Type) (J:A->hprop) Q,
  (forall x, triple t (J x) Q) ->
  triple t (hexists J) Q.
Proof.
  introv M. intros HF. rewrite hstar_hexists.
  applys hoare_hexists. intros. applys* M.
Qed.

Lemma triple_hpure : forall t (P:Prop) H Q,
  (P -> triple t H Q) ->
  triple t (\[P] \* H) Q.
Proof.
  introv M. intros HF. rewrite hstar_assoc.
  applys hoare_hpure. intros. applys* M.
Qed.

(* ================================================================= *)
(** ** Reasoning Rules for Terms *)

Lemma triple_val : forall v H Q,
  H ==> Q v ->
  triple (trm_val v) H Q.
Proof.
  introv M. intros HF. applys hoare_val. { xchange M. xsimpl. }
Qed.

Lemma triple_fix : forall f x t1 H Q,
  H ==> Q (val_fix f x t1) ->
  triple (trm_fix f x t1) H Q.
Proof.
  introv M. intros HF. applys hoare_fix. { xchange M. xsimpl. }
Qed.

Lemma triple_let : forall x t1 t2 Q1 H Q,
  triple t1 H Q1 ->
  (forall v1, triple (subst x v1 t2) (Q1 v1) Q) ->
  triple (trm_let x t1 t2) H Q.
Proof.
  introv M1 M2. intros HF. applys hoare_let.
  { applys M1. }
  { intros v. applys hoare_conseq M2; xsimpl. }
Qed.

Lemma triple_if : forall (b:bool) t1 t2 H Q,
  triple (if b then t1 else t2) H Q ->
  triple (trm_if b t1 t2) H Q.
Proof.
  introv M1. intros HF. applys hoare_if. applys M1.
Qed.

Lemma triple_app : forall v1 v2 f x t1 H Q,
  v1 = val_fix f x t1 ->
  triple (subst x v2 (subst f v1 t1)) H Q ->
  triple (trm_app v1 v2) H Q.
Proof.
  introv E M1. intros H'. applys hoare_app E. applys M1.
Qed.

(* ================================================================= *)
(** ** Specification of Primitive Operations *)

Lemma triple_add : forall n1 n2,
  triple (val_add n1 n2)
    \[]
    (fun r => \[r = val_int (n1 + n2)]).
Proof. intros. intros H'. applys hoare_conseq hoare_add; xsimpl*. Qed.

Lemma triple_div : forall n1 n2,
  n2 <> 0 ->
  triple (val_div n1 n2)
    \[]
    (fun r => \[r = val_int (Z.quot n1 n2)]).
Proof. intros. intros H'. applys* hoare_conseq hoare_div; xsimpl*. Qed.

Lemma triple_ref : forall v,
  triple (val_ref v)
    \[]
    (fun r => \exists p, \[r = val_loc p] \* p ~~> v).
Proof. intros. intros HF. applys hoare_conseq hoare_ref; xsimpl*. Qed.

Lemma triple_get : forall v p,
  triple (val_get (val_loc p))
    (p ~~> v)
    (fun x => \[x = v] \* (p ~~> v)).
(* COQBUG in v8.10, therefore using an alternative proof.
   Proof. intros. intros HF. applys hoare_conseq hoare_get; xsimpl*. Qed.
*)
Proof. intros. intros HF. applys hoare_conseq hoare_get. xsimpl*. xsimpl*. Qed.

Lemma triple_set : forall w p v,
  triple (val_set (val_loc p) w)
    (p ~~> v)
    (fun _ => p ~~> w).
Proof. intros. intros HF. applys hoare_conseq hoare_set; xsimpl*. Qed.

Lemma triple_free : forall p v,
  triple (val_free (val_loc p))
    (p ~~> v)
    (fun _ => \[]).
Proof. intros. intros HF. applys hoare_conseq hoare_free; xsimpl*. Qed.


(* ################################################################# *)
(** * Bonus: Example Proof *)

(** See chapter [Rules] for comments on this proof.

OCaml:

   let incr p =
      let n = !p in
      let m = n+1 in
      p := m
*)

(** Definition of the function [incr], using low-level syntax. *)

Open Scope string_scope.

Definition incr : val :=
  val_fix "f" "p" (
    trm_let "n" (trm_app val_get (trm_var "p")) (
    trm_let "m" (trm_app (trm_app val_add
                             (trm_var "n")) (val_int 1)) (
    trm_app (trm_app val_set (trm_var "p")) (trm_var "m")))).

(** Specification of the function [incr]. *)

Lemma triple_incr : forall (p:loc) (n:int),
  triple (trm_app incr p)
    (p ~~> n)
    (fun _ => p ~~> (n+1)).

(** Verification of [incr], applying the reasoning rules by hand. *)

Proof using.
  intros. applys triple_app. { reflexivity. } simpl.
  applys triple_let. { apply triple_get. }
  intros n'. simpl. apply triple_hpure. intros ->.
  applys triple_let. { applys triple_conseq.
    { applys triple_frame. applys triple_add. }
    { xsimpl. }
    { xsimpl. } }
  intros m'. simpl. apply triple_hpure. intros ->.
  { applys triple_set. }
Qed.

(* 2021-09-07 23:53 *)
