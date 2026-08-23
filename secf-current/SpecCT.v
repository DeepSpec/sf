(** * SpecCT: Cryptographic Constant-Time and Speculative Constant-Time *)


Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Stdlib Require Import Strings.String.
From SECF Require Import Maps.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Arith.EqNat.
From Stdlib Require Import Arith.PeanoNat. Import Nat.
From Stdlib Require Import Lia.
From Stdlib Require Import List. Import ListNotations.
Set Default Goal Selector "!".
Ltac invert H := inversion H; subst; clear H.

(** This chapter starts by presenting the cryptographic constant-time
    (CCT) discipline, which we statically enforce using a simple type
    system. This static discipline is, however, not enough to protect
    cryptographic programs against speculative execution attacks, like
    Spectre [Kocher et al 2019] (in Bib.v). To secure CCT programs against this more
    powerful attacker model we additionally use a program transformation
    called _Speculative Load Hardening_ (SLH). We prove formally that CCT
    programs protected by SLH achieve speculative constant-time security. *)

(* ################################################################# *)
(** * Cryptographic constant-time *)

(** Cryptographic constant-time (CCT) is a software countermeasure against
    timing side-channel attacks that is widely deployed for cryptographic
    implementations, for instance to prevent leakage of crypto keys
    [Barthe et al 2019] (in Bib.v).

    In the CCT discipline, each program input has to be identified as public or
    secret, and intuitively the execution time of the program should not depend
    on secret inputs, even on processors with instruction and data caches.

    We, however, do not want to explicitly model execution time or caches, since
    - it would be very hard to do right, and
    - it would bring in too many extremely low-level details of the concrete compiler
      (Clang/LLVM 20.1.6) and hardware microarchitecture (Intel Core i7-8650U). *)

(** Instead CCT works with a _more abstract leakage model_,
    which simply assumes that:
    - _all branches the program takes are leaked_;
      - since the path the program takes can greatly
        influence how long execution takes
      - this is exactly like in the Control Flow (CF)
        security model from [StaticIFC]
    - _all accessed memory addresses are leaked_;
      - since timing attacks can also exploit the latency difference between
        hits and misses in the data cache
    - _the operands that influence the timing of variable-time operations
       are leaked_;
      - as an exercise we will add a division operation that leaks both operands.
*)

(** To ensure security against this leakage model, the CCT programming
    discipline requires that:

    - _the control flow of the program does not depend on secrets_;
      - intuitively this prevents the execution time of different program paths
        from directly depending on secrets:

        if Wsecret then ... slow computation ... else skip

    - _the accessed memory addresses do not depend on secrets_;
      - intuitively this prevents secret addresses from leaking into the data cache:

        Vsecret <- AP[Wsecret]

    - _the operands leaked by variable-time operations do not depend on secrets_.
      - this prevents leaking information about secrets e.g., via division:

        Usecret := div Vsecret Wsecret
*)

(** To model memory accesses that depend on secrets we will make the Imp
    language more realistic by adding arrays. *)

(** We need such an extension, since
    otherwise variable accesses in the original Imp map to memory operations at
    constant locations, which thus cannot depend on secrets, so in Imp CCT
    trivially holds for all CF well-typed programs. Array indices on the other
    hand are computed at runtime, which leads to accessing memory addresses that
    can depend on secrets, making CCT non-trivial for Imp with arrays.

    Above we already saw a simple program that is CF secure (since it
    does no branches), but not CCT secure (since it accesses memory
    based on secret information):

        Vsecret <- AP[Wsecret]
*)

(* ================================================================= *)
(** ** Adding constant-time conditional and refactoring expressions *)

(** But first, we add a conditional expression [b ? e1 : e2] that executes in
    constant time (for instance by being compiled to a special constant-time
    conditional move instruction). This constant-time conditional can be used to
    fix some CCT insecure programs as we will see in the exercises. It will also
    be used in our SLH countermeasure later in the chapter. *)

(** Technically, adding such conditionals to Imp arithmetic expressions
    would make them dependent on boolean expressions. But boolean expressions
    are already dependent on arithmetic expressions. *)

(** To avoid making the definitions of arithmetic and boolean expressions
    mutually inductive, we drop boolean expressions altogether and encode them
    using arithmetic expressions. Our encoding of bools in terms of nats is
    similar to that of C, where zero means false, and non-zero means true. *)

(** We also refactor the semantics of binary operators in terms of the
    [binop] enumeration below, to avoid the duplication and redundancy in Imp: *)

Inductive binop : Type :=
  | BinPlus | BinMinus | BinMult | BinEq | BinLe | BinAnd | BinImpl.

(** We define the semantics of [binop]s directly on nats. We are careful to
    allow other representations of true (any non-zero number).  *)

Definition not_zero (n : nat) : bool := negb (n =? 0).
Definition bool_to_nat (b : bool) : nat := if b then 1 else 0.

Definition eval_binop (o:binop) (n1 n2 : nat) : nat :=
  match o with
  | BinPlus => n1 + n2
  | BinMinus => n1 - n2
  | BinMult => n1 * n2
  | BinEq => bool_to_nat (n1 =? n2)
  | BinLe => bool_to_nat (n1 <=? n2)
  | BinAnd => bool_to_nat (not_zero n1 && not_zero n2)
  | BinImpl => bool_to_nat (negb (not_zero n1) || not_zero n2)
  end.

Inductive exp : Type :=
  | ANum (n : nat)
  | AId (x : string)
  | ABin (o : binop) (e1 e2 : exp) (* <--- REFACTORED *)
  | ACTIf (b : exp) (e1 e2 : exp). (* <--- NEW *)

(** The most important fact about constant-time conditionals is that they are
    expressions, so they will not cause any observations. *)

(** We encode all the previous arithmetic and boolean operations: *)

Definition APlus := ABin BinPlus.
Definition AMinus := ABin BinMinus.
Definition AMult := ABin BinMult.
Definition BTrue := ANum 1.
Definition BFalse := ANum 0.
Definition BAnd := ABin BinAnd.
Definition BImpl := ABin BinImpl.
Definition BNot b := BImpl b BFalse.
Definition BOr e1 e2 := BImpl (BNot e1) e2.
Definition BEq := ABin BinEq.
Definition BNeq e1 e2 := BNot (BEq e1 e2).
Definition BLe := ABin BinLe.
Definition BGt e1 e2 := BNot (BLe e1 e2).
Definition BLt e1 e2 := BGt e2 e1.

Hint Unfold eval_binop : core.
Hint Unfold APlus AMinus AMult : core.
Hint Unfold BTrue BFalse : core.
Hint Unfold BAnd BImpl BNot BOr BEq BNeq BLe BGt BLt : core.

(** The notations we use for expressions are the same as in Imp,
    except the notation [be ? e1 : e2] which is new: *)
Definition U : string := "U".
Definition V : string := "V".
Definition W : string := "W".
Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".
Definition AP : string := "AP".
Definition AS : string := "AS".

Coercion AId : string >-> exp.
Coercion ANum : nat >-> exp.

Declare Custom Entry com.
Declare Scope com_scope.

Notation "<{ e }>" := e (at level 0, e custom com at level 99) : com_scope.
Notation "( x )" := x (in custom com, x at level 99) : com_scope.
Notation "x" := x (in custom com at level 0, x constr at level 0) : com_scope.
Notation "f x .. y" := (.. (f x) .. y)
                  (in custom com at level 0, only parsing,
                  f constr at level 0, x constr at level 9,
                  y constr at level 9) : com_scope.
Notation "x + y"   := (APlus x y) (in custom com at level 50, left associativity).
Notation "x - y"   := (AMinus x y) (in custom com at level 50, left associativity).
Notation "x * y"   := (AMult x y) (in custom com at level 40, left associativity).
Notation "'true'"  := true (at level 1).
Notation "'true'"  := BTrue (in custom com at level 0).
Notation "'false'" := false (at level 1).
Notation "'false'" := BFalse (in custom com at level 0).
Notation "x <= y"  := (BLe x y) (in custom com at level 70, no associativity).
Notation "x > y"   := (BGt x y) (in custom com at level 70, no associativity).
Notation "x < y"   := (BLt x y) (in custom com at level 70, no associativity).
Notation "x = y"   := (BEq x y) (in custom com at level 70, no associativity).
Notation "x <> y"  := (BNeq x y) (in custom com at level 70, no associativity).
Notation "x && y"  := (BAnd x y) (in custom com at level 80, left associativity).
Notation "'~' b"   := (BNot b) (in custom com at level 75, right associativity).

Open Scope com_scope.

Notation "be '?' e1 ':' e2"  := (ACTIf be e1 e2) (* <-- NEW *)
                 (in custom com at level 85, no associativity).

(* ================================================================= *)
(** ** Adding arrays *)

(** Now back to adding array loads and stores to commands: *)

Inductive com : Type :=
  | Skip
  | Asgn (x : string) (e : exp)
  | Seq (c1 c2 : com)
  | If (be : exp) (c1 c2 : com)
  | While (be : exp) (c : com)
  | ALoad (x : string) (a : string) (i : exp) (* <--- NEW *)
  | AStore (a : string) (i : exp) (e : exp)  (* <--- NEW *).


Notation "<{{ e }}>" := e (at level 0, e custom com at level 99) : com_scope.
Notation "( x )" := x (in custom com, x at level 99) : com_scope.
Notation "x" := x (in custom com at level 0, x constr at level 0) : com_scope.
Notation "f x .. y" := (.. (f x) .. y)
                  (in custom com at level 0, only parsing,
                  f constr at level 0, x constr at level 9,
                  y constr at level 9) : com_scope.

Open Scope com_scope.

Notation "'skip'"  :=
  Skip (in custom com at level 0) : com_scope.
Notation "x := y"  :=
  (Asgn x y)
    (in custom com at level 0, x constr at level 0,
      y custom com at level 85, no associativity) : com_scope.
Notation "x ; y" :=
  (Seq x y)
    (in custom com at level 90, right associativity) : com_scope.
Notation "'if' x 'then' y 'else' z 'end'" :=
  (If x y z)
    (in custom com at level 89, x custom com at level 99,
     y at level 99, z at level 99) : com_scope.
Notation "'while' x 'do' y 'end'" :=
  (While x y)
    (in custom com at level 89, x custom com at level 99, y at level 99) : com_scope.

Notation "x '<-' a '[' i ']'" := (ALoad x a i) (* <--- NEW *)
     (in custom com at level 0, x constr at level 0,
      a constr at level 0, i custom com at level 85,
      no associativity) : com_scope.
Notation "a '[' i ']'  '<-' e"  := (AStore a i e) (* <--- NEW *)
     (in custom com at level 0, a constr at level 0,
      i custom com at level 85, e custom com at level 85,
         no associativity) : com_scope.

Definition state := total_map nat.
Definition mem := total_map (list nat). (* <--- NEW *)

Fixpoint eval (s : state) (e: exp) : nat :=
  match e with
  | ANum n => n
  | AId x => s x
  | ABin b e1 e2 => eval_binop b (eval s e1) (eval s e2)
  | <{b ? e1 : e2}> => if not_zero (eval s b) then eval s e1
                           (* ^- NEW -> *)    else eval s e2
  end.

(** A couple of obvious lemmas that will be useful in the proofs: *)

Lemma not_zero_eval_S : forall b n s,
  eval s b = S n ->
  not_zero (eval s b) = true.
Proof. intros b n s H. rewrite H. reflexivity. Qed.

Lemma not_zero_eval_O : forall b s,
  eval s b = O ->
  not_zero (eval s b) = false.
Proof. intros b s H. rewrite H. reflexivity. Qed.

(** For array loads we will use the [nth] function from the Rocq library, where
    the last argument is a default for out of bounds accesses (our semantics
    will check to prevent such accesses and will pass [0] as the default): *)

Check nth : forall {A : Type}, nat -> list A -> A -> A.

(** We also define an array update operation, to be used in the semantics of
    array stores below: *)

Fixpoint upd (i:nat) (ns:list nat) (n:nat) : list nat :=
  match i, ns with
  | 0, _ :: ns' => n :: ns'
  | S i', n' :: ns' => n' :: upd i' ns' n
  | _, [] => ns
  end.

(** We introduce familiar-looking notations for reading and updating an array at
    a given index: *)

Notation "ns '.[' i ']'" := (nth i ns 0)
  (at level 2, left associativity, format "ns .[ i ]").
Notation "ns '.[' i '<-' n ']'" := (upd i ns n)
  (at level 2, left associativity, format "ns .[ i  <-  n ]").

(* ================================================================= *)
(** ** Instrumenting semantics with observations *)

(** In addition to the boolean branches, which are observable in the CF security
    model, for CCT security also the array and index of array loads and
    stores are observable: *)

Inductive observation : Type :=
  | OBranch (b : bool)
  | OALoad (a : string) (i : nat)
  | OAStore (a : string) (i : nat).

Definition obs := list observation.

(** Intuitively, variables act like machine registers (accesses not observable),
    while arrays act like the memory (accessed array+index observable). *)

(** We define an instrumented operational semantics producing
    these observations ([os]):

    <(s, m)> =[ c ]=> <(s', m', os)>

    In addition to _states_ ([s]) that assign [nat] values to variables, this
    semantics also has _memories_ ([m]) that assign lists of values to arrays.
*)

(**

          --------------------------------- (CTE_Skip)
          <(s, m)> =[ skip ]=> <(s, m, [])>

                      eval s e = n
      -------------------------------------------- (CTE_Asgn)
      <(s, m)> =[ x := e ]=> <(x !-> n; s, m, [])>

            <(s, m)> =[ c1 ]=> <(s', m', os1)>
            <(s', m')> =[ c2 ]=> <(s'', m'', os2)>
      ------------------------------------------------- (CTE_Seq)
      <(s, m)>  =[ c1 ; c2 ]=> <(s'', m'', os1 ++ os2)>

   let c := if not_zero (eval s be) then c1 else c2 in
        <(s,m)> =[ c ]=> <(s',m',os1)>
 ------------------------------------------------------- (CTE_If)
  <(s, m)> =[ if be then c1 else c2 end]=>
    <(s', m', [OBranch (not_zero (eval s be))] ++ os1)>
*)

(**

  <(s,m)> =[ if be then (c; while be do c end)
                   else skip end ]=> <(s',m',os)>
  ----------------------------------------------- (CTE_While)
    <(s,m)> =[ while be do c end ]=> <(s',m',os)>

       eval s ie = i       i < length (m a)
      --------------------------------------- (CTE_ALoad)
      <(s, m)> =[ x <- a[ie] ]=>
        <(x!->(m a).[i]; s, m, [OALoad a i])>

  eval s e = n     eval s ie = i    i < length (m a)
  -------------------------------------------------- (CTE_AStore)
      <(s, m)> =[ a[ie] <- e ]=>
        <(s, a!->(m a).[i <- n]; m, [OAStore a i])>
*)

(** This semantics uses two tricks to simplify the proofs in this file:
    - We have a single [if] rule (instead of the two ones in Imp) by using a
      Rocq [let] and [if-then-else] in the premise.
    - We have a single [while] rule (instead of the two ones in Imp) by
      evaluating the [while be do c end] in terms of its 1-step unrolling: [[
      if be then (c; while be do c end) else skip end
*)

(** Formally this looks as follows: *)
Reserved Notation
         "'<(' s , m ')>' '=[' c ']=>' '<(' s' , m' , os ')>'"
         (at level 40, c custom com at level 99,
          s constr, m constr, s' constr, m' constr at next level).

Inductive cteval : com -> state -> mem -> state -> mem -> obs -> Prop :=
  | CTE_Skip : forall s m,
      <(s , m)> =[ skip ]=> <(s, m, [])>
  | CTE_Asgn  : forall s m e n x,
      eval s e = n ->
      <(s, m)> =[ x := e ]=> <(x !-> n; s, m, [])>
  | CTE_Seq : forall c1 c2 s m s' m' s'' m'' os1 os2,
      <(s, m)> =[ c1 ]=> <(s', m', os1)>  ->
      <(s', m')> =[ c2 ]=> <(s'', m'', os2)> ->
      <(s, m)>  =[ c1 ; c2 ]=> <(s'', m'', os1++os2)>
  | CTE_If : forall s m s' m' be c1 c2 os1, (* <- Trick; single if rule *)
      let c := if not_zero (eval s be) then c1 else c2 in
      <(s, m)> =[ c ]=> <(s', m', os1)> ->
      <(s, m)> =[ if be then c1 else c2 end]=>
      <(s', m', [OBranch (not_zero (eval s be))] ++ os1)>
  | CTE_While : forall b s m s' m' os c,
      <(s,m)> =[ if b then (c; while b do c end) else skip end ]=>
        <(s', m', os)> -> (* <^- Trick; unroll loop, single while rule *)
      <(s,m)> =[ while b do c end ]=> <(s', m', os)>
  | CTE_ALoad : forall s m x a ie i,
      eval s ie = i ->
      i < length (m a) ->
      <(s, m)> =[ x <- a[ie] ]=> <(x !-> (m a).[i]; s, m, [OALoad a i])>
  | CTE_AStore : forall s m a ie i e n,
      eval s e = n ->
      eval s ie = i ->
      i < length (m a) ->
      <(s, m)> =[ a[ie] <- e ]=> <(s, a !-> (m a).[i <- n]; m, [OAStore a i])>

  where "<( s , m )> =[ c ]=> <( s' , m' , os )>" := (cteval c s m s' m' os).

Hint Constructors cteval : core.

(* ================================================================= *)
(** ** Constant-time security definition *)

(** To define CCT security we first repeat some definitions from
    [Noninterference] and [StaticIFC], generalizing [pub_equiv] so
    that it applies to both states and memories.  *)

(** Note that labels are their own inductive type. Use [l1 =? l2] to compare two
    labels, and lemmas [label_eqb_eq] and [label_eqb_neq] below to reason about
    such comparisons. *)

Inductive label : Type :=
  | public
  | secret.

Definition label_map := total_map label.

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
Definition pub_equiv (L : total_map label) {X:Type} (s1 s2 : total_map X) :=
  forall x:string, L x = public -> s1 x = s2 x.

Lemma pub_equiv_refl :
  forall {X:Type} (L : total_map label) (s : total_map X),
  pub_equiv L s s.
Proof. intros X L s x Hx. reflexivity. Qed.

Lemma pub_equiv_sym :
  forall {X:Type} (L : total_map label) (s1 s2 : total_map X),
  pub_equiv L s1 s2 ->
  pub_equiv L s2 s1.
Proof.
  unfold pub_equiv. intros X L s1 s2 H x Px.
  rewrite H; auto.
Qed.

Lemma pub_equiv_trans :
  forall {X:Type} (L : total_map label) (s1 s2 s3 : total_map X),
  pub_equiv L s1 s2 ->
  pub_equiv L s2 s3 ->
  pub_equiv L s1 s3.
Proof.
  unfold pub_equiv. intros X L s1 s2 s3 H12 H23 x Px.
  rewrite H12; try rewrite H23; auto.
Qed.

Lemma pub_equiv_update_secret :
  forall {X: Type} (L : total_map label) (s1 s2 : total_map X)
         (x: string) (e1 e2: X),
  pub_equiv L s1 s2 ->
  L x = secret ->
  pub_equiv L (x !-> e1; s1) (x !-> e2; s2).
Proof.
  unfold pub_equiv. intros X L s1 s2 x e H Pe Px y Py.
  destruct (String.eqb_spec x y) as [Hxy | Hxy]; subst.
  - rewrite Px in Py. discriminate.
  - repeat rewrite t_update_neq; auto.
Qed.

Lemma pub_equiv_update_public :
  forall {X: Type} (L : total_map label) (s1 s2 : total_map X)
         (x: string) {e1 e2: X},
  pub_equiv L s1 s2 ->
  e1 = e2 ->
  pub_equiv L (x !-> e1; s1) (x !-> e2; s2).
Proof.
  unfold pub_equiv. intros X L s1 s2 x e1 e2 H Eq y Py.
  destruct (String.eqb_spec x y) as [Hxy | Hxy]; subst.
  - repeat rewrite t_update_eq; auto.
  - repeat rewrite t_update_neq; auto.
Qed.

(** A program is CCT secure if what the attacker observes during execution
    does not depend on secrets. We formalize this similarly to CF security: if
    the two initial states agree on the variables that [L] labels public, and
    the two initial memories agree on the arrays that [LA] labels public, then
    both runs have to produce exactly the same observations. *)

Definition cct_secure L LA c :=
  forall s1 s2 m1 m2 s1' s2' m1' m2' os1 os2,
    pub_equiv L s1 s2 ->
    pub_equiv LA m1 m2 ->
    <(s1, m1)> =[ c ]=> <(s1', m1', os1)> ->
    <(s2, m2)> =[ c ]=> <(s2', m2', os2)> ->
    os1 = os2.

(* ================================================================= *)
(** ** Example CF secure program that is not CCT secure *)

(** Assuming that [W] and [V] are secret variables, the following program is
    trivially CF secure, because it does not branch at all.
    But it is not CCT secure. *)

Definition cct_insecure_load :=
   <{{ V <- AP[W] }}> .

(** We prove this below. First, we define the label maps for variables and
    arrays, which we will use in this chapter for such examples: *)

Definition LXYZpub : label_map :=
  (X!-> public; Y!-> public; Z!-> public; __ !-> secret).

Definition LAPpub : label_map :=
  (AP!-> public; __ !-> secret).

(** Then a couple of helper lemmas similar to those in previous chapters: *)

Lemma LXYZpub_public : forall x,
  LXYZpub x = public -> x = X \/ x = Y \/ x = Z.
Proof.
  unfold LXYZpub. intros x Hxyz.
  destruct (String.eqb_spec x X); auto.
  rewrite t_update_neq in Hxyz; auto.
  destruct (String.eqb_spec x Y); auto.
  rewrite t_update_neq in Hxyz; auto.
  destruct (String.eqb_spec x Z); auto.
  rewrite t_update_neq in Hxyz; auto.
  rewrite t_apply_empty in Hxyz. discriminate.
Qed.

Lemma LAPpub_public : forall a, LAPpub a = public -> a = AP.
Proof.
  unfold LAPpub. intros a Ha.
  destruct (String.eqb_spec a AP); auto.
  rewrite t_update_neq in Ha; auto. discriminate Ha.
Qed.

Lemma LXYZpubXYZ : forall x,
  x = X \/ x = Y \/ x = Z -> LXYZpub x = public.
Proof.
  intros x Hx.
  destruct Hx as [HX | HYZ]; subst.
  - reflexivity.
  - destruct HYZ as [HY | HZ]; subst; reflexivity.
Qed.

(** Finally, we can prove semantically that [cct_insecure_load] is CCT-insecure,
    because different [W] values produce different [OALoad] observations: *)

Example cct_insecure_load_is_not_cct_secure :
  ~ (cct_secure LXYZpub LAPpub cct_insecure_load).
Proof.
  unfold cct_secure, cct_insecure_load; intros CTSEC.
  remember (W !-> 1; __ !-> 0) as s1.
  remember (W !-> 2; __ !-> 0) as s2.
  remember (AP !-> [1;2;3]; __ !-> []) as m.
  specialize (CTSEC s1 s2 m m).

  assert (Contra: [OALoad AP 1] = [OALoad AP 2]).
  { eapply CTSEC; subst.
    (* public variables equivalent *)
    - apply pub_equiv_update_secret; auto.
      apply pub_equiv_refl.
    (* public arrays equivalent *)
    - apply pub_equiv_refl.
    - eapply CTE_ALoad; simpl; auto.
    - eapply CTE_ALoad; simpl; auto. }

  discriminate.
Qed.

(** **** Exercise: 2 stars, standard (cct_insecure_store_is_not_cct_secure)

    Show that also the following program is not CCT secure,
    despite the write going to a secret array. *)
Definition cct_insecure_store :=
   <{{ AS[W] <- 42 }}> .

Example cct_insecure_store_is_not_cct_secure :
  ~ (cct_secure LXYZpub LAPpub cct_insecure_store).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ================================================================= *)
(** ** Type system for cryptographic constant-time programming *)

(** In our CCT type system, the label assigned to the result of a constant-time
    conditional expression simply joins the labels of the 3 involved expressions:

        L |- be \in l   L |- e1 \in l1    L |- e2 \in l2
        ------------------------------------------------- (T_CTIf)
             L |- be?e1:e2 \in join l (join l1 l2)

    The rules for the other expressions are standard, and a lot fewer
    because of our refactoring:

            -----------------   (T_Num)
            L |- n \in public

            ----------------   (T_Id)
            L |- X \in (L X)

       L |- e1 \in l1      L |- e2 \in l2
      -----------------------------------   (T_Bin)
       L |- (e1 `op` e2) \in (join l1 l2)
*)

(** We again bring in some definitions from [StaticIFC] that we use in the
    formalization below. *)

Definition join (l1 l2 : label) : label :=
  match l1 with
  | public => l2
  | secret => secret
  end.

Lemma join_public : forall {l1 l2},
  join l1 l2 = public -> l1 = public /\ l2 = public.
Proof. intros [|] [|] H; try discriminate H; auto. Qed.

Lemma join_public_l : forall {l},
  join public l = l.
Proof. reflexivity. Qed.

Definition can_flow (l1 l2 : label) : bool :=
  match l1, l2 with
  | secret, public => false
  | _, _ => true
  end.

Lemma can_flow_secret_l : forall {l},
  can_flow secret l = true -> l = secret.
Proof.
  intros l H. destruct l.
  - discriminate H.
  - reflexivity.
Qed.

Lemma can_flow_true_iff : forall {l1 l2},
  can_flow l1 l2 = true <-> l1 = public \/ l2 = secret.
Proof.
  intros l1 l2. split.
  - intros H. destruct l1.
    + left. reflexivity.
    + right. destruct l2.
      * discriminate H.
      * reflexivity.
  - intros [H | H]; subst.
    + reflexivity.
    + destruct l1; reflexivity.
Qed.

(** Formally the label assignment judgement looks as follows: *)

Reserved Notation "L '|-' a \in l" (at level 40).

Inductive exp_has_label (L:label_map) : exp -> label -> Prop :=
  | T_Num : forall n,
       L |- (ANum n) \in public
  | T_Id : forall X,
       L |- (AId X) \in (L X)
  | T_Bin : forall op e1 l1 e2 l2,
       L |- e1 \in l1 ->
       L |- e2 \in l2 ->
       L |- (ABin op e1 e2) \in (join l1 l2)
  | T_CTIf : forall be l e1 l1 e2 l2,
       L |- be \in l ->
       L |- e1 \in l1 ->
       L |- e2 \in l2 ->
       L |- <{ be ? e1 : e2 }> \in (join l (join l1 l2))

where "L '|-' e '\in' l" := (exp_has_label L e l).

Hint Constructors exp_has_label : core.

(** Our refactoring gives us a single noninterference theorem for expressions: *)

Theorem noninterferent_exp : forall {L s1 s2 e},
  pub_equiv L s1 s2 ->
  L |- e \in public ->
  eval s1 e = eval s2 e.
Proof.
  intros L s1 s2 e Heq Ht. remember public as l.
  generalize dependent Heql.
  induction Ht; simpl; intros.
  - reflexivity.
  - eapply Heq; auto.
  - eapply join_public in Heql.
    destruct Heql as [HP1 HP2]. subst.
    rewrite IHHt1, IHHt2; reflexivity.
  - eapply join_public in Heql.
    destruct Heql as [HP HP']. subst.
    eapply join_public in HP'.
    destruct HP' as [HP1 HP2]. subst.
    rewrite IHHt1, IHHt2, IHHt3; reflexivity.
Qed.

(** All rules for commands are the same as for [cf_well_typed] (from
    [StaticIFC]), except [CCT_ALoad] and [CCT_AStore], which are new. *)

(**
                         ------------------                 (CCT_Skip)
                         L ;; LA |-ct- skip

             L |- e \in l    can_flow l (L X) = true
             -----------------------------------------      (CCT_Asgn)
                       L ;; LA |-ct- X := e

               L ;; LA |-ct- c1    L ;; LA |-ct- c2
               ------------------------------------          (CCT_Seq)
                       L ;; LA |-ct- c1;c2
*)
(**
  L |- be \in public    L ;; LA |-ct- c1    L ;; LA |-ct- c2
  ---------------------------------------------------------- (CCT_If)
             L ;; LA |-ct- if be then c1 else c2 end

                L |- be \in public    L ;; LA |-ct- c
                -------------------------------------       (CCT_While)
                  L ;; LA |-ct- while be do c end

      L |- i \in public   can_flow (LA a) (L x) = true
      --------------------------------------------------   (CCT_ALoad)
                  L ;; LA |-ct- x <- a[i]

L |- i \in public   L |- e \in l   can_flow l (LA a) = true
--------------------------------------------------------------- (CCT_AStore)
                   L ;; LA |-ct- a[i] <- e
*)

(** Formally this looks as follows: *)
Reserved Notation "L ';;' LA '|-ct-' c" (at level 40).

Inductive cct_well_typed (L LA:label_map) : com -> Prop :=
  | CCT_Skip :
      L ;; LA |-ct- <{{ skip }}>
  | CCT_Asgn : forall X e l,
      L |- e \in l ->
      can_flow l (L X) = true ->
      L ;; LA |-ct- <{{ X := e }}>
  | CCT_Seq : forall c1 c2,
      L ;; LA |-ct- c1 ->
      L ;; LA |-ct- c2 ->
      L ;; LA |-ct- <{{ c1 ; c2 }}>
  | CCT_If : forall b c1 c2,
      L |- b \in public ->
      L ;; LA |-ct- c1 ->
      L ;; LA |-ct- c2 ->
      L ;; LA |-ct- <{{ if b then c1 else c2 end }}>
  | CCT_While : forall b c1,
      L |- b \in public ->
      L ;; LA |-ct- c1 ->
      L ;; LA |-ct- <{{ while b do c1 end }}>
  | CCT_ALoad : forall x a i,
      L |- i \in public ->
      can_flow (LA a) (L x) = true ->
      L ;; LA |-ct- <{{ x <- a[i] }}>
  | CCT_AStore : forall a i e l,
      L |- i \in public ->
      L |- e \in l ->
      can_flow l (LA a) = true ->
      L ;; LA |-ct- <{{ a[i] <- e }}>

where "L ;; LA '|-ct-' c" := (cct_well_typed L LA c).

Hint Constructors cct_well_typed : core.

(* ================================================================= *)
(** ** CCT type-checker *)

(** We also define a type-checker for the CCT type system above, following the
    recipe from [StaticIFC]. Expressions are straightforward to label: *)

Fixpoint label_of_exp (L:label_map) (e:exp) : label :=
  match e with
  | ANum n => public
  | AId X => L X
  | ABin _ e1 e2 =>  join (label_of_exp L e1) (label_of_exp L e2)
  | <{ be ? e1 : e2 }> => join (label_of_exp L be)
                               (join (label_of_exp L e1)
                                     (label_of_exp L e2))
  end.

Lemma label_of_exp_sound : forall L e,
  L |- e \in label_of_exp L e.
Proof.
  intros L e. induction e; constructor; eauto. Qed.

Lemma label_of_exp_unique : forall L e l,
  L |- e \in l ->
  l = label_of_exp L e.
Proof.
  intros L e l H.
  induction H; simpl in *; subst; auto.
Qed.

(** For commands, the only new cases are the two array operations, which check
    that the index expression is public and that values flow correctly with
    respect to the label [LA a] of the array. *)

Fixpoint cct_typechecker (L LA:label_map) (c:com) : bool :=
  match c with
  | <{{ skip }}> => true
  | <{{ X := e }}> => can_flow (label_of_exp L e) (L X)
  | <{{ c1 ; c2 }}> => cct_typechecker L LA c1 && cct_typechecker L LA c2
  | <{{ if b then c1 else c2 end }}> =>
      (label_of_exp L b =? public) &&
      cct_typechecker L LA c1 && cct_typechecker L LA c2
  | <{{ while b do c1 end }}> =>
      (label_of_exp L b =? public) && cct_typechecker L LA c1
  | <{{ X <- a[i] }}> => (label_of_exp L i =? public) &&
                           can_flow (LA a) (L X)
  | <{{ a[i] <- e }}> => (label_of_exp L i =? public) &&
                         can_flow (label_of_exp L e) (LA a)
  end.

Theorem cct_typechecker_sound : forall L LA c,
  cct_typechecker L LA c = true ->
  L ;; LA |-ct- c.
Proof.
  intros L LA c. induction c; simpl in *; econstructor;
    try rewrite andb_true_iff in *; try tauto;
    eauto using label_of_exp_sound.
  - destruct H as [H1 H2].
    rewrite andb_true_iff in H1; try tauto.
    destruct H1 as [H11 H12]. apply label_eqb_eq in H11.
    rewrite <- H11. apply label_of_exp_sound.
  - destruct H as [H1 H2]. rewrite andb_true_iff in H1; tauto.
  - destruct H as [H1 H2]. apply label_eqb_eq in H1.
    rewrite <- H1. apply label_of_exp_sound.
  - destruct H as [H1 H2]. apply label_eqb_eq in H1.
    rewrite <- H1. eapply label_of_exp_sound.
  - destruct H as [H1 H2]. apply label_eqb_eq in H1.
    rewrite <- H1. eapply label_of_exp_sound.
  - destruct H as [H1 H2]. auto.
Qed.

Theorem cct_typechecker_complete : forall L LA c,
  cct_typechecker L LA c = false ->
  ~ (L ;; LA |-ct- c).
Proof.
  intros L LA c H Hc. induction Hc; simpl in *;
    try rewrite andb_false_iff in *;
    try tauto; try congruence.
  - apply label_of_exp_unique in H0.
    subst. congruence.
  - destruct H; eauto. rewrite andb_false_iff in H.
    destruct H; eauto. rewrite label_eqb_neq in H.
    apply label_of_exp_unique in H0. congruence.
  - destruct H; eauto. rewrite label_eqb_neq in H.
    apply label_of_exp_unique in H0. congruence.
  - destruct H; eauto; try congruence.
    rewrite label_eqb_neq in H.
    apply label_of_exp_unique in H0. congruence.
  - destruct H; eauto.
    + rewrite label_eqb_neq in H.
      apply label_of_exp_unique in H0. congruence.
    + apply label_of_exp_unique in H1.
      subst. congruence.
Qed.

(** Finally, we use the type-checker to show that the [cct_insecure_load] and
    [cct_insecure_store] examples above are ill-typed. *)

Print LXYZpub. (* [[
= (X!-> public; Y!-> public; Z!-> public; __ !-> secret) ]]
*)
Print cct_insecure_load. (* [[
= <{{ V <- AP[W] }}> ]]
*)
Print cct_insecure_store. (* [[
= <{{ AS[W] <- 42 }}> ]]
*)

Theorem cct_insecure_load_ill_typed :
  ~(LXYZpub ;; LAPpub |-ct- cct_insecure_load).
Proof. apply cct_typechecker_complete. reflexivity. Qed.

Theorem cct_insecure_store_ill_typed :
  ~(LXYZpub ;; LAPpub |-ct- cct_insecure_store).
Proof. apply cct_typechecker_complete. reflexivity. Qed.

(* ================================================================= *)
(** ** Noninterference lemma *)

(** To prove the security of our type system, we first show it ensures
    noninterference, which is not that hard, given that branching on secrets is
    completely disallowed. *)

Lemma cct_well_typed_noninterferent :
  forall L LA c s1 s2 m1 m2 s1' s2' m1' m2' os1 os2,
  L ;; LA |-ct- c ->
  pub_equiv L s1 s2 ->
  pub_equiv LA m1 m2 ->
  <(s1, m1)> =[ c ]=> <(s1', m1', os1)> ->
  <(s2, m2)> =[ c ]=> <(s2', m2', os2)> ->
  pub_equiv L s1' s2' /\ pub_equiv LA m1' m2'.
Proof.
  intros L LA c s1 s2 m1 m2 s1' s2' m1' m2' os1 os2
    Hwt Heq Haeq Heval1 Heval2.
  generalize dependent s2'. generalize dependent s2.
  generalize dependent m2'. generalize dependent m2.
  generalize dependent os2.
  induction Heval1;
    intros os2' m2 Haeq m2' s2 Heq s2' Heval2;
    inversion Heval2; inversion Hwt; subst.
  (* Most cases are similar as for [cf_well_typed] *)
  - split; auto.
  - split; auto. destruct l.
    + rewrite (noninterferent_exp Heq H10).
      eapply pub_equiv_update_public; auto.
    + apply can_flow_secret_l in H11.
      eapply pub_equiv_update_secret; auto.
  - edestruct IHHeval1_2; eauto.
    + eapply IHHeval1_1; eauto.
    + eapply IHHeval1_1; eauto.
  - eapply IHHeval1; eauto.
    + subst c. destruct (eval s be); simpl; auto.
    + subst c c4.
      rewrite (noninterferent_exp Heq H11); eauto.
  - eapply IHHeval1; eauto.
  - (* NEW CASE: ALoad *)
    split; eauto.
    erewrite noninterferent_exp; eauto.
    destruct (LA a) eqn:LAa.
    + eapply pub_equiv_update_public; auto.
      eapply Haeq in LAa. rewrite LAa. reflexivity.
    + apply can_flow_secret_l in H15.
      eapply pub_equiv_update_secret; auto.
  - (* NEW CASE: AStore *)
    split; eauto.
    destruct (LA a) eqn:LAa; simpl in *.
    + eapply Haeq in LAa. rewrite LAa.
      destruct l; [|discriminate].
      eapply pub_equiv_update_public; auto.
      repeat erewrite (noninterferent_exp Heq); auto.
    + eapply pub_equiv_update_secret; auto.
Qed.

(** The proof above closely follows [cf_well_typed_noninterferent], with
    extra cases for the array operations. For array stores we show that the
    memories stay publicly equivalent. *)

(* ================================================================= *)
(** ** Theorem: cryptographic constant-time security by typing *)

Print cct_secure. (* [[
= fun L LA c =>
    forall s1 s2 m1 m2 s1' s2' m1' m2' os1 os2,
      pub_equiv L s1 s2 ->
      pub_equiv LA m1 m2 ->
      <(s1, m1)> =[ c ]=> <(s1', m1', os1)> ->
      <(s2, m2)> =[ c ]=> <(s2', m2', os2)> ->
      os1 = os2. ]]
*)

Theorem cct_well_typed_secure : forall L LA c,
  L ;; LA |-ct- c ->
  cct_secure L LA c.
Proof.
  unfold cct_secure.
  intros L LA c Hwt s1 s2 m1 m2 s1' s2' m1' m2' os1 os2
    Heq Haeq Heval1 Heval2.
  generalize dependent s2'. generalize dependent s2.
  generalize dependent m2'. generalize dependent m2.
  generalize dependent os2.
  induction Heval1; intros os2' a2 Haeq a2' s2 Heq s2' Heval2;
    inversion Heval2; inversion Hwt; subst.
  - reflexivity.
  - reflexivity.
  - erewrite IHHeval1_2; [erewrite IHHeval1_1 | | | |];
      try reflexivity; try eassumption.
    + eapply cct_well_typed_noninterferent with (c:=c1); eauto.
    + eapply cct_well_typed_noninterferent with (c:=c1); eauto.
  - rewrite (noninterferent_exp Heq H11).
    f_equal; auto. eapply IHHeval1; eauto.
    + subst c. destruct (eval s be); simpl; auto.
    + subst c c4.
      rewrite (noninterferent_exp Heq H11); eauto.
  - eapply IHHeval1; eauto.
  - (* NEW CASE: ALoad *)
    f_equal. f_equal. eapply noninterferent_exp; eassumption.
  - (* NEW CASE: AStore *)
    f_equal. f_equal. eapply noninterferent_exp; eassumption.
Qed.

(** Most proof cases are similar to the security proof for [cf_well_typed] from
    [StaticIFC]. In particular, [noninterference] is used to prove the
    sequence case in both proofs.

    The only new cases here are for array operations, and they follow
    immediately from [noninterferent_exp], since the CCT type system requires
    array indices to be public.

    So everything we've done for CCT security---the instrumented semantics, the
    type system, and its security proof---is just a simple and natural extension
    of what we did for CF security, which was itself simple. *)

(** Yet this simple type system provides a formalization of the CCT programming
    discipline, which is widely used in practice. *)

(** The type system of this chapter can also be seen as a simplified
    version of the constant-time checker [Shivakumar et al 2022] (in Bib.v)
    implemented by the Jasmin language for high-assurance cryptography
    [Jasmin] (in Bib.v): there too, branch conditions and array indices must be
    public, and operators get the join of their arguments' labels. The main
    difference is that Jasmin's type system is _flow-sensitive_: variables do
    not have fixed labels; instead each assignment changes the label of the
    assigned variable to the label of the assigned expression. Jasmin's type
    system additionally supports declassification, label inference, and functions.
    Their type system also has a variant [Shivakumar et al 2023b] (in Bib.v) enforcing
    speculative constant-time for code manually hardened with SLH, a property we
    study later in this chapter for automatically SLH-hardened code. *)

(* ================================================================= *)
(** ** Exercises: Fixing CCT violations *)

(** The type-checker _detects_ CCT violations, but often we can also
    _fix_ the insecure programs: the constant-time conditional
    [be ? e1 : e2] lets us turn secret-dependent control flow and
    memory accesses into secret-dependent _data flow_, which produces
    no observations at all. *)

(** Consider first the following program, which branches on the secret
    variable [W]: *)

Definition cct_insecure_branch : com :=
  <{{ if W = 0 then V := 42 else skip end }}>.

(** This program is not CCT secure: the branching immediately leaks
    the secret condition [W = 0] to the attacker via the [OBranch]
    observation. Accordingly, the type-checker rejects this program: *)

Theorem cct_insecure_branch_ill_typed :
  ~(LXYZpub ;; LAPpub |-ct- cct_insecure_branch).
Proof. apply cct_typechecker_complete. reflexivity. Qed.

(** **** Exercise: 3 stars, standard (fixing_cct_insecure_branch)

    Fix this program: define a functionally equivalent program that does not
    branch on the secret, by instead assigning to [V] a constant-time
    conditional expression. *)

Definition cct_fixed_branch : com
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

(** Show that your program is accepted by the type-checker: *)

Lemma cct_fixed_branch_well_typed :
  cct_typechecker LXYZpub LAPpub cct_fixed_branch = true.
Proof.
  (* FILL IN HERE *) Admitted.

(** Security then follows for free from the soundness of the
    type-checker and our security theorem: *)

Corollary cct_fixed_branch_secure :
  cct_secure LXYZpub LAPpub cct_fixed_branch.
Proof.
  apply cct_well_typed_secure. apply cct_typechecker_sound.
  apply cct_fixed_branch_well_typed.
Qed.

(** Also prove that your program is functionally equivalent to the
    insecure one: it reaches the same final state and memory (only
    the observations can differ between the two programs). *)

Lemma cct_fixed_branch_equiv : forall s m s' m' os,
  <(s, m)> =[ cct_insecure_branch ]=> <(s', m', os)> ->
  exists os', <(s, m)> =[ cct_fixed_branch ]=> <(s', m', os')>.
Proof.
  (* FILL IN HERE *) Admitted.

(** Note that only the _combination_ of these two properties
    guarantees that your program is a correct fix, so you need both to
    get the points for this exercise. *)

Lemma cct_fixed_branch_spec :
  cct_typechecker LXYZpub LAPpub cct_fixed_branch = true /\
  (forall s m s' m' os,
    <(s, m)> =[ cct_insecure_branch ]=> <(s', m', os)> ->
    exists os', <(s, m)> =[ cct_fixed_branch ]=> <(s', m', os')>).
Proof.
  split.
  - apply cct_fixed_branch_well_typed.
  - apply cct_fixed_branch_equiv.
Qed.
(** [] *)

(** **** Exercise: 4 stars, advanced (fixing_cct_insecure_load)

    Recall [cct_insecure_load], which loads from the public array [AP] at a
    _secret_ index [W], leaking the index via the [OALoad] observation: *)

Print cct_insecure_load. (* [[
= <{{ V <- AP[W] }}> ]]
*)

(** Also this program can be fixed by loading from _all_ the locations of the
    array using public indices, and then selecting the right value using
    constant-time conditionals. *)

(** Define a fixed version of [cct_insecure_load], assuming for simplicity that
    the array [AP] has size 2, so that the secret index [W] is either 0 or 1.
    Since our expressions cannot read arrays, use public variables [X] and [Y]
    as temporaries holding the results of the array loads. *)

Definition cct_fixed_load : com
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

(** Show that your program is accepted by the type-checker: *)

Lemma cct_fixed_load_well_typed :
  cct_typechecker LXYZpub LAPpub cct_fixed_load = true.
Proof.
  (* FILL IN HERE *) Admitted.

(** Finally, prove that your program computes the same value for [V]
    as [cct_insecure_load], provided the array [AP] has indeed
    exactly two elements. Your program is allowed to change the
    temporaries [X] and [Y] and to produce different observations,
    but it has to leave the array memory unchanged.

    Hints:
    - Start by inverting the evaluation of [cct_insecure_load];
      among other things this tells you that the secret index [s W]
      is within the bounds of the array.
    - To compute with state lookups and updates of concrete
      variables, you can use [unfold t_update] followed by [simpl].
    - Finally, case analyze the possible values of the secret index
      [s W], which can only be [0] or [1] since it is within bounds. *)

Lemma cct_fixed_load_correct : forall s m a0 a1 s' os,
  m AP = [a0; a1] ->
  <(s, m)> =[ cct_insecure_load ]=> <(s', m, os)> ->
  exists s'' os',
    <(s, m)> =[ cct_fixed_load ]=> <(s'', m, os')> /\
    s'' V = s' V.
Proof.
  (* FILL IN HERE *) Admitted.

(** Again, only the conjunction of the two properties above guarantees
    that your program is a correct fix to get you the points: *)

Lemma cct_fixed_load_spec :
  cct_typechecker LXYZpub LAPpub cct_fixed_load = true /\
  (forall s m a0 a1 s' os,
    m AP = [a0; a1] ->
    <(s, m)> =[ cct_insecure_load ]=> <(s', m, os)> ->
    exists s'' os',
      <(s, m)> =[ cct_fixed_load ]=> <(s'', m, os')> /\
      s'' V = s' V).
Proof.
  split.
  - apply cct_fixed_load_well_typed.
  - apply cct_fixed_load_correct.
Qed.
(** [] *)

(** The exercise above explained the basic idea behind constant-time array
    lookups in cryptographic implementations. For large arrays such as AES's
    S-box, however, scanning every entry is too slow, so real implementations
    either vectorize the scan (using SIMD instructions) or avoid secret-indexed
    array accesses altogether (e.g. bitsliced or hardware AES). *)

(** **** Exercise: 4 stars, advanced, optional (fixing_cct_insecure_store)

    Recall [cct_insecure_store], which stores to a _secret_ index [W] of the
    secret array [AS], leaking the index via the [OAStore] observation: *)

Print cct_insecure_store. (* [[
= <{{ AS[W] <- 42 }}> ]]
*)

(** This program can also be fixed, but the fix is a bit more involved than for
    [cct_insecure_load]. Since a store must leave the _other_ array cells
    unchanged, and our expressions cannot read arrays, we first _load_ every
    cell into a temporary, and then store back to _all_ cells using public
    indices, writing the new value only at the target cell (selected with a
    constant-time conditional). Note that the temporaries have to be _secret_
    variables, since we are loading from the secret array [AS]. *)

(** Define such a fixed program, again assuming [AS] has size 2. You can use the
    secret variables [U] and [V] as temporaries. *)

Definition cct_fixed_store : com
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

(** Show that your program is accepted by the type-checker: *)

Lemma cct_fixed_store_well_typed :
  cct_typechecker LXYZpub LAPpub cct_fixed_store = true.
Proof.
  (* FILL IN HERE *) Admitted.

(** Finally, prove that your program updates the array [AS] the same way
    as [cct_insecure_store], provided [AS] has exactly two elements. This
    time the store leaves the state unchanged but modifies the memory, so
    (dually to [cct_fixed_load]) your program is allowed to change the
    temporaries and to produce different observations, as long as the
    array [AS] ends up the same.

    This proof is very similar to the one for [cct_fixed_load_correct]
    above, so if needed have a look at the hints there. *)

Lemma cct_fixed_store_correct : forall s m a0 a1 s' m' os,
  m AS = [a0; a1] ->
  <(s, m)> =[ cct_insecure_store ]=> <(s', m', os)> ->
  exists s'' m'' os',
    <(s, m)> =[ cct_fixed_store ]=> <(s'', m'', os')> /\
    m'' AS = m' AS.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** Storing at a secret index comes up less often in cryptographic code. When it
    does, the fix from the exercise above would prevent leaking the index,
    though this is even more expensive than the fix for loads. *)

(* ================================================================= *)
(** ** Exercise: Adding division (non-constant-time operation) *)

(** The CCT discipline also prevents passing secrets to operations that are not
    constant time. For instance, division often takes time that depends on the
    values of the two operands. Much like long division on paper, the hardware
    produces the quotient one digit at a time, so a division whose quotient has
    more digits usually takes longer. In this exercise we will add a new
    [x := e1 div e2] command for division, add corresponding evaluation and
    typing rules, and extend the security proofs with the new division case. *)

Module Div.

Inductive com : Type :=
| Skip
| Asgn (x : string) (e : exp)
| Seq (c1 c2 : com)
| If (be : exp) (c1 c2 : com)
| While (be : exp) (c : com)
| ALoad (x : string) (a : string) (i : exp)
| AStore (a : string) (i : exp) (e : exp)
| Div (x: string) (e1 e2: exp). (* <--- NEW *)

Open Scope com_scope.

(** Notations for the old commands are the same as before: *)
Notation "'skip'"  :=
  Skip (in custom com at level 0) : com_scope.
Notation "x := y"  :=
  (Asgn x y)
    (in custom com at level 0, x constr at level 0,
      y custom com at level 85, no associativity) : com_scope.
Notation "x ; y" :=
  (Seq x y)
    (in custom com at level 90, right associativity) : com_scope.
Notation "'if' x 'then' y 'else' z 'end'" :=
  (If x y z)
    (in custom com at level 89, x custom com at level 99,
     y at level 99, z at level 99) : com_scope.
Notation "'while' x 'do' y 'end'" :=
  (While x y)
    (in custom com at level 89, x custom com at level 99, y at level 99) : com_scope.
Notation "x '<-' a '[' i ']'" := (ALoad x a i)
     (in custom com at level 0, x constr at level 0,
      a constr at level 0, i custom com at level 85,
      no associativity) : com_scope.
Notation "a '[' i ']'  '<-' e"  := (AStore a i e)
     (in custom com at level 0, a constr at level 0,
      i custom com at level 85, e custom com at level 85,
         no associativity) : com_scope.

(** Notation for division: *)
Notation "x := y 'div' z" := (* <--- NEW *)
  (Div x y z)
    (in custom com at level 0, x constr at level 0,
        y custom com at level 85, z custom com at level 85,
        no associativity) : com_scope.

Inductive observation : Type :=
| OBranch (b : bool)
| OALoad (a : string) (i : nat)
| OAStore (a : string) (i : nat)
| ODiv (n1 n2: nat). (* <--- NEW *)

Definition obs := list observation.

(** We add a new rule to the big-step operational semantics that produces an
    [ODiv] observation:

               eval s e1 = n1     eval s e2 = n2
------------------------------------------------------------------ (CTE_Div)
<(s,m)> =[x := e1 div e2]=> <(x!->(n1/n2);s,m,[ODiv n1 n2])>

   Formally this looks as follows, where only the last rule is new:
*)

Reserved Notation
         "'<(' s , m ')>' '=[' c ']=>' '<(' s' , m' , os ')>'"
         (at level 40, c custom com at level 99,
          s constr, m constr, s' constr, m' constr at next level).

Inductive cteval : com -> state -> mem -> state -> mem -> obs -> Prop :=
  | CTE_Skip : forall s m,
      <(s , m)> =[ skip ]=> <(s, m, [])>
  | CTE_Asgn  : forall s m e n x,
      eval s e = n ->
      <(s, m)> =[ x := e ]=> <(x !-> n; s, m, [])>
  | CTE_Seq : forall c1 c2 s m s' m' s'' m'' os1 os2,
      <(s, m)> =[ c1 ]=> <(s', m', os1)>  ->
      <(s', m')> =[ c2 ]=> <(s'', m'', os2)> ->
      <(s, m)>  =[ c1 ; c2 ]=> <(s'', m'', os1++os2)>
  | CTE_If : forall s m s' m' be c1 c2 os1,
      let c := if not_zero (eval s be) then c1 else c2 in
      <(s, m)> =[ c ]=> <(s', m', os1)> ->
      <(s, m)> =[ if be then c1 else c2 end]=>
      <(s', m', [OBranch (not_zero (eval s be))] ++ os1)>
  | CTE_While : forall b s m s' m' os c,
      <(s,m)> =[ if b then (c; while b do c end) else skip end ]=>
        <(s', m', os)> ->
      <(s,m)> =[ while b do c end ]=> <(s', m', os)>
  | CTE_ALoad : forall s m x a ie i,
      eval s ie = i ->
      i < length (m a) ->
      <(s, m)> =[ x <- a[ie] ]=> <(x !-> (m a).[i]; s, m, [OALoad a i])>
  | CTE_AStore : forall s m a ie i e n,
      eval s e = n ->
      eval s ie = i ->
      i < length (m a) ->
      <(s, m)> =[ a[ie] <- e ]=> <(s, a !-> (m a).[i <- n]; m, [OAStore a i])>
  | CTE_Div : forall s m e1 n1 e2 n2 x, (* <--- NEW *)
      eval s e1 = n1 ->
      eval s e2 = n2 ->
      <(s, m)> =[ x := e1 div e2  ]=> <(x !-> (n1 / n2)%nat; s, m, [ODiv n1 n2] )>

  where "<( s , m )> =[ c ]=> <( s' , m' , os )>" := (cteval c s m s' m' os).

Hint Constructors cteval : core.

(** **** Exercise: 1 star, standard (cct_well_typed_div)

    Add a new typing rule for division to [cct_well_typed] below.
    Your rule should prevent leaking secret division operands via observations. *)

Reserved Notation "L ';;' LA '|-ct-' c" (at level 40).

Inductive cct_well_typed (L LA:label_map) : com -> Prop :=
  | CCT_Skip :
      L ;; LA |-ct- <{{ skip }}>
  | CCT_Asgn : forall X e l,
      L |- e \in l ->
      can_flow l (L X) = true ->
      L ;; LA |-ct- <{{ X := e }}>
  | CCT_Seq : forall c1 c2,
      L ;; LA |-ct- c1 ->
      L ;; LA |-ct- c2 ->
      L ;; LA |-ct- <{{ c1 ; c2 }}>
  | CCT_If : forall b c1 c2,
      L |- b \in public ->
      L ;; LA |-ct- c1 ->
      L ;; LA |-ct- c2 ->
      L ;; LA |-ct- <{{ if b then c1 else c2 end }}>
  | CCT_While : forall b c1,
      L |- b \in public ->
      L ;; LA |-ct- c1 ->
      L ;; LA |-ct- <{{ while b do c1 end }}>
  | CCT_ALoad : forall x a i,
      L |- i \in public ->
      can_flow (LA a) (L x) = true ->
      L ;; LA |-ct- <{{ x <- a[i] }}>
  | CCT_AStore : forall a i e l,
      L |- i \in public ->
      L |- e \in l ->
      can_flow l (LA a) = true ->
      L ;; LA |-ct- <{{ a[i] <- e }}>
(* FILL IN HERE *)
   (* <--- Add your new typing rule here *)
  where "L ;; LA '|-ct-' c" := (cct_well_typed L LA c).
(* Do not modify the following line: *)
Definition manual_grade_for_cct_well_typed_div : option (nat*string) := None.
(** [] *)

Hint Constructors cct_well_typed : core.

(** **** Exercise: 2 stars, standard (cct_well_typed_div_noninterferent)

    Extend the typing implies noninterference proof to the [div] case. *)

Theorem cct_well_typed_div_noninterferent :
  forall L LA c s1 s2 m1 m2 s1' s2' m1' m2' os1 os2,
  L ;; LA |-ct- c ->
  pub_equiv L s1 s2 ->
  pub_equiv LA m1 m2 ->
  <(s1, m1)> =[ c ]=> <(s1', m1', os1)> ->
  <(s2, m2)> =[ c ]=> <(s2', m2', os2)> ->
  pub_equiv L s1' s2' /\ pub_equiv LA m1' m2'.
Proof.
  intros L LA c s1 s2 m1 m2 s1' s2' m1' m2' os1 os2
    Hwt Heq Haeq Heval1 Heval2.
  generalize dependent s2'. generalize dependent s2.
  generalize dependent m2'. generalize dependent m2.
  generalize dependent os2.
  induction Heval1;
    intros os2' m2 Haeq m2' s2 Heq s2' Heval2;
    inversion Heval2; inversion Hwt; subst.
  - split; auto.
  - split; auto. destruct l.
    + rewrite (noninterferent_exp Heq H10).
      eapply pub_equiv_update_public; auto.
    + apply can_flow_secret_l in H11.
      eapply pub_equiv_update_secret; auto.
  - edestruct IHHeval1_2; eauto.
    + eapply IHHeval1_1; eauto.
    + eapply IHHeval1_1; eauto.
  - eapply IHHeval1; eauto.
    + subst c. destruct (eval s be); simpl; auto.
    + subst c c4.
      rewrite (noninterferent_exp Heq H11); eauto.
  - eapply IHHeval1; eauto.
  - split; eauto.
    erewrite noninterferent_exp; eauto.
    destruct (LA a) eqn:LAa.
    + eapply pub_equiv_update_public; auto.
      eapply Haeq in LAa. rewrite LAa. reflexivity.
    + apply can_flow_secret_l in H15.
      eapply pub_equiv_update_secret; auto.
  - split; eauto.
    destruct (LA a) eqn:LAa; simpl in *.
    + eapply Haeq in LAa. rewrite LAa.
      destruct l; [|discriminate].
      eapply pub_equiv_update_public; auto.
      repeat erewrite (noninterferent_exp Heq); auto.
    + eapply pub_equiv_update_secret; auto.
(* FILL IN HERE *) Admitted.
(** [] *)

(** We need to redefine [cct_secure] for our new command definition *)
Definition cct_secure L LA c :=
  forall s1 s2 m1 m2 s1' s2' m1' m2' os1 os2,
    pub_equiv L s1 s2 ->
    pub_equiv LA m1 m2 ->
    <(s1, m1)> =[ c ]=> <(s1', m1', os1)> ->
    <(s2, m2)> =[ c ]=> <(s2', m2', os2)> ->
    os1 = os2.

(** **** Exercise: 2 stars, standard (cct_well_typed_div_secure)

    Reprove CCT security of the type system. Hint: If this proof doesn't go
    through easily, you may need to go back and fix your div rule. *)
Theorem cct_well_typed_div_secure : forall L LA c,
  L ;; LA |-ct- c ->
  cct_secure L LA c.
Proof.
  unfold cct_secure.
  intros L LA c Hwt s1 s2 m1 m2 s1' s2' m1' m2' os1 os2
    Heq Haeq Heval1 Heval2.
  generalize dependent s2'. generalize dependent s2.
  generalize dependent m2'. generalize dependent m2.
  generalize dependent os2.
  induction Heval1; intros os2' a2 Haeq a2' s2 Heq s2' Heval2;
    inversion Heval2; inversion Hwt; subst.
  - reflexivity.
  - reflexivity.
  - erewrite IHHeval1_2; [erewrite IHHeval1_1 | | | |];
      try reflexivity; try eassumption.
    + eapply cct_well_typed_div_noninterferent with (c:=c1); eauto.
    + eapply cct_well_typed_div_noninterferent with (c:=c1); eauto.
  - rewrite (noninterferent_exp Heq H11).
    f_equal; auto. eapply IHHeval1; eauto.
    + subst c. destruct (eval s be); simpl; auto.
    + subst c c4.
      rewrite (noninterferent_exp Heq H11); eauto.
  - eapply IHHeval1; eauto.
  - f_equal. f_equal. eapply noninterferent_exp; eassumption.
  - f_equal. f_equal. eapply noninterferent_exp; eassumption.
  (* FILL IN HERE *) Admitted.
(** [] *)
End Div.

(* ################################################################# *)
(** * Speculative constant-time *)

(** This second part of the chapter is based on the Spectre
    Declassified paper [Shivakumar et al 2023a] (in Bib.v) in simplified form
    (e.g., without declassification). Like in this paper, we only look
    at a class of speculative execution attacks called Spectre v1
    [Kocher et al 2019] (in Bib.v). *)

(* ================================================================= *)
(** ** CCT programs can be insecure under speculative execution *)

(** All variables and arrays mentioned in the code below ([X], [Y], [AP]) are
    _public_, so this code respects the CCT discipline, yet this code is not
    secure under speculative execution. *)

Definition spec_insecure_prog :=
  <{{ if Y < 3 then (* <- this check can misspeculate for Y >= 3! *)
        X <- AP[Y]; (* <- speculative out of bounds access
                          loads _a secret_ to public variable X *)
        if X <= 5   (* <- speculatively leak X *)
        then X := 5
        else skip end
      else skip end }}> .

(** The size of public array [AP] is [3] and we check we're in bounds, yet a
    modern processor can predict that the [Y < 3] check will be true and start
    executing the then branch even in cases when [Y >= 3]. We assume we also
    have a secret array [AS], which is not even mentioned in the code, yet its
    contents can still be leaked under speculative execution. *)

Example spec_insecure_prog_is_ct_well_typed :
  LXYZpub ;; LAPpub |-ct- spec_insecure_prog.
Proof. apply cct_typechecker_sound. reflexivity. Qed.

(** Here is a more realistic version of this example: *)

Definition spec_insecure_prog_2 :=
  <{{ X := 0;
      Y := 0;
      while Y < 3 do
        Z <- AP[Y];
        X := X + Z;
        Y := Y + 1
      end;
      if X <= 5 then X := 5 else skip end }}> .

Example spec_insecure_prog_2_is_ct_well_typed :
  LXYZpub ;; LAPpub |-ct- spec_insecure_prog_2.
Proof. apply cct_typechecker_sound. reflexivity. Qed.

(** All variables and arrays mentioned in the program are again public, so also
    this program respects the CCT discipline, yet it is also not secure under
    speculative execution. *)

(** We return to this more realistic program at the end of the chapter and
    prove it is indeed insecure. *)

(* ================================================================= *)
(** ** Speculative semantics *)

(** To reason about security against such Spectre v1 attacks we will introduce a
    speculative semantics. This semantics models leakage using the same CCT
    observations as above ([OBranch], [OALoad], and [OAStore]). *)

(** More interestingly, to model speculative execution we add to the semantics
    adversary-provided _directions_, which control the speculation behavior: *)

Inductive direction :=
| DStep  (* adversary chooses the correct branch *)
| DForce (* adversary forces us to take the wrong branch *)
| DLoad (a : string) (i : nat)   (* for speculative OOB array accesses *)
| DStore (a : string) (i : nat). (* adversary chooses array and index *)

Definition dirs := list direction.

(** This gives us a very high-level model of speculation that abstracts away
    low-level details such as the compiler, branch predictors, memory layout,
    speculation window, rollbacks, etc. We do this in a way that tries to
    overapproximate the adversary's power.

    This is the kind of speculation model used by the Jasmin language. *)

(** Compared to the CCT semantics with observations as output, we now add the
    directions as input to the evaluation judgement and we also track a
    misspeculation bit [b]. *)

(**

  ----------------------------------------- (Spec_Skip)
  <(s,m,b,[])> =[skip]=> <(s,m,b,[])>

                 eval s e = n
   ----------------------------------------------- (Spec_Asgn)
   <(s,m,b,[])> =[x:=e]=> <(x!->n;s,m,b,[])>

     <(s,m,b,ds1)> =[c1]=> <(s',m',b',os1)>
   <(s',m',b',ds2)> =[c2]=> <(s'',m'',b'',os2)>
------------------------------------------------------------ (Spec_Seq)
<(s,m,b,ds1++ds2)> =[c1;c2]=> <(s'',m'',b'',os1++os2)>

  <(s,m,b,ds)> =[ if be then (c; while be do c end)
                        else skip end ]=> <(s',m',b',os)>
----------------------------------------------------------- (Spec_While)
<(s,m,b,ds)> =[ while be do c end ]=> <(s',m',b',os)>

*)

(** If the attacker issues the [DStep] directive we execute the correct
    if branch, as before:

   let c := if not_zero (eval s be) then c1 else c2 in
       <(s,m,b,ds)> =[ c ]=> <(s',m',b',os1)>
 ---------------------------------------------------------- (Spec_If)
 <(s,m,b, DStep::ds)> =[ if be then c1 else c2 end ]=>
   <(s',m',b', [OBranch (not_zero (eval s be))]++os1)>
*)

(** If the attacker issues [DForce] we execute the wrong if branch:

   let c := if not_zero (eval s be) then c2 else c1 in
     <(s,m,true,ds)> =[ c ]=> <(s',m',true,os1)>
---------------------------------------------------------- (Spec_If_F)
<(s,m,b, DForce::ds)> =[ if be then c1 else c2 end ]=>
  <(s',m',true, [OBranch (not_zero (eval s be))]++os1)>

    In case of such misspeculation we also set [b] to [true].
*)

(** If the attacker issues [DStep] we load from the correct index ([i])
    in the correct array ([a]), as before:

      eval s ie = i      i < length(m a)
 ------------------------------------------ (Spec_ALoad)
 <(s, m, b, [DStep])> =[ x <- a[ie] ]=>
 <(x !-> (m a).[i]; s, m, b, [OALoad a i])>
*)

(** If we have already misspeculated ([b=true]) and the load is out of bounds
    the attacker can also issue [DLoad a' i'] and then we load from the array
    [a'] at location [i']:

eval s ie = i   i >= length(m a)   i' < length(m a')
---------------------------------------------------- (Spec_ALoad_U)
  <(s, m, true, [DLoad a' i'])> =[ x <- a[ie] ]=>
  <(x !-> (m a').[i']; s, m, true, [OALoad a i])>
*)

(** The rules for store are very similar to the ones for load:

 eval s e = n    eval s ie = i    i < length(m a)
----------------------------------------------------------- (Spec_AStore)
    <(s, m, b, [DStep])> =[ a[ie] <- e ]=>
    <(s, a !-> (m a).[i <- n]; m, b, [OAStore a i])>

        eval s e = n     eval s ie = i
      i >= length(m a)   i' < length(m a')
----------------------------------------------------------- (Spec_AStore_U)
 <(s, m, true, [DStore a' i'])> =[ a[ie] <- e ]=>
 <(s, a' !-> (m a').[i' <- n]; m, true, [OAStore a i])>
*)

(** These array access rules abstract away from the actual layout of the arrays
    in memory at a lower level, while overapproximating the attacker's power. *)

(** Out of bounds stores allow the attacker to put secrets into public
    arrays, so that later even in bounds public loads can load secrets. *)

Definition spec_insecure_store_then_load :=
  <{{ if Y < 2 then (* <- this check can misspeculate for Y >= 2! *)
        AS[Y] <- W; (* <- speculative out-of-bounds store can write
                          the secret W to index 0 of public array AP *)
        X <- AP[0]; (* <- this in-bounds public load then loads
                          the secret into X *)
        if X <= 5 then X := 5 else skip end (* <- speculatively leak X *)
      else skip end }}>.

(** Formally the speculative semantics definition looks as follows: *)

Reserved Notation
  "'<(' s , m , b , ds ')>' '=[' c ']=>' '<(' s' , m' , bb , os ')>'"
  (at level 40, c custom com at level 99,
   s constr, m constr, s' constr, m' constr at next level).

Inductive spec_eval : com -> state -> mem -> bool -> dirs ->
                             state -> mem -> bool -> obs -> Prop :=
  | Spec_Skip : forall s m b,
      <(s, m, b, [])> =[ skip ]=> <(s, m, b, [])>
  | Spec_Asgn  : forall s m b e n x,
      eval s e = n ->
      <(s, m, b, [])> =[ x := e ]=> <(x !-> n; s, m, b, [])>
  | Spec_Seq : forall c1 c2 s m b s' m' b' s'' m'' b'' os1 os2 ds1 ds2,
      <(s, m, b, ds1)> =[ c1 ]=> <(s', m', b', os1)>  ->
      <(s', m', b', ds2)> =[ c2 ]=> <(s'', m'', b'', os2)> ->
      <(s, m, b, ds1++ds2)>  =[ c1 ; c2 ]=> <(s'', m'', b'', os1++os2)>
  | Spec_If : forall s m b s' m' b' be c1 c2 os1 ds,
      let c := (if (not_zero (eval s be)) then c1 else c2) in
      <(s, m, b, ds)> =[ c ]=> <(s', m', b', os1)> ->
      <(s, m, b, DStep :: ds)> =[ if be then c1 else c2 end ]=>
      <(s', m', b', [OBranch (not_zero (eval s be))] ++ os1)>
  | Spec_If_F : forall s m b s' m' be c1 c2 os1 ds,
      let c := (if (not_zero (eval s be)) then c2 else c1) in
      (* ^- branches swapped *)
      <(s, m, true, ds)> =[ c ]=> <(s', m', true, os1)> ->
      <(s, m, b, DForce :: ds)> =[ if be then c1 else c2 end ]=>
      <(s', m', true, [OBranch (not_zero (eval s be))] ++ os1)>
  | Spec_While : forall be s m b ds s' m' b' os c,
      <(s, m, b, ds)> =[ if be then (c; while be do c end) else skip end ]=>
      <(s', m', b', os)> ->
      <(s, m, b, ds)> =[ while be do c end ]=> <(s', m', b', os)>
  | Spec_ALoad : forall s m b x a ie i,
      eval s ie = i ->
      i < length (m a) ->
      <(s, m, b, [DStep])> =[ x <- a[ie] ]=>
      <(x !-> (m a).[i]; s, m, b, [OALoad a i])>
  | Spec_ALoad_U : forall s m x a ie i a' i',
      eval s ie = i ->
      i >= length (m a) ->
      i' < length (m a') ->
      <(s, m, true, [DLoad a' i'])> =[ x <- a[ie] ]=>
      <(x !-> (m a').[i']; s, m, true, [OALoad a i])>
  | Spec_AStore : forall s m b a ie i e n,
      eval s e = n ->
      eval s ie = i ->
      i < length (m a) ->
      <(s, m, b, [DStep])> =[ a[ie] <- e ]=>
      <(s, a !-> (m a).[i <- n]; m, b, [OAStore a i])>
  | Spec_AStore_U : forall s m a ie i e n a' i',
      eval s e = n ->
      eval s ie = i ->
      i >= length (m a) ->
      i' < length (m a') ->
      <(s, m, true, [DStore a' i'])> =[ a[ie] <- e ]=>
      <(s, a' !-> (m a').[i' <- n]; m, true, [OAStore a i])>

  where "<( s , m , b , ds )> =[ c ]=> <( s' , m' , bb , os )>" :=
    (spec_eval c s m b ds s' m' bb os).

Hint Constructors spec_eval : core.



(* ================================================================= *)
(** ** Structural properties of speculative semantics *)

(** As a warm-up we formalize some structural properties of our speculative semantics: *)

(** **** Exercise: 1 star, standard (speculation_bit_monotonic) *)

(** As mentioned above, our speculative semantics is very high-level, and
    doesn't have to deal with detecting misspeculation and rolling back. So in
    our semantics once the misspeculation bit is set to true, it will stay set: *)

Lemma speculation_bit_monotonic :
  forall c s a b ds s' a' b' os,
  <(s, a, b, ds)> =[ c ]=> <(s', a', b', os)> ->
  b = true ->
  b' = true.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** Conversely, misspeculation cannot start on its own: if an execution starts
    with the misspeculation bit unset but ends with it set, then the attacker
    must have passed a [DForce] direction. *)

Lemma speculation_needs_force :
  forall c s a b ds s' a' b' os,
  <(s, a, b, ds)> =[ c ]=> <(s', a', b', os)> ->
  b = false ->
  b' = true ->
  In DForce ds.
Proof.
  intros c s a b ds s' a' b' os Heval Hb Hb'.
  induction Heval; subst; simpl; eauto; try discriminate.
  apply in_or_app. destruct b'; eauto.
Qed.

(** We can recover sequential execution from [spec_eval] if there is no
    speculation, so all directives are [DStep] and misspeculation flag starts
    set to [false]. *)

Definition seq_spec_eval (c :com) (s :state) (m :mem)
    (s' :state) (m' :mem) (os :obs) : Prop :=
  exists ds, (forall d, In d ds -> d = DStep) /\
    <(s, m, false, ds)> =[ c ]=> <(s', m', false, os)>.

(** We prove that this new definition for sequential execution is equivalent to
    the old one, i.e. [cteval]. *)

Lemma cteval_equiv_seq_spec_eval : forall c s m s' m' os,
  seq_spec_eval c s m s' m' os <-> <(s, m)> =[ c ]=> <(s', m', os)>.
Proof.
  intros c s m s' m' os. unfold seq_spec_eval. split; intros H.
  - (* -> *)
    destruct H as [ds [Hstep Heval]].
    induction Heval; try (now econstructor; eauto).
    + (* Spec_Seq *)
      eapply CTE_Seq.
      * eapply IHHeval1. intros d HdIn.
        assert (L: In d ds1 \/ In d ds2) by (left; assumption).
        eapply in_or_app in L. eapply Hstep in L. assumption.
      * eapply IHHeval2. intros d HdIn.
        assert (L: In d ds1 \/ In d ds2) by (right; assumption).
        eapply in_or_app in L. eapply Hstep in L. assumption.
    + (* Spec_If *)
      eapply CTE_If. destruct (eval s be) eqn:Eqbe.
      * eapply IHHeval. intros d HdIn.
        apply (in_cons DStep d) in HdIn.
        apply Hstep in HdIn. assumption.
      * eapply IHHeval. intros d HdIn.
        apply (in_cons DStep d) in HdIn.
        apply Hstep in HdIn. assumption.
    + (* Spec_IF_F; contra *)
      exfalso.
      assert (L: ~(DForce = DStep)) by discriminate.
      apply L. apply (Hstep DForce). apply in_eq.
    + (* Spec_ALoad_U; contra *)
      exfalso.
      assert (L: ~(DLoad a' i' = DStep)) by discriminate.
      apply L. apply (Hstep (DLoad a' i')). apply in_eq.
    + (* Spec_AStore_U; contra *)
      exfalso.
      assert (L: ~(DStore a' i' = DStep)) by discriminate.
      apply L. apply (Hstep (DStore a' i')). apply in_eq.
  - (* <- *)
    induction H.
    + (* CTE_Skip *)
      exists []; split; [| eapply Spec_Skip].
      simpl. intros d Contra; destruct Contra.
    + (* CTE_Asgn *)
      exists []; split; [| eapply Spec_Asgn; assumption].
      simpl. intros d Contra; destruct Contra.
    + (* CTE_Seq *)
      destruct IHcteval1 as [ds1 [Hds1 Heval1]].
      destruct IHcteval2 as [ds2 [Hds2 Heval2]].
      exists (ds1 ++ ds2). split; [| eapply Spec_Seq; eassumption].
      intros d HdIn. apply in_app_or in HdIn.
      destruct HdIn as [Hin1 | Hin2].
      * apply Hds1 in Hin1. assumption.
      * apply Hds2 in Hin2. assumption.
    + (* CTE_If *)
      destruct IHcteval as [ds [Hds Heval]].
      exists (DStep :: ds). split.
      * intros d HdIn. apply in_inv in HdIn.
        destruct HdIn as [Heq | HIn];
          [symmetry; assumption | apply Hds; assumption].
      * subst c. eapply Spec_If. eauto.
    + (* CTE_While *)
      destruct IHcteval as [ds [Hds Heval]].
      exists ds. split; [assumption |].
      eapply Spec_While; assumption.
    + (* CTE_ALoad *)
      exists [DStep]. split.
      * simpl. intros d HdIn.
        destruct HdIn as [Heq | Contra]; [| destruct Contra].
        symmetry. assumption.
      * eapply Spec_ALoad; assumption.
    + (* CTE_AStore *)
      exists [DStep]. split.
      * simpl. intros d HdIn.
        destruct HdIn as [Heq | Contra]; [| destruct Contra].
        symmetry. assumption.
      * eapply Spec_AStore; assumption.
Qed.

(** **** Exercise: 1 star, standard (ct_well_typed_seq_spec_eval_ct_secure)

    Use this equivalence to transfer our earlier security theorem to the
    speculative semantics: CCT well-typed programs produce the same observations
    in any two sequential executions that start in publicly equivalent states
    and memories. Note that this statement is precisely [cct_secure], just
    using sequential executions of the new speculative semantics. Hint: this
    corollary is a direct consequence of the results we already proved
    above. *)

Corollary ct_well_typed_seq_spec_eval_ct_secure :
  forall L LA c s1 s2 m1 m2 s1' s2' m1' m2' os1 os2,
  L ;; LA |-ct- c ->
  pub_equiv L s1 s2 ->
  pub_equiv LA m1 m2 ->
  seq_spec_eval c s1 m1 s1' m1' os1 ->
  seq_spec_eval c s2 m2 s2' m2' os2 ->
  os1 = os2.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ================================================================= *)
(** ** Speculative constant-time security definition *)

(** The definition of speculative constant-time security is very similar to CCT
    security, but applied to the speculative semantics, where the two executions
    receive the same directions [ds]: *)

Definition spec_ct_secure L LA c :=
  forall s1 s2 m1 m2 s1' s2' m1' m2' b1' b2' os1 os2 ds,
    pub_equiv L s1 s2 ->
    pub_equiv LA m1 m2 ->
    <(s1, m1, false, ds)> =[ c ]=> <(s1', m1', b1', os1)> ->
    <(s2, m2, false, ds)> =[ c ]=> <(s2', m2', b2', os2)> ->
    os1 = os2.

(** We can use this definition to show that our first example is speculatively
    insecure: *)

Print spec_insecure_prog. (* [[
= <{{ if Y < 3 then
        X <- AP[Y];
        if X <= 5 then X := 5 else skip end
      else skip end }}> ]]
*)

(** For this we build a counterexample where the attacker chooses an
    out-of-bounds index [Y = 3] and then passes the directions:
    [[DForce; DLoad AS 0; DStep]].  This causes the two executions to load
    different values for [X] from index [0] of secret array [AS].
    If the different values loaded from [AS[0]] are well chosen (e.g., [4 <= 5]
    in the first execution and [7 > 5] in the second) this causes two different
    observations:
    - [[OBranch false; OALoad AP 3; OBranch true]] and
    - [[OBranch false; OALoad AP 3; OBranch false]].  *)

Example spec_insecure_prog_is_spec_insecure :
  ~(spec_ct_secure LXYZpub LAPpub spec_insecure_prog).
Proof.
  unfold spec_insecure_prog. intros Hcs.
  remember (Y!-> 3; __ !-> 0) as s.
  remember (AP!-> [0;1;2]; AS!-> [4;1]; __ !-> []) as m1.
  remember (AP!-> [0;1;2]; AS!-> [7;1]; __ !-> []) as m2.
  remember (DForce :: [DLoad AS 0] ++ [DStep]) as ds.
  assert (Heval1:
            <(s, m1, false, ds )> =[ spec_insecure_prog ]=>
            <( X!-> 5; X!-> 4; s, m1, true,
               [OBranch false] ++ [OALoad AP 3] ++ [OBranch true] ++ [])>).
  { unfold spec_insecure_prog; subst.
    eapply Spec_If_F. eapply Spec_Seq.
    - eapply Spec_ALoad_U; simpl; eauto.
    - eapply Spec_If; simpl; auto. }
  assert (Heval2:
            <(s, m2, false, ds )> =[ spec_insecure_prog ]=>
            <( X!-> 7; s, m2, true,
               [OBranch false] ++ [OALoad AP 3] ++ [OBranch false] ++ [])>).
  { unfold spec_insecure_prog; subst.
    eapply Spec_If_F. eapply Spec_Seq.
    - eapply Spec_ALoad_U; simpl; eauto.
    - eapply Spec_If; simpl; auto. }
  subst. eapply Hcs in Heval1.
  + eapply Heval1 in Heval2. discriminate.
  + eapply pub_equiv_refl.
  + apply pub_equiv_update_public; auto.
    apply pub_equiv_update_secret; auto.
    apply pub_equiv_refl.
Qed.

(** A similar counterexample can be used to show that
    [spec_insecure_store_then_load] is speculatively insecure. *)

Print spec_insecure_store_then_load. (* [[
= <{{ if Y < 2 then
        AS[Y] <- W;
        X <- AP[0];
        if X <= 5 then X := 5 else skip end
      else skip end }}> ]]
*)

(** This time the attacker chooses the out-of-bounds index [Y = 2] (recall
    that [AS] has size 2) and passes the directions:
    [[DForce; DStore AP 0; DStep; DStep]]. The [DStore AP 0] direction
    redirects the out-of-bounds store, putting the secret value of [W] into
    [AP[0]], from where the subsequent in-bounds load reads it, so the final
    branch observation again leaks the secret. *)

Example spec_insecure_store_then_load_is_spec_insecure :
  ~(spec_ct_secure LXYZpub LAPpub spec_insecure_store_then_load).
Proof.
  unfold spec_insecure_store_then_load. intros Hcs.
  remember (W!-> 4; Y!-> 2; __ !-> 0) as s1.
  remember (W!-> 7; Y!-> 2; __ !-> 0) as s2.
  remember (AP!-> [0;1;2]; AS!-> [4;1]; __ !-> []) as m.
  remember (DForce :: [DStore AP 0] ++ [DStep] ++ [DStep]) as ds.
  assert (Heval1:
            <(s1, m, false, ds )> =[ spec_insecure_store_then_load ]=>
            <( X!-> 5; X!-> 4; s1, AP!-> [4;1;2]; m, true,
               [OBranch false] ++ [OAStore AS 2] ++ [OALoad AP 0]
                 ++ [OBranch true] ++ [])>).
  { unfold spec_insecure_store_then_load; subst.
    eapply Spec_If_F. eapply Spec_Seq.
    - eapply Spec_AStore_U; simpl; eauto.
    - eapply Spec_Seq.
      + eapply Spec_ALoad; simpl; eauto.
      + eapply Spec_If; simpl; auto. }
  assert (Heval2:
            <(s2, m, false, ds )> =[ spec_insecure_store_then_load ]=>
            <( X!-> 7; s2, AP!-> [7;1;2]; m, true,
               [OBranch false] ++ [OAStore AS 2] ++ [OALoad AP 0]
                 ++ [OBranch false] ++ [])>).
  { unfold spec_insecure_store_then_load; subst.
    eapply Spec_If_F. eapply Spec_Seq.
    - eapply Spec_AStore_U; simpl; eauto.
    - eapply Spec_Seq.
      + eapply Spec_ALoad; simpl; eauto.
      + eapply Spec_If; simpl; auto. }
  subst. eapply Hcs in Heval1.
  + eapply Heval1 in Heval2. discriminate.
  + apply pub_equiv_update_secret; auto. apply pub_equiv_refl.
  + apply pub_equiv_refl.
Qed.

(* ================================================================= *)
(** ** Selective SLH transformation *)

(** Now how can we make CCT programs secure against speculative execution
    attacks? It turns out that we can protect such programs against Spectre v1
    by doing only two things:
    - Keep track of a misspeculation flag using constant-time conditionals;
    - Use this flag to mask the value of misspeculated public loads.

    We implement this as a _Selective Speculative Load Hardening_ (SLH)
    transformation that we will show enforces speculative constant-time security
    for all CCT-well-typed programs.

    This SLH transformation is "selective", since it only masks _public_ loads.
    A non-selective SLH transformation was invented in LLVM
    [Carruth 2018] (in Bib.v), but what they implement is anyway much more
    complicated and not very principled. *)

(** We track if we have misspeculated or not using a fresh variable: *)
Definition msf : string := "msf". (* misspeculation flag variable *)

(** The [sel_slh] transformation below keeps the variable [msf] equal to
    [1] exactly when execution is misspeculating: at each branch, a
    constant-time conditional sets [msf] to [1] if the taken branch disagrees
    with the branch condition, and otherwise leaves [msf] unchanged. This flag
    is then used to mask loads into _public_ variables: after each such load,
    another constant-time conditional overwrites the loaded value with [0]
    whenever [msf] records misspeculation, so speculatively loaded secrets can
    never reach public variables: *)

Fixpoint sel_slh (L:label_map) (c:com) :=
  match c with
  | <{{if be then c1 else c2 end}}> =>
      <{{if be then msf := (be ? msf : 1); (* <- tracking flag *)
                    sel_slh L c1
               else msf := (be ? 1 : msf); (* <- tracking flag *)
                    sel_slh L c2 end}}>
  | <{{while be do c end}}> =>
      <{{while be do
           msf := (be ? msf : 1); (* <- tracking flag *)
           sel_slh L c end;
         msf := (be ? 1 : msf)}}> (* <- tracking flag *)
  | <{{x <- a[i]}}> =>
      if L x =? public
      then <{{x <- a[i]; (* ↓ masking public load value *)
              x := (msf <> 0) ? 0 : x}}>
      else <{{x <- a[i]}}>
  | <{{c1; c2}}> => <{{sel_slh L c1; sel_slh L c2}}>
  | _ => c
  end.

(** We can use [sel_slh] to harden our example speculatively-insecure
    programs, starting with our first example: *)

Print spec_insecure_prog. (* [[
= <{{ if Y < 3 then
        X <- AP[Y];
        if X <= 5 then X := 5 else skip end
      else skip end }}> ]]
*)

Definition sel_slh_spec_insecure_prog :=
<{{ if Y < 3 then
      msf := ((Y < 3) ? msf : 1);
      (X <- AP[Y]; X := (msf <> 0) ? 0 : X);
      if X <= 5 then
        msf := ((X <= 5) ? msf : 1);
        X := 5
      else msf := ((X <= 5) ? 1 : msf); skip end
    else msf := ((Y < 3) ? 1 : msf); skip end }}>.

Lemma sel_slh_spec_insecure_prog_check:
  sel_slh LXYZpub spec_insecure_prog = sel_slh_spec_insecure_prog.
Proof. reflexivity. Qed.

(** When misspeculation occurs in the first condition [if Y < 3], the
    transformation detects this misspeculation and sets [msf] (misspeculation
    flag) to [1].  Then, although the secret value gets loaded into X via the
    out-of-bounds access [X <- AP[Y]], it is immediately overwritten with 0 due
    to the masking code [X := (msf <> 0) ? 0 : X] that follows. As a result, all
    subsequent operations like [if X <= 5] only use the masked value [0]
    instead of the actual secret. *)

(** **** Exercise: 2 stars, standard (sel_slh_store_then_load)

    Write down explicitly the program that the [sel_slh] transformation produces
    for the [spec_insecure_store_then_load] example. Note that this exercise is
    graded manually: to get the points you have to write down the transformed
    program _explicitly_ in the style of the previous example above. *)

Definition sel_slh_spec_insecure_store_then_load : com
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

(** Check your definition using the transformation; if your definition above is
    correct this can be proved by reflexivity: *)

Lemma sel_slh_spec_insecure_store_then_load_check :
  sel_slh LXYZpub spec_insecure_store_then_load
  = sel_slh_spec_insecure_store_then_load.
Proof.
  (* FILL IN HERE *) Admitted.
(* Do not modify the following line: *)
Definition manual_grade_for_sel_slh_store_then_load : option (nat*string) := None.
(** [] *)

(* ================================================================= *)
(** ** Main idea for proving [sel_slh] secure: use ideal semantics *)

(** To prove [sel_slh] secure, Spectre Declassified uses an ideal
    semantics, capturing selective speculative load hardening more abstractly.
    The proof effort is decomposed into two parts:
    - a speculative constant-time proof for the ideal semantics;
    - a compiler correctness proof for the [sel_slh] transformation, taking source
      programs which are executed using the ideal semantics, to target programs
      executed using the speculative semantics.
 *)

(** In a little bit more detail, we're intuitively trying to prove:

forall L LA c, L;;LA |-ct- c -> spec_ct_secure L LA (sel_slh L c),

    where the conclusion looks as follows:
<<
forall s1 s2 m1 m2 s1' s2' m1' m2' b1' b2' os1 os2 ds,
  pub_equiv L s1 s2 ->
  pub_equiv LA m1 m2 ->
  <(s1,m1,false,ds)> =[ sel_slh L c ]=> <(s1',m1',b1',os1)> ->
  <(s2,m2,false,ds)> =[ sel_slh L c ]=> <(s2',m2',b2',os2)> ->
  os1 = os2

    Compiler correctness allows us to get rid of [sel_slh L c] in the premises
    and instead get an execution in terms of the ideal semantics:

  <(s,m,b,ds)> =[ sel_slh L c ]=> <(s',m',b',os)> ->
    L |-i <(s,m,b,ds)> =[ c ]=> <(msf!->s msf;s',m',b',os)>
*)

(** One thing to note is that the ideal semantics doesn't track misspeculation
    in the [msf] variable, but instead directly uses the misspeculation bit in
    the speculative semantics for masking. This allows us to keep the ideal
    semantics simple, and then we show that [msf] correctly tracks misspeculation
    in our compiler correctness proof. *)

(* ================================================================= *)
(** ** Ideal semantics definition *)

(** All rules of the ideal semantics are the same as for the speculative
    semantics, except the rules for array loads, which add the extra
    masking done by [sel_slh] on top of the speculative semantics:

      eval s ie = i      i < length(m a)
 ----------------------------------------------------- (Ideal_ALoad)
let v := if b && (L x =? public) then 0 else (m a).[i] in
L |-i <(s, m, b, [DStep])> =[ x <- a[ie] ]=>
      <(x !-> v; s, m, b, [OALoad a i])>
*)

(** The rule for the [DLoad] directive is very similar,
    but specialized knowing that for this rule to apply [b=true]:

eval s ie = i   i >= length(m a)   i' < length(m a')
------------------------------------------------------------ (Ideal_ALoad_U)
let v := if L x =? public then 0 else (m a').[i'] in
L |-i <(s, m, true, [DLoad a' i'])> =[ x <- a[ie] ]=>
      <(x !-> v; s, m, true, [OALoad a i])>
*)

(** This is formalized as follows: *)
Reserved Notation
  "L '|-i' '<(' s , m , b , ds ')>' '=[' c ']=>' '<(' s' , m' , bb , os ')>'"
  (at level 40, c custom com at level 99,
   s constr, m constr, s' constr, m' constr at next level).

Inductive ideal_eval (L:label_map) :
    com -> state -> mem -> bool -> dirs ->
           state -> mem -> bool -> obs -> Prop :=
  | Ideal_Skip : forall s m b,
      L |-i <(s, m, b, [])> =[ skip ]=> <(s, m, b, [])>
  | Ideal_Asgn  : forall s m b e n x,
      eval s e = n ->
      L |-i <(s, m, b, [])> =[ x := e ]=> <(x !-> n; s, m, b, [])>
  | Ideal_Seq : forall c1 c2 s m b s' m' b' s'' m'' b'' os1 os2 ds1 ds2,
      L |-i <(s, m, b, ds1)> =[ c1 ]=> <(s', m', b', os1)>  ->
      L |-i <(s', m', b', ds2)> =[ c2 ]=> <(s'', m'', b'', os2)> ->
      L |-i <(s, m, b, ds1++ds2)>  =[ c1 ; c2 ]=> <(s'', m'', b'', os1++os2)>
  | Ideal_If : forall s m b s' m' b' be c1 c2 os1 ds,
      let c := (if (not_zero (eval s be)) then c1 else c2) in
      L |-i <(s, m, b, ds)> =[ c ]=> <(s', m', b', os1)> ->
      L |-i <(s, m, b, DStep :: ds)> =[ if be then c1 else c2 end ]=>
        <(s', m', b', [OBranch (not_zero (eval s be))] ++ os1 )>
  | Ideal_If_F : forall s m b s' m' be c1 c2 os1 ds,
      let c := (if (not_zero (eval s be)) then c2 else c1) in
      (* ^- branches swapped *)
      L |-i <(s, m, true, ds)> =[ c ]=> <(s', m', true, os1)> ->
      L |-i <(s, m, b, DForce :: ds)> =[ if be then c1 else c2 end ]=>
        <(s', m', true, [OBranch (not_zero (eval s be))] ++ os1)>
  | Ideal_While : forall be s m b ds s' m' b' os c,
      L |-i <(s, m, b, ds)> =[ if be then (c; while be do c end) else skip end ]=>
        <(s', m', b', os)> ->
      L |-i <(s, m, b, ds)> =[ while be do c end ]=> <(s', m', b', os)>
  | Ideal_ALoad : forall s m b x a ie i,
      eval s ie = i ->
      i < length (m a) ->
      let v := if b && (L x =? public) then 0 else (m a).[i] in
      L |-i <(s, m, b, [DStep])> =[ x <- a[ie] ]=>
        <(x !-> v; s, m, b, [OALoad a i])>
  | Ideal_ALoad_U : forall s m x a ie i a' i',
      eval s ie = i ->
      i >= length (m a) ->
      i' < length (m a') ->
      let v := if L x =? public then 0 else (m a').[i'] in
      L |-i <(s, m, true, [DLoad a' i'])> =[ x <- a[ie] ]=>
        <(x !-> v; s, m, true, [OALoad a i])>
  | Ideal_AStore : forall s m b a ie i e n,
      eval s e = n ->
      eval s ie = i ->
      i < length (m a) ->
      L |-i <(s, m, b, [DStep])> =[ a[ie] <- e ]=>
        <(s, a !-> (m a).[i <- n]; m, b, [OAStore a i])>
  | Ideal_AStore_U : forall s m a ie i e n a' i',
      eval s e = n ->
      eval s ie = i ->
      i >= length (m a) ->
      i' < length (m a') ->
      L |-i <(s, m, true, [DStore a' i'])> =[ a[ie] <- e ]=>
        <(s, a' !-> (m a').[i' <- n]; m, true, [OAStore a i])>

  where "L |-i <( s , m , b , ds )> =[ c ]=> <( s' , m' , bb , os )>" :=
    (ideal_eval L c s m b ds s' m' bb os).

Hint Constructors ideal_eval : core.

(* ================================================================= *)
(** ** Ideal semantics enforces speculative constant-time *)

(** We prove that the ideal semantics enforces speculative
    constant-time for CCT-well-typed programs:

    L ;; LA |-ct- c ->
    pub_equiv L s1 s2 ->
    pub_equiv LA m1 m2 ->
    L |-i <(s1, m1, false, ds)> =[ c ]=> <(s1', m1', b1', os1)> ->
    L |-i <(s2, m2, false, ds)> =[ c ]=> <(s2', m2', b2', os2)> ->
    os1 = os2.

    On its own this proof is simple and standard. As in the proofs we did before
    for instance for CCT and CF security, we rely on a proof of
    _noninterference_, which for us is where all the interesting action happens:
    - For a start, it is noninterference that is broken by our speculative
      execution attacks and that is fixed by masking misspeculated public loads.
    - Moreover, for our ideal semantics the noninterference proof requires two
      interesting generalizations of the induction hypothesis. *)

(** Generalization 1: We need to also deal with executions ending with [b=true],
    but in that case we cannot ensure that the array states are publicly
    equivalent, since our selective SLH does not mask misspeculated stores (for
    efficiency, since it's not needed for security). This requires generalizing
    the [pub_equiv LA m1 m2] premise of our statements too. *)

(** Generalization 2: To show that the two executions run in lock-step the
    proof uses not only the CCT type system (no branching on secrets) but
    also the fact that both executions receive the same directions. This
    fact cannot simply be assumed in the induction though: in the sequence
    case each execution splits its direction list as [ds1++ds1'] and
    [ds2++ds2'] respectively, and these two splits could a priori be
    different. So the induction hypothesis only assumes the weaker fact
    that one direction list is a prefix of the other, and the conclusion
    then recovers that the two lists are in fact equal. *)

(** So our general noninterference statement looks as follows:

    L ;; LA |-ct- c ->
    pub_equiv L s1 s2 ->
    (b = false -> pub_equiv LA m1 m2) ->         <-- Generalization 1
    (prefix ds1 ds2 \/ prefix ds2 ds1) ->        <-- Generalization 2
    L |-i <(s1, m1, b, ds1)> =[ c ]=> <(s1', m1', b1', os1)> ->
    L |-i <(s2, m2, b, ds2)> =[ c ]=> <(s2', m2', b2', os2)> ->
    pub_equiv L s1' s2' /\ b1' = b2' /\
      (b1' = false -> pub_equiv LA m1' m2') /\   <-- Generalization 1
      ds1 = ds2                                  <-- Generalization 2
*)

(** For more details on this please see the proof of
    [ct_well_typed_ideal_noninterferent_general] below. *)

(** The noninterference generalization requires to reason about list prefixes,
    so we first prove some general lemmas about that: *)

Definition prefix {X:Type} (xs ys : list X) : Prop :=
  exists zs, xs ++ zs = ys.

Lemma prefix_refl : forall {X:Type} {ds : list X},
  prefix ds ds.
Proof. intros X ds. exists []. apply app_nil_r. Qed.

Lemma prefix_nil : forall {X:Type} (ds : list X),
  prefix [] ds.
Proof. intros X ds. unfold prefix. eexists. simpl. reflexivity. Qed.

Lemma prefix_heads_and_tails : forall {X:Type} (h1 h2 : X) (t1 t2 : list X),
  prefix (h1::t1) (h2::t2) -> h1 = h2 /\ prefix t1 t2.
Proof.
  intros X h1 h2 t1 t2. unfold prefix. intros Hpre.
  destruct Hpre as [zs Hpre]; simpl in Hpre.
  inversion Hpre; subst. eauto.
Qed.

Lemma prefix_heads : forall {X:Type} (h1 h2 : X) (t1 t2 : list X),
  prefix (h1::t1) (h2::t2) -> h1 = h2.
Proof.
  intros X h1 h2 t1 t2 H. apply prefix_heads_and_tails in H; tauto.
Qed.

Lemma prefix_or_heads : forall {X:Type} (x y : X) (xs ys : list X),
  prefix (x :: xs) (y :: ys) \/ prefix (y :: ys) (x :: xs) ->
  x = y.
Proof.
  intros X x y xs ys H.
  destruct H as [H | H]; apply prefix_heads in H; congruence.
Qed.

Lemma prefix_cons : forall {X:Type} (d :X) (ds1 ds2: list X),
 prefix ds1 ds2 <->
 prefix (d::ds1) (d::ds2).
Proof.
  intros X d ds1 ds2. split; [unfold prefix| ]; intros H.
  - destruct H; subst.
    eexists; simpl; eauto.
  - apply prefix_heads_and_tails in H. destruct H as [_ H]. assumption.
Qed.

Lemma prefix_app : forall {X:Type} {ds1 ds2 ds0 ds3 : list X},
  prefix (ds1 ++ ds2) (ds0 ++ ds3) ->
  prefix ds1 ds0 \/ prefix ds0 ds1.
Proof.
  intros X ds1. induction ds1 as [| d1 ds1' IH]; intros ds2 ds0 ds3 H.
  - left. apply prefix_nil.
  - destruct ds0 as [| d0 ds0'] eqn:D0.
    + right. apply prefix_nil.
    + simpl in H; apply prefix_heads_and_tails in H.
      destruct H as [Heq Hpre]; subst.
      apply IH in Hpre; destruct Hpre; [left | right];
      apply prefix_cons; assumption.
Qed.

Lemma prefix_append_front : forall {X:Type} {ds1 ds2 ds3 : list X},
  prefix (ds1 ++ ds2) (ds1 ++ ds3) ->
  prefix ds2 ds3.
Proof.
  intros X ds1. induction ds1 as [| d1 ds1' IH]; intros ds2 ds3 H.
  - auto.
  - simpl in H; apply prefix_cons in H. apply IH in H. assumption.
Qed.

Lemma app_eq_prefix : forall {X:Type} {ds1 ds2 ds1' ds2' : list X},
  ds1 ++ ds2 = ds1' ++ ds2' ->
  prefix ds1 ds1' \/ prefix ds1' ds1.
Proof.
  intros X ds1. induction ds1 as [| h1 t1 IH]; intros ds2 ds1' ds2' H.
  - left. apply prefix_nil.
  - destruct ds1' as [| h1' t1'] eqn:D1'.
    + right. apply prefix_nil.
    + simpl in H; inversion H; subst.
      apply IH in H2. destruct H2 as [HL | HR];
      [left | right]; apply prefix_cons; auto.
Qed.

(** We also define a variant of [split] that's used in the proofs below. *)
Ltac split4 := split; [|split; [| split]].

(** Finally, we use these things to prove the general statement of
    noninterference, by induction on the first evaluation derivation and
    inversion of the second, as in our previous noninterference proofs.
    Two further points are worth noting. First, since the two executions
    receive the same directions and branch conditions are public, the two
    runs stay in lock-step even while misspeculating: the attacker can only
    force both executions into the _same_ wrong branch. Second, the masking
    of public loads is exactly what makes the load cases go through under
    misspeculation: the two runs may speculatively load different secrets,
    but both mask the loaded value to [0], so the resulting states stay
    publicly equivalent. *)
Lemma ct_well_typed_ideal_noninterferent_general : forall L LA c,
  forall s1 s2 m1 m2 b s1' s2' m1' m2' b1' b2' os1 os2 ds1 ds2,
    L ;; LA |-ct- c ->
    pub_equiv L s1 s2 ->
    (b = false -> pub_equiv LA m1 m2) ->
    (prefix ds1 ds2 \/ prefix ds2 ds1) ->
    L |-i <(s1, m1, b, ds1)> =[ c ]=> <(s1', m1', b1', os1)> ->
    L |-i <(s2, m2, b, ds2)> =[ c ]=> <(s2', m2', b2', os2)> ->
    pub_equiv L s1' s2' /\ b1' = b2' /\
      (b1' = false -> pub_equiv LA m1' m2') /\
      ds1 = ds2.
Proof.
  intros L LA c s1 s2 m1 m2 b s1' s2' m1' m2' b1' b2' os1 os2 ds1 ds2
    Hwt Heq Haeq Hds Heval1 Heval2.
  generalize dependent s2'. generalize dependent s2.
  generalize dependent m2'. generalize dependent m2.
  generalize dependent os2. generalize dependent b2'.
  generalize dependent ds2.
  induction Heval1; intros ds2X Hds b2' os2' a2 Haeq a2' s2 Heq s2' Heval2;
    inversion Heval2; inversion Hwt; subst.
  - (* Skip *) auto.
  - (* Asgn *) split4; auto.
    destruct (L x) eqn:EqLx.
    + eapply pub_equiv_update_public; eauto.
      eapply noninterferent_exp; eauto.
      destruct l; [auto | simpl in H14; discriminate].
    + eapply pub_equiv_update_secret; eauto.
  - (* Seq *)
    destruct Hds as [Hpre | Hpre]; apply prefix_app in Hpre as Hds1.
    + (* prefix (ds1 ++ ds2) (ds0 ++ ds3) *)
      eapply IHHeval1_1 in Hds1; eauto.
      destruct Hds1 as [ Hstates [Hbits [Hmates Hdirections]]]. subst.
      eapply prefix_append_front in Hpre as Hds2.
      eapply IHHeval1_2 in H14; eauto. firstorder. subst. reflexivity.
    + (* prefix (ds0 ++ ds3) (ds1 ++ ds2) *)
      eapply IHHeval1_1 with (ds2:=ds0) in H13; eauto; [| tauto].
      destruct H13 as [ Hstates [Hbits [Hmates Hdirections]]]. subst.
      eapply prefix_append_front in Hpre as Hds2.
      eapply IHHeval1_2 in H14; eauto. firstorder; subst; reflexivity.
  - (* If *)
    remember (if not_zero (eval s be) then c1 else c2) as c5.
    assert(G : L ;; LA |-ct- c5).
    { subst c5. destruct (eval s be); assumption. }
    assert(Gds : prefix ds ds0 \/ prefix ds0 ds).
    { destruct Hds as [Hds | Hds]; apply prefix_cons in Hds; tauto. }
    subst c4 c5. erewrite noninterferent_exp in H10.
    + specialize (IHHeval1 G _ Gds _ _ _ Haeq _ _ Heq _ H10).
      firstorder; congruence.
    + apply pub_equiv_sym. eassumption.
    + eassumption.
  - (* IF; contra *)
    apply prefix_or_heads in Hds; inversion Hds.
  - (* IF; contra *)
     apply prefix_or_heads in Hds; inversion Hds.
  - (* If_F; analog to If *)
    remember (if not_zero (eval s be) then c2 else c1) as c5.
    assert(G : L ;; LA |-ct- c5).
    { subst c5. destruct (eval s be); assumption. }
    assert(Gds : prefix ds ds0 \/ prefix ds0 ds).
    { destruct Hds as [Hds | Hds]; apply prefix_cons in Hds; tauto. }
    subst c4 c5. erewrite noninterferent_exp in H10.
    + assert(GG: true = false -> pub_equiv LA m a2). (* <- only difference *)
      { intro Hc. discriminate. }
      specialize (IHHeval1 G _ Gds _ _ _ GG _ _ Heq _ H10).
      firstorder; congruence.
    + apply pub_equiv_sym. eassumption.
    + eassumption.
  - (* While *) eapply IHHeval1; try eassumption. repeat constructor; eassumption.
  - (* ALoad *) split4; eauto.
    destruct (L x) eqn:EqLx; simpl.
    + eapply pub_equiv_update_public; eauto.
      destruct b2' eqn:Eqb2'; simpl; [reflexivity |].
      apply can_flow_true_iff in H18.
      destruct H18 as [Hapub | Contra]; [| congruence].
      subst v v1 v2. eapply Haeq in Hapub; [| reflexivity]. rewrite Hapub.
      eapply noninterferent_exp in Heq; eauto. rewrite Heq.
      reflexivity.
    + eapply pub_equiv_update_secret; eauto.
  - (* ALoad_U *)
    split4; eauto.
    + destruct (L x) eqn:EqLx.
      * simpl. eapply pub_equiv_update_public; eauto.
      * eapply pub_equiv_update_secret; eauto.
    + apply prefix_or_heads in Hds. inversion Hds.
  - (* ALoad *)
    split4; eauto.
    + destruct (L x) eqn:EqLx.
      * eapply pub_equiv_update_public; eauto.
      * eapply pub_equiv_update_secret; eauto.
    + apply prefix_or_heads in Hds. inversion Hds.
  - (* ALoad_U *)
    split4; eauto.
    + destruct (L x) eqn:EqLx.
      * eapply pub_equiv_update_public; eauto.
      * eapply pub_equiv_update_secret; eauto.
    + apply prefix_or_heads in Hds. inversion Hds. reflexivity.
  - (* AStore *)
    split4; eauto. intro Hb2'.
    destruct (LA a) eqn:EqLAa.
    + eapply pub_equiv_update_public; eauto.
      destruct l eqn:Eql.
      * eapply noninterferent_exp in H19, H20; eauto. rewrite H19, H20.
        apply Haeq in Hb2'. apply Hb2' in EqLAa. rewrite EqLAa. reflexivity.
      * simpl in H21. discriminate.
    + eapply pub_equiv_update_secret; eauto.
  - (* AStore_U; contra *) apply prefix_or_heads in Hds. inversion Hds.
  - (* AStore; contra *) apply prefix_or_heads in Hds. inversion Hds.
  - (* AStore_U; contra *)
    split4; eauto.
    + intro contra. discriminate contra.
    + apply prefix_or_heads in Hds. inversion Hds. reflexivity.
Qed.

(** As a corollary we prove a more standard noninterference statement, where the
    two executions receive equal directions. The prefix assumption of the
    general statement then holds trivially, and its direction-equality
    conclusion becomes uninformative, so we drop it. Note that Generalization 1
    is still visible here: the final memories are only guaranteed to be publicly
    equivalent if no misspeculation happened, and as explained above there's no
    way around this without also masking stores, which here we don't do. *)

Corollary ct_well_typed_ideal_noninterferent :
  forall L LA c s1 s2 m1 m2 b s1' s2' m1' m2' b1' b2' os1 os2 ds,
    L ;; LA |-ct- c ->
    pub_equiv L s1 s2 ->
    (b = false -> pub_equiv LA m1 m2) ->
    L |-i <(s1, m1, b, ds)> =[ c ]=> <(s1', m1', b1', os1)> ->
    L |-i <(s2, m2, b, ds)> =[ c ]=> <(s2', m2', b2', os2)> ->
    pub_equiv L s1' s2' /\ b1' = b2' /\ (b1' = false -> pub_equiv LA m1' m2').
Proof.
  intros L LA c s1 s2 m1 m2 b s1' s2' m1' m2' b1' b2' os1 os2 ds
    Hwt Heq Haeq Heval1 Heval2.
  eapply ct_well_typed_ideal_noninterferent_general in Heval2; eauto; try tauto.
  left. apply prefix_refl.
Qed.

(** Another corollary of the general statement: two executions of the same
    well-typed command from publicly equivalent configurations consume the
    same directions -- if their direction lists are prefixes of a common
    list, they must be equal. This is used below in the sequence case, where
    the direction list could a priori be split differently in the two executions. *)
Corollary ct_well_typed_ideal_same_dirs :
  forall L LA s1 s2 m1 m2 b ds1 ds2 c s1' s2' m1' m2'
    b1 b2 os1 os2 ds1' ds2',
  ds2 ++ ds2' = ds1 ++ ds1' ->
  L ;; LA |-ct- c ->
  pub_equiv L s1 s2 ->
  (b = false -> pub_equiv LA m1 m2) ->
  L |-i <(s1, m1, b, ds1)> =[ c ]=> <(s1', m1', b1, os1)>  ->
  L |-i <(s2, m2, b, ds2)> =[ c ]=> <(s2', m2', b2, os2)> ->
  ds1 = ds2 /\ ds1' = ds2'.
Proof.
  intros L LA s1 s2 m1 m2 b ds1 ds2 c s1' s2' m1' m2' b1 b2 os1 os2 ds1' ds2'
    Hds Hwt Heq Haeq Heval1 Heval2.
  pose proof Hds as H.
  symmetry in H.
  apply app_eq_prefix in H.
  eapply ct_well_typed_ideal_noninterferent_general in H;
    [ | | | | apply Heval1 | apply Heval2]; try eassumption.
  - destruct H as [ _ [ _ [ _ H]]]. subst. split; [reflexivity|].
    apply app_inv_head in Hds. congruence.
Qed.

(** With these ingredients, proving that the ideal semantics enforces
    speculative constant-time is standard: as in our earlier proofs of CF
    security and CCT security, the sequence case is the interesting one,
    and it is handled using the noninterference corollaries above. *)

Theorem ideal_spec_ct_secure :
  forall L LA c s1 s2 m1 m2 b s1' s2' m1' m2' b1' b2' os1 os2 ds,
    L ;; LA |-ct- c ->
    pub_equiv L s1 s2 ->
    (b = false -> pub_equiv LA m1 m2) ->
    L |-i <(s1, m1, b, ds)> =[ c ]=> <(s1', m1', b1', os1)> ->
    L |-i <(s2, m2, b, ds)> =[ c ]=> <(s2', m2', b2', os2)> ->
    os1 = os2.
Proof.
  intros L LA c s1 s2 m1 m2 b s1' s2' m1' m2' b1' b2' os1 os2 ds
    Hwt Heq Haeq Heval1 Heval2.
  generalize dependent s2'. generalize dependent s2.
  generalize dependent m2'. generalize dependent m2.
  generalize dependent os2. generalize dependent b2'.
  induction Heval1; intros b2' os2' m2 Haeq m2' s2 Heq s2' Heval2;
    inversion Heval2; inversion Hwt; subst.
  - (* Skip *) reflexivity.
  - (* Skip *) reflexivity.
  - (* Seq *)
    eapply ct_well_typed_ideal_same_dirs in H1;
      [| | | | apply Heval1_1 | apply H5 ]; eauto.
    destruct H1 as [H1 H1']. subst.
    assert(NI1 : pub_equiv L s' s'0 /\ b' = b'0 /\
                 (b' = false -> pub_equiv LA m' m'0)).
    { eapply ct_well_typed_ideal_noninterferent;
        [ | | | eassumption | eassumption]; eauto. }
    destruct NI1 as [NI1eq [NIb NIaeq]]. subst.
    erewrite IHHeval1_2; [erewrite IHHeval1_1 | | | |];
      try reflexivity; try eassumption.
  - (* If *)
    f_equal.
    + f_equal. eapply noninterferent_exp in Heq; [| eassumption].
      rewrite Heq. reflexivity.
    + eapply IHHeval1; try eassumption; try (destruct (eval s be); eassumption).
      subst c c4. erewrite (noninterferent_exp Heq H14); eassumption.
  - (* If_F *)
    f_equal.
    + f_equal. eapply noninterferent_exp in Heq; [| eassumption].
      rewrite Heq. reflexivity.
    + eapply IHHeval1; try eassumption; try (destruct (eval s be); eassumption).
      * intro contra. discriminate contra.
      * subst c c4. erewrite noninterferent_exp; eassumption.
  - (* While *) eapply IHHeval1; eauto.
  - (* ALoad *) f_equal. f_equal. eapply noninterferent_exp; eassumption.
  - (* ALoad_U *) f_equal. f_equal. eapply noninterferent_exp; eassumption.
  - (* AStore *) f_equal. f_equal. eapply noninterferent_exp; eassumption.
  - (* AStore *) f_equal. f_equal. eapply noninterferent_exp; eassumption.
Qed.

(* ================================================================= *)
(** ** Correctness of sel_slh as a compiler from ideal to speculative semantics *)

(** We now prove that the ideal semantics correctly captures the programs
    produced by [sel_slh] when executed using the speculative semantics. We
    phrase this as a backwards compiler correctness proof for [sel_slh],
    which intuitively looks as follows:

    <(s,m,b,ds)> =[[ sel_slh L c ]]=> <(s',m',b',os)> ->
    L |-i <(s,m,b,ds)> =[[ c ]]=> <(msf!->s msf;s',m',b',os)>
*)

(** The [msf !-> s msf; s'] part accounts for the extra variable [msf]:
    the hardened program uses it for its misspeculation bookkeeping, while
    the ideal semantics tracks misspeculation directly in its bit [b], so it
    needs no variable for this. The two final states thus agree except on
    [msf], whose final value we reset to its initial one, since that is the
    value [msf] keeps throughout the ideal execution of [c]. *)

(** All results about [sel_slh] below assume that the original [c] doesn't
    already use the variable [msf] needed by the [sel_slh] translation.
    We define this using two recursive propositions: *)

Fixpoint e_unused (x:string) (e:exp) : Prop :=
  match e with
  | ANum n      => True
  | AId y       => y <> x
  | ABin _ e1 e2 => e_unused x e1 /\ e_unused x e2
  | <{b ? e1 : e2}> => e_unused x b /\ e_unused x e1 /\ e_unused x e2
  end.

Fixpoint unused (x:string) (c:com) : Prop :=
  match c with
  | <{{skip}}> => True
  | <{{y := e}}> => y <> x /\ e_unused x e
  | <{{c1; c2}}> => unused x c1 /\ unused x c2
  | <{{if be then c1 else c2 end}}> =>
      e_unused x be /\ unused x c1 /\ unused x c2
  | <{{while be do c end}}> => e_unused x be /\ unused x c
  | <{{y <- a[i]}}> => y <> x /\ e_unused x i
  | <{{a[i] <- e}}> => e_unused x i /\ e_unused x e
  end.

(** As a warm-up we prove that [sel_slh] properly updates the variable msf. *)

(** Proving this by induction on [com] or [spec_eval] leads to induction
    hypotheses that are not strong enough to prove the [Spec_While] case:
    the premise of [Spec_While] evaluates the loop unrolled to an [if] whose
    body contains the very same [while] command, so neither the command nor
    the evaluation derivation gets smaller. What does get smaller is the
    direction list, since executing the unrolled [if] consumes at least one
    direction. We therefore prove this lemma by induction on the combined
    [size] of the command [c] and the direction list [ds], which does
    decrease. The same issue will come back below in the backwards compiler
    correctness proof, which uses the same solution. *)

(** Setting up this induction requires a few ingredients. The first one is
    the [size] measure itself: *)

Fixpoint com_size (c:com) : nat :=
  match c with
  | <{{ c1; c2 }}> => 1 + (com_size c1) + (com_size c2)
  | <{{ if be then ct else cf end }}> => 1 + max (com_size ct) (com_size cf)
  | <{{ while be do cw end }}> => 1 + (com_size cw)
  | <{{ skip }}> => 1
  | _  => 1
  end.

Definition size (c:com) (ds:dirs) : nat := com_size c + length ds.

(** We prove a helpful induction principle on [size]: *)

Check measure_induction : forall (X : Type) (f : X -> nat) (A : X -> Type),
  (forall x : X, (forall y : X, f y < f x -> A y) -> A x) ->
  forall x : X, A x.

Lemma size_ind : forall P : com -> dirs -> Prop,
  (forall c ds,
    (forall c' ds', size c' ds' < size c ds -> P c' ds') ->
    P c ds) ->
  (forall c ds, P c ds).
Proof.
  intros.
  remember (fun c_ds => P (fst c_ds) (snd c_ds)) as P'.
  replace (P c ds) with (P' (c, ds)) by now rewrite HeqP'.
  eapply measure_induction with (f:=fun c_ds => size (fst c_ds) (snd c_ds)).
  intros. rewrite HeqP'.
  apply H. intros.
  remember (c', ds') as c_ds'.
  replace (P c' ds') with (P' c_ds') by now rewrite Heqc_ds', HeqP'.
  apply H0. now rewrite Heqc_ds'.
Qed.

(** The next ingredient is for discharging the size-decrease side conditions
    that [size_ind] generates at each use of the induction hypothesis. The
    following lemma reduces such conditions to separate, simpler conditions
    on the command size and on the direction list length: *)

Lemma size_decreasing: forall c1 ds1 c2 ds2,
  (com_size c1 < com_size c2 /\ length ds1 <= length ds2 ) \/
  (com_size c1 <= com_size c2 /\ length ds1 < length ds2) ->
  size c1 ds1 < size c2 ds2.
Proof.
  intros c1 ds1 c2 ds2 [[Hcom Hdir] | [Hcom Hdir]];
  unfold size; lia.
Qed.

(** Based on the [size_decreasing] lemma we then build a tactic that
    automatically solves subgoals of the form [size c' ds' < size c ds]:
    it tries both cases of the lemma and discharges the resulting
    arithmetic conditions using [lia]. *)

Ltac size_auto :=
  try ( apply size_decreasing; left; split; simpl;
        [| repeat rewrite length_app]; lia );
  try ( apply size_decreasing; right; split; simpl;
        [| repeat rewrite length_app]; lia);
  try ( apply size_decreasing; left; split; simpl;
        [auto | repeat rewrite length_app; lia] ).

(** To properly apply [size_ind], we need to state [sel_slh_flag] as a
    proposition of type [com -> dirs -> Prop], which we do as follows: *)

Definition sel_slh_flag_prop (c :com) (ds :dirs) :Prop :=
  forall L s m (b:bool) s' m' (b':bool) os,
  unused msf c ->
  s msf = (if b then 1 else 0) ->
  <(s, m, b, ds)> =[ sel_slh L c ]=> <(s', m', b', os)> ->
  s' msf = (if b' then 1 else 0).

(** With all the ingredients in place, we can now state and prove the
    warm-up lemma about [msf] using our [size] induction: *)

Lemma sel_slh_flag : forall c ds,
  sel_slh_flag_prop c ds.
Proof.
  eapply size_ind. unfold sel_slh_flag_prop.
  intros c ds IH L s m b s' m' b' os Hunused Hstb Heval.
  destruct c; simpl in *; try (now inversion Heval; subst; eauto).
  - (* Asgn *)
    inversion Heval; subst. rewrite t_update_neq; tauto.
  - (* Seq *)
    invert Heval.
    apply IH in H1; try tauto.
    + apply IH in H10; try tauto. size_auto.
    + size_auto.
  - (* IF *)
    invert Heval.
    + (* Spec_If *)
      destruct (eval s be) eqn:Eqnbe.
      * invert H10.
        invert H1.
        apply IH in H11; try tauto.
        { size_auto. }
        { rewrite t_update_eq. simpl. rewrite Eqnbe. assumption. }
      * (* analog to true case *)
        invert H10.
        invert H1.
        apply IH in H11.
        { auto. }
        { size_auto. }
        { tauto. }
        { rewrite t_update_eq. simpl. rewrite Eqnbe. assumption. }
    + (* Spec_If_F; analog to Spec_If case *)
      destruct (eval s be) eqn:Eqnbe.
      * invert H10.
        invert H1.
        apply IH in H11; try tauto.
        { size_auto. }
        { rewrite t_update_eq. simpl. rewrite Eqnbe. simpl. reflexivity. }
      * invert H10.
        invert H1.
        apply IH in H11; try tauto.
        { size_auto. }
        { rewrite t_update_eq. simpl. rewrite Eqnbe. simpl. reflexivity. }
  - (* While *)
      invert Heval.
      invert H1.
      invert H11.
      + (* non-speculative *)
        destruct (eval s be) eqn:Eqnbe.
        * invert H12.
          inversion H10; subst; simpl.
          rewrite t_update_eq, Eqnbe; simpl. assumption.
        * invert H12.
          assert(Hwhile: <(s'1, m'1, b'1, (ds0 ++ ds2)%list)>
              =[ sel_slh L <{{while be do c end}}> ]=>
              <(s', m', b', (os3++os2)%list)> ).
          { simpl. eapply Spec_Seq; eassumption. }
          apply IH in Hwhile; eauto.
          { size_auto. }
          { clear Hwhile; clear H11.
            invert H1.
            invert H2. simpl in H12.
            apply IH in H12; try tauto.
            - size_auto.
            - rewrite t_update_eq, Eqnbe; simpl. assumption. }
      + (* speculative; analog to non_speculative case *)
        destruct (eval s be) eqn:Eqnbe.
        * invert H12.
          assert(Hwhile: <(s'1, m'1, b'0, (ds0 ++ ds2)%list)>
              =[sel_slh L <{{while be do c end}}>]=>
              <(s', m', b', (os3++os2)%list )>).
          { simpl. eapply Spec_Seq; eassumption. }
          apply IH in Hwhile; eauto.
          { size_auto. }
          { clear Hwhile; clear H11.
            invert H1.
            invert H2. simpl in H12.
            apply IH in H12; try tauto.
            - size_auto.
            - rewrite t_update_eq, Eqnbe; simpl. reflexivity. }
        * invert H12.
          inversion H10; subst; simpl.
          rewrite t_update_eq, Eqnbe; simpl. reflexivity.
  - (* ALoad *)
    destruct (L x) eqn:Eqnbe.
    + invert Heval.
      invert H10.
      rewrite t_update_neq; [| tauto].
      inversion H1; subst;
      try (rewrite t_update_neq; [assumption| tauto]).
    + inversion Heval; subst;
      try (rewrite t_update_neq; [assumption| tauto]).
Qed.

(** We need a few more lemmas before we prove backwards compiler correctness.
    They all express that evaluation and ideal execution do not depend on the
    value of a variable that the program does not use. We will apply them to
    the variable [msf], to account for the [msf] updates that the hardened
    program performs but the source program does not: *)

Lemma eval_unused_update : forall X s n,
  (forall ae, e_unused X ae ->
    eval (X !-> n; s) ae = eval s ae).
Proof.
  intros X s n. induction ae; intros; simpl in *; try reflexivity.
  - rewrite t_update_neq; eauto.
  - destruct H.
    rewrite IHae1; [| tauto]. rewrite IHae2; [| tauto].
    reflexivity.
  - destruct H. destruct H0.
    rewrite IHae1, IHae2, IHae3; auto.
Qed.

Lemma ideal_unused_overwrite: forall L s m b ds c s' m' b' os X n,
  unused X c ->
  L |-i <(s, m, b, ds)> =[ c ]=> <(s', m', b', os)> ->
  L |-i <(X !-> n; s, m, b, ds)> =[ c ]=> <(X !-> n; s', m', b', os)>.
Proof.
  intros L s m b ds c s' m' b' os X n Hu H.
  induction H; simpl in Hu.
  - (* Skip *) econstructor.
  - (* Asgn *)
    rewrite t_update_permute; [| tauto].
    econstructor. rewrite eval_unused_update; tauto.
  - (* Seq *)
    econstructor.
    + apply IHideal_eval1; tauto.
    + apply IHideal_eval2; tauto.
  - (* If *)
    rewrite <- eval_unused_update with (X:=X) (n:=n); [| tauto].
    econstructor.
    rewrite eval_unused_update; [ | tauto].
    destruct (eval s be) eqn:D; apply IHideal_eval; tauto.
  - (* If_F *)
    rewrite <- eval_unused_update with (X:=X) (n:=n); [| tauto].
    econstructor.
    rewrite eval_unused_update; [ | tauto].
    destruct (eval s be) eqn:D; apply IHideal_eval; tauto.
  - (* While *)
    econstructor. apply IHideal_eval. simpl; tauto.
  - (* ALoad *)
    rewrite t_update_permute; [| tauto]. econstructor; [ | assumption].
    rewrite eval_unused_update; tauto.
  - (* ALoad_U *)
    rewrite t_update_permute; [| tauto]. econstructor; try assumption.
    rewrite eval_unused_update; tauto.
  - (* AStore *)
    econstructor; try assumption.
    + rewrite eval_unused_update; tauto.
    + rewrite eval_unused_update; tauto.
  - (* AStore_U *)
    econstructor; try assumption.
    + rewrite eval_unused_update; tauto.
    + rewrite eval_unused_update; tauto.
Qed.

Lemma ideal_unused_update : forall L s m b ds c s' m' b' os X n,
  unused X c ->
  L |-i <(X !-> n; s, m, b, ds)> =[ c ]=> <(X !-> n; s', m', b', os)> ->
  L |-i <(s, m, b, ds)> =[ c ]=> <(X !-> s X; s', m', b', os)>.
Proof.
  intros L s m b ds c s' m' b' os X n Hu Heval.
  eapply ideal_unused_overwrite with (X:=X) (n:=(s X)) in Heval; [| assumption].
  repeat rewrite t_update_shadow in Heval.
  rewrite t_update_same in Heval. assumption.
Qed.

Lemma ideal_unused_update_rev : forall L s m b ds c s' m' b' os X n,
  unused X c ->
  L |-i <(s, m, b, ds)> =[ c ]=> <(X!-> s X; s', m', b', os)> ->
  L |-i <(X !-> n; s, m, b, ds)> =[ c ]=> <(X !-> n; s', m', b', os)>.
Proof.
  intros L s m b ds c s' m' b' os X n Hu H.
  eapply ideal_unused_overwrite in H; [| eassumption].
  rewrite t_update_shadow in H. eassumption.
Qed.

(** The backwards compiler correctness proof also uses [size_ind], for the
    same reason as before. In each case it computes the code that [sel_slh]
    emits for the given source construct, and inverts the execution of that
    code into executions of its pieces, from which it reassembles an ideal
    execution of the source program. The premise
    [s msf = (if b then 1 else 0)] is the key invariant that [msf] correctly
    mirrors the misspeculation bit: it makes the masking performed by the
    hardened program ([(msf <> 0) ? 0 : x]) coincide with the masking built
    into the ideal semantics. Whenever, because of sequencing, a first part
    of the hardened program has already executed, the warm-up lemma
    [sel_slh_flag] re-establishes this invariant in the intermediate state,
    so that the induction hypothesis can be applied to the rest of the program. *)

Definition sel_slh_compiler_correctness_prop (c:com) (ds:dirs) : Prop :=
  forall L s m (b: bool) s' m' b' os,
  unused msf c ->
  s msf = (if b then 1 else 0) ->
  <(s, m, b, ds)> =[ sel_slh L c ]=> <(s', m', b', os)> ->
  L |-i <(s, m, b, ds)> =[ c ]=> <(msf !-> s msf; s', m', b', os)>.

Lemma sel_slh_compiler_correctness : forall c ds,
  sel_slh_compiler_correctness_prop c ds.
Proof.
  apply size_ind. unfold sel_slh_compiler_correctness_prop.
  intros c ds IH L s m b s' m' b' os Hunused Hstb Heval.
  destruct c; simpl in *; invert Heval;
  try (destruct (L x); discriminate).
  - (* Skip *)
    rewrite t_update_same. apply Ideal_Skip.
  - (* Asgn *)
    rewrite t_update_permute; [| tauto].
    rewrite t_update_same.
    constructor. reflexivity.
  - (* Seq *)
    eapply Ideal_Seq.
    + apply IH in H1; try tauto.
      * eassumption.
      * size_auto.
    + apply sel_slh_flag in H1 as Hstb'0; try tauto.
      apply IH in H10; try tauto.
      * eapply ideal_unused_update_rev; try tauto.
      * size_auto.
  (* IF *)
  - (* non-speculative *)
    destruct (eval s be) eqn:Eqnbe; invert H10; invert H1; simpl in *.
    + apply IH in H11; try tauto.
      * rewrite <- Eqnbe. apply Ideal_If. rewrite Eqnbe in *.
        rewrite t_update_same in H11. apply H11.
      * size_auto.
      * rewrite t_update_eq. rewrite Eqnbe. assumption.
    + (* analog to false case *)
      apply IH in H11; try tauto.
      * rewrite <- Eqnbe. apply Ideal_If. rewrite Eqnbe in *.
        rewrite t_update_same in H11. apply H11.
      * size_auto.
      * rewrite t_update_eq. rewrite Eqnbe. assumption.
  - (* speculative *)
    destruct (eval s be) eqn:Eqnbe; inversion H10; inversion H1;
    subst; simpl in *; clear H10; clear H1; rewrite Eqnbe in H11.
    + rewrite <- Eqnbe. apply Ideal_If_F. rewrite Eqnbe. apply IH in H11; try tauto.
      * rewrite t_update_eq in H11.
        apply ideal_unused_update in H11; try tauto.
      * size_auto.
    + (* analog to false case *)
      rewrite <- Eqnbe. apply Ideal_If_F. rewrite Eqnbe. apply IH in H11; try tauto.
      * rewrite t_update_eq in H11.
        apply ideal_unused_update in H11; try tauto.
      * size_auto.
  - (* While *)
    eapply Ideal_While.
    invert H1.
    invert H11; simpl in *.
    + (* non-speculative *)
      assert(Lnil: os2 = [] /\ ds2 = []).
      { inversion H10; subst; eauto. }
      destruct Lnil; subst; simpl.
      apply Ideal_If.
      destruct (eval s be) eqn:Eqnbe.
      * invert H12.
        invert H10; simpl in *.
        rewrite Eqnbe. repeat rewrite t_update_same.
        apply Ideal_Skip.
      * invert H12.
        invert H1.
        invert H2; simpl in *.
        assert(Hwhile: <(s'1, m'1, b'1, ds2)>
          =[ sel_slh L <{{while be do c end}}> ]=> <(s', m', b', os2)> ).
        { simpl. replace ds2 with (ds2 ++ [])%list
            by (rewrite app_nil_r; reflexivity).
          replace os2 with (os2 ++ [])%list by (rewrite app_nil_r; reflexivity).
          eapply Spec_Seq; eassumption. }
        repeat rewrite app_nil_r. eapply Ideal_Seq.
        { rewrite Eqnbe in H13. rewrite t_update_same in H13.
          apply IH in H13; try tauto.
          - eassumption.
          - size_auto. }
        { apply IH in Hwhile; auto.
          - eapply ideal_unused_update_rev; eauto.
          - size_auto.
          - apply sel_slh_flag in H13; try tauto.
            rewrite t_update_eq. rewrite Eqnbe. assumption. }
    + (* speculative; analog to non_speculative *)
      assert(Lnil: os2 = [] /\ ds2 = [] /\ b' = true).
      { inversion H10; subst; eauto. }
      destruct Lnil as [? [? ?]]; subst; simpl.
      apply Ideal_If_F.
      destruct (eval s be) eqn:Eqnbe.
      * invert H12.
        invert H1.
        invert H2; simpl in *.
        assert(Hwhile: <(s'1, m'1, b', ds2)>
          =[ sel_slh L <{{while be do c end}}> ]=> <(s', m', true, os2)> ).
        { simpl. replace ds2 with (ds2 ++ [])%list
            by (rewrite app_nil_r; reflexivity).
          replace os2 with (os2 ++ [])%list by (rewrite app_nil_r; reflexivity).
          eapply Spec_Seq; eassumption. }
        repeat rewrite app_nil_r. eapply Ideal_Seq.
        { rewrite Eqnbe in H13.
          apply IH in H13; try tauto.
          - rewrite t_update_eq in H13.
            apply ideal_unused_update in H13; [| tauto].
            eassumption.
          - size_auto. }
        { apply IH in Hwhile; auto.
          - rewrite Eqnbe in H13.
            apply IH in H13; try tauto.
            + apply ideal_unused_update_rev; eauto.
            + size_auto.
          - size_auto.
          - apply sel_slh_flag in H13; try tauto.
            rewrite Eqnbe. rewrite t_update_eq. reflexivity. }
      * invert H12.
        invert H10; simpl in *.
        rewrite Eqnbe. rewrite t_update_shadow. rewrite t_update_same.
        apply Ideal_Skip.
  (* ALoad *)
  - (* Spec_ALoad; public *)
    destruct (L x) eqn:Heq; try discriminate H.
    injection H; intros; subst; clear H.
    inversion H1; clear H1; subst. rewrite <- app_nil_r in *.
    inversion H0; clear H0; subst; simpl in *.
    * (* Ideal_ALoad *)
      rewrite t_update_neq; [| tauto]. rewrite Hstb.
      rewrite t_update_shadow. rewrite t_update_permute; [| tauto].
      rewrite t_update_eq. simpl.
      rewrite <- Hstb at 1. rewrite t_update_same.
      replace (not_zero (bool_to_nat (negb (not_zero
        (bool_to_nat ((if b' then 1 else 0) =? 0)%nat)) || not_zero 0)))
        with (b' && (L x =? public))
          by (rewrite Heq; destruct b'; simpl; reflexivity).
        eapply Ideal_ALoad; eauto.
    * (* Ideal_ALoad_U *)
      rewrite t_update_neq; [| tauto]. rewrite Hstb.
      rewrite t_update_shadow. rewrite t_update_permute; [| tauto].
      simpl. rewrite <- Hstb at 1. rewrite t_update_same.
      replace (x !-> 0; s)
        with (x !-> if L x =? public then 0 else (m' a').[i']; s)
        by (rewrite Heq; reflexivity).
      eapply Ideal_ALoad_U; eauto.
  - (* Spec_ALoad; secret*)
    destruct (L x) eqn:Heq; try discriminate H. inversion H; clear H; subst.
    rewrite t_update_permute; [| tauto]. rewrite t_update_same.
    replace (x !-> (m' a).[eval s i]; s)
      with (x !-> if b' && (L x =? public) then 0 else (m' a).[eval s i]; s)
        by (rewrite Heq; destruct b'; reflexivity).
    eapply Ideal_ALoad; eauto.
  - (* Spec_ALoad_U *)
    destruct (L x) eqn:Heq; try discriminate H. inversion H; clear H; subst.
    rewrite t_update_permute; [| tauto]. rewrite t_update_same.
    replace (x !-> (m' a').[i']; s)
      with (x !-> if L x =? public then 0 else (m' a').[i']; s)
        by (rewrite Heq; reflexivity).
    eapply Ideal_ALoad_U; eauto.
  (* AStore *)
  - (* Spec_AStore *)
    rewrite t_update_same. apply Ideal_AStore; tauto.
  - (* Spec_AStore_U *)
    rewrite t_update_same. apply Ideal_AStore_U; tauto.
Qed.

(* ================================================================= *)
(** ** Speculative constant-time security for Selective SLH *)

(** Finally, we use compiler correctness and [spec_ct_secure] for the ideal
    semantics to prove [spec_ct_secure] for [sel_slh]. *)

Theorem sel_slh_spec_ct_secure :
  forall L LA c s1 s2 m1 m2 s1' s2' m1' m2' b1' b2' os1 os2 ds,
  L ;; LA |-ct- c ->
  unused msf c ->
  s1 msf = 0 ->
  s2 msf = 0 ->
  pub_equiv L s1 s2 ->
  pub_equiv LA m1 m2 ->
  <(s1, m1, false, ds)> =[ sel_slh L c ]=> <(s1', m1', b1', os1)> ->
  <(s2, m2, false, ds)> =[ sel_slh L c ]=> <(s2', m2', b2', os2)> ->
  os1 = os2.
Proof.
  intros L LA c s1 s2 m1 m2 s1' s2' m1' m2' b1' b2' os1 os2 ds
    Hwt Hunused Hs1b Hs2b Hequiv Haequiv Heval1 Heval2.
  eapply sel_slh_compiler_correctness in Heval1; try assumption.
  eapply sel_slh_compiler_correctness in Heval2; try assumption.
  eapply ideal_spec_ct_secure; eauto.
Qed.

(* ================================================================= *)
(** ** This Selective SLH formalization is already research-level *)

(** What we did above was to use ideas from this course to mechanize the core of
    a research paper: Spectre Declassified [Shivakumar et al 2023a] (in Bib.v).

    This mechanization served as the base for two more recent papers that use
    stronger SLH variants to improve security of _arbitrary_ programs (no CCT):
    - Formalized a stronger SLH variant [Zhang et al 2023] (in Bib.v) and proved
      relative security: any hardened program running with speculation must not
      leak more than what the source program leaks sequentially.  Pervasive
      hardening can make things slow though, so being selective still helps
      [Baumann et al 2025] (in Bib.v).
    - Also used SLH as a base for protection against speculative control-flow
      hijacking attacks (Spectre BTB and RSB) [Baumann et al 2026] (in Bib.v). *)

(* ################################################################# *)
(** * Monadic interpreter for speculative semantics (optional; text missing) *)

Module SpecCTInterpreter.

(** Since manually constructing evaluation derivations for the proofs of
    examples is very time consuming, we introduce a sound monadic interpreter,
    which can be used to simplify the proofs of the examples. *)

(** The Rocq development below is complete, but the text about it is missing.
    Readers not familiar with monadic interpreters can safely skip this section. *)

Definition prog_st : Type :=  state * mem * bool * dirs * obs.

Inductive output_st (A : Type): Type :=
| OST_Error : output_st A
| OST_OutOfFuel : output_st A
| OST_Finished : A -> prog_st -> output_st A.

Definition evaluator (A : Type): Type := prog_st -> (output_st A).
Definition interpreter : Type := evaluator unit.

Definition ret {A : Type} (value : A) : evaluator A :=
  fun (pst: prog_st) => OST_Finished A value pst.

Definition bind {A : Type} {B : Type}
    (e : evaluator A) (f : A -> evaluator B): evaluator B :=
  fun (pst: prog_st) =>
    match e pst with
    | OST_Finished _ value (s', m', b', ds', os1)  =>
        match (f value) (s', m', b', ds', os1) with
        | OST_Finished _ value (s'', m'', b'', ds'', os2) =>
            OST_Finished B value (s'', m'', b'', ds'', os2)
        | ret => ret
        end
    | OST_Error _ => OST_Error B
    | OST_OutOfFuel _ => OST_OutOfFuel B
    end.

Notation "e >>= f" := (bind e f) (at level 58, left associativity).
Notation "e >> f" := (bind e (fun _ => f)) (at level 58, left associativity).

(* ================================================================= *)
(** ** Helper functions for individual instructions *)

Definition finish : interpreter := ret tt.

Definition get_var (name : string): evaluator nat :=
  fun (pst : prog_st) =>
    let
      '(s, _, _, _, _) := pst
    in
      ret (s name) pst.

Definition set_var (name : string) (value : nat) : interpreter :=
  fun (pst: prog_st) =>
    let
      '(s, m, b, ds, os) := pst
    in
      let
        new_st := (name !-> value; s)
      in
        finish (new_st, m, b, ds, os).

Definition get_arr (name : string): evaluator (list nat) :=
  fun (pst: prog_st) =>
    let
      '(_, m, _, _, _) := pst
    in
      ret (m name) pst.

Definition set_arr (name : string) (value : list nat) : interpreter :=
  fun (pst : prog_st) =>
    let '(s, m, b, ds, os) := pst in
    let new_m := (name !-> value ; m) in
    finish (s, new_m, b, ds, os).

Definition start_speculating : interpreter :=
  fun (pst : prog_st) =>
    let '(s, m, _, ds, os) := pst in
    finish (s, m, true, ds, os).

Definition is_speculating : evaluator bool :=
  fun (pst : prog_st) =>
    let '(_, _, b, _, _) := pst in
    ret b pst.

Definition eval_exp (a : exp) : evaluator nat :=
  fun (pst: prog_st) =>
    let '(s, _, _, _, _) := pst in
    let v := eval s a in
    ret v pst.

Definition raise_error : interpreter :=
  fun _ => OST_Error unit.

Definition observe (o : observation) : interpreter :=
  fun (pst : prog_st) =>
    let '(s, m, b, ds, os) := pst in
    OST_Finished unit tt (s, m, b, ds, (os ++ [o])%list).

Definition fetch_direction : evaluator (option direction) :=
  fun (pst : prog_st) =>
    let '(s, m, b, ds, os) := pst in
    match ds with
    | d::ds' =>
        ret (Some d) (s, m, b, ds', os)
    | [] => ret None (s, m, b, [], os)
    end.

(* ================================================================= *)
(** ** The actual speculative interpreter *)

Fixpoint spec_eval_engine_aux (fuel : nat) (c : com) : interpreter :=
  match fuel with
  | O => fun _ => OST_OutOfFuel unit
  | S fuel =>
    match c with
    | <{ skip }> => finish
    | <{ x := e }> => eval_exp e >>= fun v => set_var x v
    | <{ c1 ; c2 }> =>
        spec_eval_engine_aux fuel c1 >>
        spec_eval_engine_aux fuel c2
    | <{ if be then ct else cf end }> =>
        eval_exp be >>= fun bool_value =>
          observe (OBranch (not_zero bool_value)) >> fetch_direction >>=
        fun dop =>
          match dop with
          | Some DStep =>
              if not_zero bool_value then spec_eval_engine_aux fuel ct
              else spec_eval_engine_aux fuel cf
          | Some DForce =>
              start_speculating >>
              if not_zero bool_value then spec_eval_engine_aux fuel cf
              else spec_eval_engine_aux fuel ct
          | _ => raise_error
          end
    | <{ while be do c end }> =>
        spec_eval_engine_aux fuel <{if be then (c; while be do c end) else skip end}>
    | <{ x <- a[ie] }> =>
        eval_exp ie >>= fun i => observe (OALoad a i) >> get_arr a >>=
        fun arr_a => is_speculating >>= fun b => fetch_direction >>=
        fun dop =>
          match dop with
          | Some DStep =>
              if (i <? List.length arr_a)%nat then set_var x (arr_a.[i])
              else raise_error
          | Some (DLoad a' i') =>
              get_arr a' >>= fun arr_a' =>
                if negb (i <? List.length arr_a)%nat
                   && (i' <? List.length arr_a')%nat && b then
                  set_var x (arr_a'.[i'])
                else raise_error
          | _ => raise_error
          end
    | <{ a[ie] <- e }> =>
        eval_exp ie >>= fun i => observe (OAStore a i) >> get_arr a >>=
        fun arr_a => eval_exp e >>= fun n => is_speculating >>=
        fun b => fetch_direction >>=
        fun dop =>
          match dop with
          | Some DStep =>
              if (i <? List.length arr_a)%nat then set_arr a (arr_a.[i <- n])
              else raise_error
          | Some (DStore a' i') =>
              get_arr a' >>= fun arr_a' =>
                if negb (i <? List.length arr_a)%nat
                   && (i' <? List.length arr_a')%nat && b then
                  set_arr a' (arr_a'.[i' <- n])
                else raise_error
          | _ => raise_error
          end
    end
end.

Definition compute_fuel (c :com) (ds :dirs) : nat :=
  2 +
    match ds with
    | [] => com_size c
    | _ => length ds * com_size c
    end.

Definition spec_eval_engine (c : com) (s : state) (m : mem) (b : bool) (ds : dirs)
      : option (state * mem * bool * obs) :=
    match spec_eval_engine_aux (compute_fuel c ds) c (s, m, b, ds, []) with
    | OST_Finished _ _ (s', m', b', ds', os) =>
        if ((length ds') =? 0)%nat then Some (s', m', b', os)
        else None
    | _ => None
    end.

(* ================================================================= *)
(** ** Soundness of the interpreter *)

Lemma ltb_reflect : forall n m :nat,
  reflect (n < m) (n <? m)%nat.
Proof.
  intros n m. apply iff_reflect. rewrite ltb_lt. reflexivity.
Qed.

Lemma eqb_reflect: forall n m :nat,
  reflect (n = m ) (n =? m)%nat.
Proof.
  intros n m. apply iff_reflect. rewrite eqb_eq. reflexivity.
Qed.

Lemma spec_eval_engine_aux_sound : forall n c s m b ds os s' m' b' ds' os' u,
  spec_eval_engine_aux n c (s, m, b, ds, os)
    = OST_Finished unit u (s', m', b', ds', os') ->
  (exists dsn osn,
  (dsn++ds')%list = ds /\ (os++osn)%list = os' /\
      <(s, m, b, dsn)> =[ c ]=> <(s', m', b', osn)> ).
Proof.
  induction n as [| n' IH]; intros c s m b ds os s' m' b' ds' os' u Haux;
  simpl in Haux; [discriminate |].
  destruct c as [| X e | c1 c2 | be ct cf | be cw | X a ie | a ie e ] eqn:Eqnc;
  unfold ">>=" in Haux; simpl in Haux.
  - (* Skip *)
    inversion Haux; subst.
    exists []; exists []; split;[| split].
    + reflexivity.
    + rewrite app_nil_r. reflexivity.
    + apply Spec_Skip.
  - (* Asgn *)
    simpl in Haux. inversion Haux; subst.
    exists []; exists []; split;[| split].
    + reflexivity.
    + rewrite app_nil_r. reflexivity.
    + apply Spec_Asgn. reflexivity.
  - destruct (spec_eval_engine_aux _ c1 _) eqn:Hc1;
    try discriminate; simpl in Haux.
    destruct p as [[[[stm mm] bm] dsm] osm]; simpl in Haux.
    destruct (spec_eval_engine_aux _ c2 _) eqn:Hc2;
    try discriminate; simpl in Haux.
    destruct p as [[[[s'' m''] bt] dst] ost]; simpl in Haux.
    apply IH in Hc1. destruct Hc1 as [ds1 [ os1 [Hds1 [Hos1 Heval1]]]].
    apply IH in Hc2. destruct Hc2 as [ds2 [ os2 [Hds2 [Hos2 Heval2]]]].
    inversion Haux; subst. exists (ds1++ds2)%list; exists (os1++os2)%list;
    split; [| split].
    + rewrite <- app_assoc. reflexivity.
    + rewrite <- app_assoc. reflexivity.
    + eapply Spec_Seq; eauto.
  - (* IF *)
    destruct ds as [| d ds_tl] eqn:Eqnds; simpl in Haux; try discriminate.
    destruct d eqn:Eqnd; try discriminate; simpl in Haux.
    + (* DStep *)
      destruct (eval s be) eqn:Eqnbe.
      * unfold obs, dirs, not_zero in Haux. simpl in Haux.
        destruct (spec_eval_engine_aux n' cf
                    (s, m, b, ds_tl, (os ++ [OBranch false])%list))
          eqn:Hcf;
        try discriminate; simpl in Haux.
        destruct p as [[[[s'' m''] bt] dst] ost]; simpl in Haux.
        inversion Haux; subst. apply IH in Hcf.
        destruct Hcf as [dst [ ost [Hds [Hos Heval]]]].
        exists (DStep :: dst); exists ([OBranch false]++ost)%list; split;[| split].
        { simpl. rewrite Hds. reflexivity. }
        { rewrite app_assoc. rewrite Hos. reflexivity. }
        { erewrite <- not_zero_eval_O; [| eassumption].
          apply Spec_If. rewrite Eqnbe. apply Heval. }
      * unfold obs, dirs, not_zero in Haux. simpl in Haux.
        destruct (spec_eval_engine_aux n' ct
                    (s, m, b, ds_tl, (os ++ [OBranch true])%list))
          eqn:Hct;
        try discriminate; simpl in Haux.
        destruct p as [[[[s'' m''] bt] dst] ost]; simpl in Haux.
        inversion Haux; subst. apply IH in Hct.
        destruct Hct as [dst [ ost [Hds [Hos Heval]]]].
        exists (DStep :: dst); exists ([OBranch true]++ost)%list; split;[| split].
        { simpl. rewrite Hds. reflexivity. }
        { rewrite app_assoc. rewrite Hos. reflexivity. }
        { erewrite <- not_zero_eval_S; [| eassumption].
          apply Spec_If. rewrite Eqnbe. apply Heval. }
    + (* DForce *)
      destruct (eval s be) eqn:Eqnbe.
      * unfold obs, dirs, not_zero in Haux. simpl in Haux.
        destruct (spec_eval_engine_aux n' ct
                    (s, m, true, ds_tl, (os ++ [OBranch false])%list))
          eqn:Hcf;
        try discriminate; simpl in Haux.
        destruct p as [[[[s'' m''] bt] dst] ost]; simpl in Haux.
        inversion Haux; subst. apply IH in Hcf.
        destruct Hcf as [dst [ ost [Hds [Hos Heval]]]].
        assert (b' = true)
          by (eapply speculation_bit_monotonic; [apply Heval|reflexivity]).
        subst b'.
        exists (DForce :: dst); exists ([OBranch false]++ost)%list; split;[| split].
        { simpl. rewrite Hds. reflexivity. }
        { rewrite app_assoc. rewrite Hos. reflexivity. }
        { erewrite <- not_zero_eval_O; [| eassumption].
          apply Spec_If_F. rewrite Eqnbe. apply Heval. }
      * unfold obs, dirs, not_zero in Haux. simpl in Haux.
        destruct (spec_eval_engine_aux n' cf
                    (s, m, true, ds_tl, (os ++ [OBranch true])%list))
          eqn:Hct; try discriminate; simpl in Haux.
        destruct p as [[[[s'' m''] bt] dst] ost]; simpl in Haux.
        inversion Haux; subst. apply IH in Hct.
        destruct Hct as [dst [ ost [Hds [Hos Heval]]]].
        assert (b' = true)
          by (eapply speculation_bit_monotonic; [apply Heval|reflexivity]).
        subst b'.
        exists (DForce :: dst); exists ([OBranch true]++ost)%list; split;[| split].
        { simpl. rewrite Hds. reflexivity. }
        { rewrite app_assoc. rewrite Hos. reflexivity. }
        { replace ([OBranch true]++ost)%list
            with ([OBranch (not_zero (eval s be))]++ost)%list
            by (erewrite not_zero_eval_S; [reflexivity|eassumption]).
          apply Spec_If_F. rewrite Eqnbe. apply Heval. }
  - (* While *)
    apply IH in Haux. destruct Haux as [dst [ ost [Hds [Hos Heval]]]].
    exists dst; exists ost; split; [| split]; eauto.
  - (* ALoad *)
    destruct ds as [| d ds_tl] eqn:Eqnds; simpl in Haux; try discriminate.
    destruct d eqn:Eqnd; try discriminate; simpl in Haux.
    + (* DStep *)
      destruct (eval s ie <? Datatypes.length (m a))%nat eqn:Eqnindex;
        try discriminate.
      destruct (observe (OALoad a (eval s ie)) (s, m, b, ds_tl, os))
        eqn:Eqbobs; try discriminate;
      simpl in Haux. inversion Haux; subst.
      eexists [DStep]; eexists [OALoad a (eval s ie)];
        split;[| split]; try reflexivity.
      eapply Spec_ALoad; eauto.
      destruct (ltb_reflect (eval s ie) (length (m' a))) as [Hlt | Hgeq].
      * apply Hlt.
      * discriminate.
    + (* DForce *)
      destruct (negb (eval s ie <? Datatypes.length (m a))%nat) eqn:Eqnindex1;
      destruct ((i <? Datatypes.length (m a0))%nat) eqn:Eqnindex2;
      destruct b eqn:Eqnb; try discriminate; simpl in Haux. inversion Haux; subst.
      eexists [DLoad a0 i ]; eexists [OALoad a (eval s ie)];
        split;[| split]; try reflexivity.
      eapply Spec_ALoad_U; eauto.
      * destruct (ltb_reflect (eval s ie) (length (m' a))) as [Hlt | Hgeq].
        { discriminate. }
        { apply not_lt in Hgeq. apply Hgeq. }
      * destruct (ltb_reflect i (length (m' a0))) as [Hlt | Hgeq].
        { apply Hlt. }
        { discriminate. }
  - (* AStore *)
  destruct ds as [| d ds_tl] eqn:Eqnds; simpl in Haux; try discriminate.
  destruct d eqn:Eqnd; try discriminate; simpl in Haux.
  + (* DStep *)
    destruct ((eval s ie <? Datatypes.length (m a))%nat) eqn:Eqnindex;
      try discriminate.
    destruct (observe (OAStore a (eval s ie)) (s, m, b, ds_tl, os))
      eqn:Eqbobs; try discriminate;
    simpl in Haux. inversion Haux; subst.
    eexists [DStep]; eexists [OAStore a (eval s' ie)];
      split;[| split]; try reflexivity.
    eapply Spec_AStore; eauto.
    destruct (ltb_reflect (eval s' ie) (length (m a))) as [Hlt | Hgeq].
    * apply Hlt.
    * discriminate.
  + (* DForce *)
    destruct  (negb (eval s ie <? Datatypes.length (m a))%nat) eqn:Eqnindex1;
    destruct (i <? Datatypes.length (m a0))%nat eqn:Eqnindex2;
    destruct b eqn:Eqnb; try discriminate; simpl in Haux. inversion Haux; subst.
    eexists [DStore a0 i]; eexists [OAStore a (eval s' ie)];
      split;[| split]; try reflexivity.
    eapply Spec_AStore_U; eauto.
    * destruct (ltb_reflect (eval s' ie) (length (m a))) as [Hlt | Hgeq].
      { discriminate. }
      {  apply not_lt in Hgeq. apply Hgeq. }
    * destruct (ltb_reflect i (length (m a0))) as [Hlt | Hgeq].
      { apply Hlt. }
      { discriminate. }
Qed.

Theorem spec_eval_engine_sound: forall c s m b ds s' m' b' os',
  spec_eval_engine c s m b ds = Some (s', m', b', os') ->
  <(s, m, b, ds)> =[ c ]=> <(s', m', b', os')> .
Proof.
  intros c s m b ds s' m' b' os' Hengine.
  unfold spec_eval_engine in Hengine.
  destruct (spec_eval_engine_aux _ c _) eqn:Eqnaux;
  try discriminate. destruct p as [[[[s'' m''] bt] dst] ost].
  destruct ((Datatypes.length dst =? 0)%nat) eqn:Eqnds; try discriminate.
  apply spec_eval_engine_aux_sound in Eqnaux.
  destruct Eqnaux as [dsn [osn [Hdsn [Hosn Heval]]]].
  inversion Hengine; subst. rewrite app_nil_l.
  destruct (eqb_reflect (length dst) 0) as [Heq | Hneq].
  + apply length_zero_iff_nil in Heq. rewrite Heq. rewrite app_nil_r. apply Heval.
  + discriminate.
Qed.

(* ================================================================= *)
(** ** Back to showing that our example is not speculative constant-time *)

(** For exploiting [spec_insecure_prog_2], the attacker uses [DForce] to enter a
    fourth loop iteration, whose out-of-bounds load [Z <- AP[3]] is steered by
    the [DLoad AS 3] direction into reading the secret [AS.[3]]. This value
    flows into [X], so the observation traces of the two executions below differ
    in the final branch on [X <= 5]. *)

Print spec_insecure_prog_2. (* [[
= <{{ X := 0;
      Y := 0;
      while Y < 3 do
        Z <- AP[Y];
        X := X + Z;
        Y := Y + 1
      end;
      if X <= 5 then X := 5 else skip end }}> ]]
*)

Example spec_insecure_prog_2_is_spec_insecure :
  ~(spec_ct_secure LXYZpub LAPpub spec_insecure_prog_2).
Proof.
  unfold spec_insecure_prog_2.
  remember (__ !-> 0) as s.
  remember (AP!-> [0;1;2]; AS !-> [0;0;0;0]; __ !-> []) as m1.
  remember (AP!-> [0;1;2]; AS !-> [4;5;6;7]; __ !-> []) as m2.
  remember ([DStep; DStep; DStep; DStep; DStep; DStep; DForce;
             DLoad AS 3; DStep; DStep]) as ds.
  (* the two traces differ only in the last branch observation: *)
  remember ([OBranch true; OALoad AP 0; OBranch true; OALoad AP 1;
             OBranch true; OALoad AP 2; OBranch false; OALoad AP 3;
             OBranch false; OBranch true]) as os1.
  remember ([OBranch true; OALoad AP 0; OBranch true; OALoad AP 1;
             OBranch true; OALoad AP 2; OBranch false; OALoad AP 3;
             OBranch false; OBranch false]) as os2.
  intros Hsecure.
  (* this time we compute the two executions using the interpreter *)
  assert (Heval1 : exists s1' m1' bt1,
    <(s, m1, false, ds)> =[ spec_insecure_prog_2 ]=> <(s1', m1', bt1, os1)>).
  { eexists; eexists; eexists. apply spec_eval_engine_sound.
    unfold spec_insecure_prog_2, spec_eval_engine; subst; simpl; reflexivity. }
  assert (Heval2 : exists s2' m2' bt2,
    <(s, m2, false, ds)> =[ spec_insecure_prog_2 ]=> <(s2', m2', bt2, os2)>).
  { eexists; eexists; eexists. apply spec_eval_engine_sound.
    unfold spec_insecure_prog_2, spec_eval_engine; subst; simpl; reflexivity. }
  destruct Heval1 as [s1' [m1' [bt1 Heval1]]].
  destruct Heval2 as [s2' [m2' [bt2 Heval2]]].
  eapply Hsecure in Heval1.
  - eapply Heval1 in Heval2. subst. discriminate Heval2.
  - apply pub_equiv_refl.
  - subst. apply pub_equiv_update_public; auto.
    apply pub_equiv_update_secret; auto.
    apply pub_equiv_refl.
Qed.

(** How did we come up with the two observation traces used in this proof?
    We did not have to guess: we simply asked the interpreter, using the
    [Compute] command (here keeping only the observations from the result): *)

Compute (match spec_eval_engine spec_insecure_prog_2
    (__ !-> 0) (AP!-> [0;1;2]; AS !-> [4;5;6;7]; __ !-> []) false
    [DStep; DStep; DStep; DStep; DStep; DStep; DForce;
     DLoad AS 3; DStep; DStep]
  with Some (_, _, _, os) => os | None => [] end).
(** As a result we get:

    [OBranch true; OALoad AP 0; OBranch true; OALoad AP 1;
    OBranch true; OALoad AP 2; OBranch false; OALoad AP 3;
    OBranch false; OBranch false]
*)

(** In fact, spelling out the two observation traces is not needed for the proof
    to go through; it just makes the proof more explicit for the reader. We
    could instead have kept the two traces existentially quantified, like the
    final states, and let the interpreter compute them inside the proof,
    concluding from the computed results that they are different. That proof
    would be shorter, but it would no longer show the reader what the attacker
    observes, and where that differs between the two executions. *)

End SpecCTInterpreter.

(* 2026-08-23 16:10 *)
