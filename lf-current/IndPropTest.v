Set Warnings "-notation-overridden,-parsing".
From Stdlib Require Export String.
From LF Require Import IndProp.

Parameter MISSING: Type.

Module Check.

Ltac check_type A B :=
    match type of A with
    | context[MISSING] => idtac "Missing:" A
    | ?T => first [unify T B; idtac "Type: ok" | idtac "Type: wrong - should be (" B ")"]
    end.

Ltac print_manual_grade A :=
    match eval compute in A with
    | Some (_ ?S ?C) =>
        idtac "Score:"  S;
        match eval compute in C with
          | ""%string => idtac "Comment: None"
          | _ => idtac "Comment:" C
        end
    | None =>
        idtac "Score: Ungraded";
        idtac "Comment: None"
    end.

End Check.

From LF Require Import IndProp.
Import Check.

Goal True.

idtac "-------------------  ev_double  --------------------".
idtac " ".

idtac "#> ev_double".
idtac "Possible points: 1".
check_type @ev_double ((forall n : nat, ev (double n))).
idtac "Assumptions:".
Abort.
Print Assumptions ev_double.
Goal True.
idtac " ".

idtac "-------------------  Perm3  --------------------".
idtac " ".

idtac "#> Perm3_ex1".
idtac "Possible points: 0.5".
check_type @Perm3_ex1 (
(@Perm3 nat (@cons nat 1 (@cons nat 2 (@cons nat 3 (@nil nat))))
   (@cons nat 2 (@cons nat 3 (@cons nat 1 (@nil nat)))))).
idtac "Assumptions:".
Abort.
Print Assumptions Perm3_ex1.
Goal True.
idtac " ".

idtac "#> Perm3_refl".
idtac "Possible points: 0.5".
check_type @Perm3_refl (
(forall (X : Type) (a b c : X),
 @Perm3 X (@cons X a (@cons X b (@cons X c (@nil X))))
   (@cons X a (@cons X b (@cons X c (@nil X)))))).
idtac "Assumptions:".
Abort.
Print Assumptions Perm3_refl.
Goal True.
idtac " ".

idtac "-------------------  le_inversion  --------------------".
idtac " ".

idtac "#> le_inversion".
idtac "Possible points: 1".
check_type @le_inversion (
(forall (n m : nat) (_ : le n m),
 or (@eq nat n m)
   (@ex nat (fun m' : nat => and (@eq nat m (S m')) (le n m'))))).
idtac "Assumptions:".
Abort.
Print Assumptions le_inversion.
Goal True.
idtac " ".

idtac "-------------------  inversion_practice  --------------------".
idtac " ".

idtac "#> SSSSev__even".
idtac "Possible points: 1".
check_type @SSSSev__even ((forall (n : nat) (_ : ev (S (S (S (S n))))), ev n)).
idtac "Assumptions:".
Abort.
Print Assumptions SSSSev__even.
Goal True.
idtac " ".

idtac "-------------------  ev5_nonsense  --------------------".
idtac " ".

idtac "#> ev5_nonsense".
idtac "Possible points: 1".
check_type @ev5_nonsense ((forall _ : ev 5, @eq nat (Nat.add 2 2) 9)).
idtac "Assumptions:".
Abort.
Print Assumptions ev5_nonsense.
Goal True.
idtac " ".

idtac "-------------------  ev_sum  --------------------".
idtac " ".

idtac "#> ev_sum".
idtac "Possible points: 2".
check_type @ev_sum ((forall (n m : nat) (_ : ev n) (_ : ev m), ev (Nat.add n m))).
idtac "Assumptions:".
Abort.
Print Assumptions ev_sum.
Goal True.
idtac " ".

idtac "-------------------  ev_ev__ev  --------------------".
idtac " ".

idtac "#> ev_ev__ev".
idtac "Advanced".
idtac "Possible points: 3".
check_type @ev_ev__ev ((forall (n m : nat) (_ : ev (Nat.add n m)) (_ : ev n), ev m)).
idtac "Assumptions:".
Abort.
Print Assumptions ev_ev__ev.
Goal True.
idtac " ".

idtac "-------------------  Perm3_In  --------------------".
idtac " ".

idtac "#> Perm3_In".
idtac "Possible points: 2".
check_type @Perm3_In (
(forall (X : Type) (x : X) (l1 l2 : list X) (_ : @Perm3 X l1 l2)
   (_ : @In X x l1),
 @In X x l2)).
idtac "Assumptions:".
Abort.
Print Assumptions Perm3_In.
Goal True.
idtac " ".

idtac "-------------------  le_facts  --------------------".
idtac " ".

idtac "#> le_trans".
idtac "Possible points: 0.5".
check_type @le_trans ((forall (m n o : nat) (_ : le m n) (_ : le n o), le m o)).
idtac "Assumptions:".
Abort.
Print Assumptions le_trans.
Goal True.
idtac " ".

idtac "#> O_le_n".
idtac "Possible points: 0.5".
check_type @O_le_n ((forall n : nat, le 0 n)).
idtac "Assumptions:".
Abort.
Print Assumptions O_le_n.
Goal True.
idtac " ".

idtac "#> n_le_m__Sn_le_Sm".
idtac "Possible points: 0.5".
check_type @n_le_m__Sn_le_Sm ((forall (n m : nat) (_ : le n m), le (S n) (S m))).
idtac "Assumptions:".
Abort.
Print Assumptions n_le_m__Sn_le_Sm.
Goal True.
idtac " ".

idtac "#> Sn_le_Sm__n_le_m".
idtac "Possible points: 1".
check_type @Sn_le_Sm__n_le_m ((forall (n m : nat) (_ : le (S n) (S m)), le n m)).
idtac "Assumptions:".
Abort.
Print Assumptions Sn_le_Sm__n_le_m.
Goal True.
idtac " ".

idtac "#> le_plus_l".
idtac "Possible points: 0.5".
check_type @le_plus_l ((forall a b : nat, le a (Nat.add a b))).
idtac "Assumptions:".
Abort.
Print Assumptions le_plus_l.
Goal True.
idtac " ".

idtac "-------------------  plus_le_facts1  --------------------".
idtac " ".

idtac "#> plus_le".
idtac "Possible points: 1".
check_type @plus_le (
(forall (n1 n2 m : nat) (_ : le (Nat.add n1 n2) m), and (le n1 m) (le n2 m))).
idtac "Assumptions:".
Abort.
Print Assumptions plus_le.
Goal True.
idtac " ".

idtac "#> plus_le_cases".
idtac "Possible points: 1".
check_type @plus_le_cases (
(forall (n m p q : nat) (_ : le (Nat.add n m) (Nat.add p q)),
 or (le n p) (le m q))).
idtac "Assumptions:".
Abort.
Print Assumptions plus_le_cases.
Goal True.
idtac " ".

idtac "-------------------  plus_le_facts2  --------------------".
idtac " ".

idtac "#> plus_le_compat_l".
idtac "Possible points: 0.5".
check_type @plus_le_compat_l (
(forall (n m p : nat) (_ : le n m), le (Nat.add p n) (Nat.add p m))).
idtac "Assumptions:".
Abort.
Print Assumptions plus_le_compat_l.
Goal True.
idtac " ".

idtac "#> plus_le_compat_r".
idtac "Possible points: 0.5".
check_type @plus_le_compat_r (
(forall (n m p : nat) (_ : le n m), le (Nat.add n p) (Nat.add m p))).
idtac "Assumptions:".
Abort.
Print Assumptions plus_le_compat_r.
Goal True.
idtac " ".

idtac "#> le_plus_trans".
idtac "Possible points: 1".
check_type @le_plus_trans ((forall (n m p : nat) (_ : le n m), le n (Nat.add m p))).
idtac "Assumptions:".
Abort.
Print Assumptions le_plus_trans.
Goal True.
idtac " ".

idtac "-------------------  R_provability  --------------------".
idtac " ".

idtac "#> Manually graded: R.R_provability".
idtac "Possible points: 3".
print_manual_grade R.manual_grade_for_R_provability.
idtac " ".

idtac "-------------------  subsequence  --------------------".
idtac " ".

idtac "#> subseq_refl".
idtac "Advanced".
idtac "Possible points: 1".
check_type @subseq_refl ((forall l : list nat, subseq l l)).
idtac "Assumptions:".
Abort.
Print Assumptions subseq_refl.
Goal True.
idtac " ".

idtac "#> subseq_app".
idtac "Advanced".
idtac "Possible points: 2".
check_type @subseq_app (
(forall (l1 l2 l3 : list nat) (_ : subseq l1 l2), subseq l1 (@app nat l2 l3))).
idtac "Assumptions:".
Abort.
Print Assumptions subseq_app.
Goal True.
idtac " ".

idtac "#> subseq_trans".
idtac "Advanced".
idtac "Possible points: 3".
check_type @subseq_trans (
(forall (l1 l2 l3 : list nat) (_ : subseq l1 l2) (_ : subseq l2 l3),
 subseq l1 l3)).
idtac "Assumptions:".
Abort.
Print Assumptions subseq_trans.
Goal True.
idtac " ".

idtac "-------------------  exp_match_ex1  --------------------".
idtac " ".

idtac "#> EmptySet_is_empty".
idtac "Possible points: 0.5".
check_type @EmptySet_is_empty (
(forall (T : Type) (s : list T), not (@exp_match T s (@EmptySet T)))).
idtac "Assumptions:".
Abort.
Print Assumptions EmptySet_is_empty.
Goal True.
idtac " ".

idtac "#> MUnion'".
idtac "Possible points: 0.5".
check_type @MUnion' (
(forall (T : Type) (s : list T) (re1 re2 : reg_exp T)
   (_ : or (@exp_match T s re1) (@exp_match T s re2)),
 @exp_match T s (@Union T re1 re2))).
idtac "Assumptions:".
Abort.
Print Assumptions MUnion'.
Goal True.
idtac " ".

idtac "#> MStar'".
idtac "Possible points: 2".
check_type @MStar' (
(forall (T : Type) (ss : list (list T)) (re : reg_exp T)
   (_ : forall (s : list T) (_ : @In (list T) s ss), @exp_match T s re),
 @exp_match T (@fold (list T) (list T) (@app T) ss (@nil T)) (@Star T re))).
idtac "Assumptions:".
Abort.
Print Assumptions MStar'.
Goal True.
idtac " ".

idtac "-------------------  re_not_empty  --------------------".
idtac " ".

idtac "#> re_not_empty".
idtac "Possible points: 3".
check_type @re_not_empty ((forall (T : Type) (_ : reg_exp T), bool)).
idtac "Assumptions:".
Abort.
Print Assumptions re_not_empty.
Goal True.
idtac " ".

idtac "#> re_not_empty_correct".
idtac "Possible points: 3".
check_type @re_not_empty_correct (
(forall (T : Type) (re : reg_exp T),
 iff (@ex (list T) (fun s : list T => @exp_match T s re))
   (@eq bool (@re_not_empty T re) true))).
idtac "Assumptions:".
Abort.
Print Assumptions re_not_empty_correct.
Goal True.
idtac " ".

idtac "-------------------  weak_pumping_char  --------------------".
idtac " ".

idtac "#> Pumping.weak_pumping_char".
idtac "Possible points: 2".
check_type @Pumping.weak_pumping_char (
(forall (T : Type) (x : T)
   (_ : le (@Pumping.pumping_constant T (@Char T x))
          (@length T (@cons T x (@nil T)))),
 @ex (list T)
   (fun s1 : list T =>
    @ex (list T)
      (fun s2 : list T =>
       @ex (list T)
         (fun s3 : list T =>
          and (@eq (list T) (@cons T x (@nil T)) (@app T s1 (@app T s2 s3)))
            (and (not (@eq (list T) s2 (@nil T)))
               (forall m : nat,
                @exp_match T (@app T s1 (@app T (@Pumping.napp T m s2) s3))
                  (@Char T x)))))))).
idtac "Assumptions:".
Abort.
Print Assumptions Pumping.weak_pumping_char.
Goal True.
idtac " ".

idtac "-------------------  weak_pumping_app  --------------------".
idtac " ".

idtac "#> Pumping.weak_pumping_app".
idtac "Possible points: 3".
check_type @Pumping.weak_pumping_app (
(forall (T : Type) (s1 s2 : list T) (re1 re2 : reg_exp T)
   (_ : @exp_match T s1 re1) (_ : @exp_match T s2 re2)
   (_ : forall _ : le (@Pumping.pumping_constant T re1) (@length T s1),
        @ex (list T)
          (fun s3 : list T =>
           @ex (list T)
             (fun s4 : list T =>
              @ex (list T)
                (fun s5 : list T =>
                 and (@eq (list T) s1 (@app T s3 (@app T s4 s5)))
                   (and (not (@eq (list T) s4 (@nil T)))
                      (forall m : nat,
                       @exp_match T
                         (@app T s3 (@app T (@Pumping.napp T m s4) s5)) re1))))))
   (_ : forall _ : le (@Pumping.pumping_constant T re2) (@length T s2),
        @ex (list T)
          (fun s3 : list T =>
           @ex (list T)
             (fun s4 : list T =>
              @ex (list T)
                (fun s5 : list T =>
                 and (@eq (list T) s2 (@app T s3 (@app T s4 s5)))
                   (and (not (@eq (list T) s4 (@nil T)))
                      (forall m : nat,
                       @exp_match T
                         (@app T s3 (@app T (@Pumping.napp T m s4) s5)) re2))))))
   (_ : le (@Pumping.pumping_constant T (@App T re1 re2))
          (@length T (@app T s1 s2))),
 @ex (list T)
   (fun s0 : list T =>
    @ex (list T)
      (fun s3 : list T =>
       @ex (list T)
         (fun s4 : list T =>
          and (@eq (list T) (@app T s1 s2) (@app T s0 (@app T s3 s4)))
            (and (not (@eq (list T) s3 (@nil T)))
               (forall m : nat,
                @exp_match T (@app T s0 (@app T (@Pumping.napp T m s3) s4))
                  (@App T re1 re2)))))))).
idtac "Assumptions:".
Abort.
Print Assumptions Pumping.weak_pumping_app.
Goal True.
idtac " ".

idtac "-------------------  weak_pumping_union_l  --------------------".
idtac " ".

idtac "#> Pumping.weak_pumping_union_l".
idtac "Possible points: 3".
check_type @Pumping.weak_pumping_union_l (
(forall (T : Type) (s1 : list T) (re1 re2 : reg_exp T)
   (_ : @exp_match T s1 re1)
   (_ : forall _ : le (@Pumping.pumping_constant T re1) (@length T s1),
        @ex (list T)
          (fun s2 : list T =>
           @ex (list T)
             (fun s3 : list T =>
              @ex (list T)
                (fun s4 : list T =>
                 and (@eq (list T) s1 (@app T s2 (@app T s3 s4)))
                   (and (not (@eq (list T) s3 (@nil T)))
                      (forall m : nat,
                       @exp_match T
                         (@app T s2 (@app T (@Pumping.napp T m s3) s4)) re1))))))
   (_ : le (@Pumping.pumping_constant T (@Union T re1 re2)) (@length T s1)),
 @ex (list T)
   (fun s0 : list T =>
    @ex (list T)
      (fun s2 : list T =>
       @ex (list T)
         (fun s3 : list T =>
          and (@eq (list T) s1 (@app T s0 (@app T s2 s3)))
            (and (not (@eq (list T) s2 (@nil T)))
               (forall m : nat,
                @exp_match T (@app T s0 (@app T (@Pumping.napp T m s2) s3))
                  (@Union T re1 re2)))))))).
idtac "Assumptions:".
Abort.
Print Assumptions Pumping.weak_pumping_union_l.
Goal True.
idtac " ".

idtac "-------------------  reflect_iff  --------------------".
idtac " ".

idtac "#> reflect_iff".
idtac "Possible points: 2".
check_type @reflect_iff (
(forall (P : Prop) (b : bool) (_ : reflect P b), iff P (@eq bool b true))).
idtac "Assumptions:".
Abort.
Print Assumptions reflect_iff.
Goal True.
idtac " ".

idtac "-------------------  eqbP_practice  --------------------".
idtac " ".

idtac "#> eqbP_practice".
idtac "Possible points: 3".
check_type @eqbP_practice (
(forall (n : nat) (l : list nat) (_ : @eq nat (count n l) 0),
 not (@In nat n l))).
idtac "Assumptions:".
Abort.
Print Assumptions eqbP_practice.
Goal True.
idtac " ".

idtac "-------------------  nostutter_defn  --------------------".
idtac " ".

idtac "#> Manually graded: nostutter".
idtac "Possible points: 3".
print_manual_grade manual_grade_for_nostutter.
idtac " ".

idtac "-------------------  filter_challenge  --------------------".
idtac " ".

idtac "#> merge_filter".
idtac "Advanced".
idtac "Possible points: 6".
check_type @merge_filter (
(forall (X : Set) (test : forall _ : X, bool) (l l1 l2 : list X)
   (_ : @merge X l1 l2 l)
   (_ : @All X (fun n : X => @eq bool (test n) true) l1)
   (_ : @All X (fun n : X => @eq bool (test n) false) l2),
 @eq (list X) (@filter X test l) l1)).
idtac "Assumptions:".
Abort.
Print Assumptions merge_filter.
Goal True.
idtac " ".

idtac " ".

idtac "Max points - standard: 44".
idtac "Max points - advanced: 59".
idtac "".
idtac "Allowed Axioms:".
idtac "functional_extensionality".
idtac "FunctionalExtensionality.functional_extensionality_dep".
idtac "plus_le".
idtac "le_trans".
idtac "le_plus_l".
idtac "add_le_cases".
idtac "Sn_le_Sm__n_le_m".
idtac "O_le_n".
idtac "".
idtac "".
idtac "********** Summary **********".
idtac "".
idtac "Below is a summary of the automatically graded exercises that are incomplete.".
idtac "".
idtac "The output for each exercise can be any of the following:".
idtac "  - 'Closed under the global context', if it is complete".
idtac "  - 'MANUAL', if it is manually graded".
idtac "  - A list of pending axioms, containing unproven assumptions. In this case".
idtac "    the exercise is considered complete, if the axioms are all allowed.".
idtac "".
idtac "********** Standard **********".
idtac "---------- ev_double ---------".
Print Assumptions ev_double.
idtac "---------- Perm3_ex1 ---------".
Print Assumptions Perm3_ex1.
idtac "---------- Perm3_refl ---------".
Print Assumptions Perm3_refl.
idtac "---------- le_inversion ---------".
Print Assumptions le_inversion.
idtac "---------- SSSSev__even ---------".
Print Assumptions SSSSev__even.
idtac "---------- ev5_nonsense ---------".
Print Assumptions ev5_nonsense.
idtac "---------- ev_sum ---------".
Print Assumptions ev_sum.
idtac "---------- Perm3_In ---------".
Print Assumptions Perm3_In.
idtac "---------- le_trans ---------".
Print Assumptions le_trans.
idtac "---------- O_le_n ---------".
Print Assumptions O_le_n.
idtac "---------- n_le_m__Sn_le_Sm ---------".
Print Assumptions n_le_m__Sn_le_Sm.
idtac "---------- Sn_le_Sm__n_le_m ---------".
Print Assumptions Sn_le_Sm__n_le_m.
idtac "---------- le_plus_l ---------".
Print Assumptions le_plus_l.
idtac "---------- plus_le ---------".
Print Assumptions plus_le.
idtac "---------- plus_le_cases ---------".
Print Assumptions plus_le_cases.
idtac "---------- plus_le_compat_l ---------".
Print Assumptions plus_le_compat_l.
idtac "---------- plus_le_compat_r ---------".
Print Assumptions plus_le_compat_r.
idtac "---------- le_plus_trans ---------".
Print Assumptions le_plus_trans.
idtac "---------- R_provability ---------".
idtac "MANUAL".
idtac "---------- EmptySet_is_empty ---------".
Print Assumptions EmptySet_is_empty.
idtac "---------- MUnion' ---------".
Print Assumptions MUnion'.
idtac "---------- MStar' ---------".
Print Assumptions MStar'.
idtac "---------- re_not_empty ---------".
Print Assumptions re_not_empty.
idtac "---------- re_not_empty_correct ---------".
Print Assumptions re_not_empty_correct.
idtac "---------- Pumping.weak_pumping_char ---------".
Print Assumptions Pumping.weak_pumping_char.
idtac "---------- Pumping.weak_pumping_app ---------".
Print Assumptions Pumping.weak_pumping_app.
idtac "---------- Pumping.weak_pumping_union_l ---------".
Print Assumptions Pumping.weak_pumping_union_l.
idtac "---------- reflect_iff ---------".
Print Assumptions reflect_iff.
idtac "---------- eqbP_practice ---------".
Print Assumptions eqbP_practice.
idtac "---------- nostutter ---------".
idtac "MANUAL".
idtac "".
idtac "********** Advanced **********".
idtac "---------- ev_ev__ev ---------".
Print Assumptions ev_ev__ev.
idtac "---------- subseq_refl ---------".
Print Assumptions subseq_refl.
idtac "---------- subseq_app ---------".
Print Assumptions subseq_app.
idtac "---------- subseq_trans ---------".
Print Assumptions subseq_trans.
idtac "---------- merge_filter ---------".
Print Assumptions merge_filter.
Abort.

(* 2026-01-07 13:18 *)

(* 2026-01-07 13:18 *)
