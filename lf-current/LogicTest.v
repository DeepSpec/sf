Set Warnings "-notation-overridden,-parsing".
From Stdlib Require Export String.
From LF Require Import Logic.

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

From LF Require Import Logic.
Import Check.

Goal True.

idtac "-------------------  plus_is_O  --------------------".
idtac " ".

idtac "#> plus_is_O".
idtac "Possible points: 2".
check_type @plus_is_O (
(forall (n m : nat) (_ : @eq nat (Nat.add n m) 0),
 and (@eq nat n 0) (@eq nat m 0))).
idtac "Assumptions:".
Abort.
Print Assumptions plus_is_O.
Goal True.
idtac " ".

idtac "-------------------  and_assoc  --------------------".
idtac " ".

idtac "#> and_assoc".
idtac "Possible points: 1".
check_type @and_assoc ((forall (P Q R : Prop) (_ : and P (and Q R)), and (and P Q) R)).
idtac "Assumptions:".
Abort.
Print Assumptions and_assoc.
Goal True.
idtac " ".

idtac "-------------------  mult_is_O  --------------------".
idtac " ".

idtac "#> mult_is_O".
idtac "Possible points: 2".
check_type @mult_is_O (
(forall (n m : nat) (_ : @eq nat (Nat.mul n m) 0),
 or (@eq nat n 0) (@eq nat m 0))).
idtac "Assumptions:".
Abort.
Print Assumptions mult_is_O.
Goal True.
idtac " ".

idtac "-------------------  or_commut  --------------------".
idtac " ".

idtac "#> or_commut".
idtac "Possible points: 1".
check_type @or_commut ((forall (P Q : Prop) (_ : or P Q), or Q P)).
idtac "Assumptions:".
Abort.
Print Assumptions or_commut.
Goal True.
idtac " ".

idtac "-------------------  contrapositive  --------------------".
idtac " ".

idtac "#> contrapositive".
idtac "Possible points: 1".
check_type @contrapositive (
(forall (P Q : Prop) (_ : forall _ : P, Q) (_ : not Q), not P)).
idtac "Assumptions:".
Abort.
Print Assumptions contrapositive.
Goal True.
idtac " ".

idtac "-------------------  not_both_true_and_false  --------------------".
idtac " ".

idtac "#> not_both_true_and_false".
idtac "Possible points: 1".
check_type @not_both_true_and_false ((forall P : Prop, not (and P (not P)))).
idtac "Assumptions:".
Abort.
Print Assumptions not_both_true_and_false.
Goal True.
idtac " ".

idtac "-------------------  not_PNP_informal  --------------------".
idtac " ".

idtac "#> Manually graded: not_PNP_informal".
idtac "Advanced".
idtac "Possible points: 1".
print_manual_grade manual_grade_for_not_PNP_informal.
idtac " ".

idtac "-------------------  de_morgan_not_or  --------------------".
idtac " ".

idtac "#> de_morgan_not_or".
idtac "Possible points: 2".
check_type @de_morgan_not_or (
(forall (P Q : Prop) (_ : not (or P Q)), and (not P) (not Q))).
idtac "Assumptions:".
Abort.
Print Assumptions de_morgan_not_or.
Goal True.
idtac " ".

idtac "-------------------  or_distributes_over_and  --------------------".
idtac " ".

idtac "#> or_distributes_over_and".
idtac "Possible points: 3".
check_type @or_distributes_over_and (
(forall P Q R : Prop, iff (or P (and Q R)) (and (or P Q) (or P R)))).
idtac "Assumptions:".
Abort.
Print Assumptions or_distributes_over_and.
Goal True.
idtac " ".

idtac "-------------------  dist_not_exists  --------------------".
idtac " ".

idtac "#> dist_not_exists".
idtac "Possible points: 1".
check_type @dist_not_exists (
(forall (X : Type) (P : forall _ : X, Prop) (_ : forall x : X, P x),
 not (@ex X (fun x : X => not (P x))))).
idtac "Assumptions:".
Abort.
Print Assumptions dist_not_exists.
Goal True.
idtac " ".

idtac "-------------------  dist_exists_or  --------------------".
idtac " ".

idtac "#> dist_exists_or".
idtac "Possible points: 2".
check_type @dist_exists_or (
(forall (X : Type) (P Q : forall _ : X, Prop),
 iff (@ex X (fun x : X => or (P x) (Q x)))
   (or (@ex X (fun x : X => P x)) (@ex X (fun x : X => Q x))))).
idtac "Assumptions:".
Abort.
Print Assumptions dist_exists_or.
Goal True.
idtac " ".

idtac "-------------------  In_map_iff  --------------------".
idtac " ".

idtac "#> In_map_iff".
idtac "Possible points: 2".
check_type @In_map_iff (
(forall (A B : Type) (f : forall _ : A, B) (l : list A) (y : B),
 iff (@In B y (@map A B f l))
   (@ex A (fun x : A => and (@eq B (f x) y) (@In A x l))))).
idtac "Assumptions:".
Abort.
Print Assumptions In_map_iff.
Goal True.
idtac " ".

idtac "-------------------  In_app_iff  --------------------".
idtac " ".

idtac "#> In_app_iff".
idtac "Possible points: 2".
check_type @In_app_iff (
(forall (A : Type) (l l' : list A) (a : A),
 iff (@In A a (@app A l l')) (or (@In A a l) (@In A a l')))).
idtac "Assumptions:".
Abort.
Print Assumptions In_app_iff.
Goal True.
idtac " ".

idtac "-------------------  All  --------------------".
idtac " ".

idtac "#> All_In".
idtac "Possible points: 3".
check_type @All_In (
(forall (T : Type) (P : forall _ : T, Prop) (l : list T),
 iff (forall (x : T) (_ : @In T x l), P x) (@All T P l))).
idtac "Assumptions:".
Abort.
Print Assumptions All_In.
Goal True.
idtac " ".

idtac "-------------------  even_double_conv  --------------------".
idtac " ".

idtac "#> even_double_conv".
idtac "Possible points: 3".
check_type @even_double_conv (
(forall n : nat,
 @ex nat
   (fun k : nat => @eq nat n (if even n then double k else S (double k))))).
idtac "Assumptions:".
Abort.
Print Assumptions even_double_conv.
Goal True.
idtac " ".

idtac "-------------------  logical_connectives  --------------------".
idtac " ".

idtac "#> andb_true_iff".
idtac "Possible points: 1".
check_type @andb_true_iff (
(forall b1 b2 : bool,
 iff (@eq bool (andb b1 b2) true) (and (@eq bool b1 true) (@eq bool b2 true)))).
idtac "Assumptions:".
Abort.
Print Assumptions andb_true_iff.
Goal True.
idtac " ".

idtac "#> orb_true_iff".
idtac "Possible points: 1".
check_type @orb_true_iff (
(forall b1 b2 : bool,
 iff (@eq bool (orb b1 b2) true) (or (@eq bool b1 true) (@eq bool b2 true)))).
idtac "Assumptions:".
Abort.
Print Assumptions orb_true_iff.
Goal True.
idtac " ".

idtac "-------------------  eqb_neq  --------------------".
idtac " ".

idtac "#> eqb_neq".
idtac "Possible points: 1".
check_type @eqb_neq (
(forall x y : nat, iff (@eq bool (eqb x y) false) (not (@eq nat x y)))).
idtac "Assumptions:".
Abort.
Print Assumptions eqb_neq.
Goal True.
idtac " ".

idtac "-------------------  eqb_list  --------------------".
idtac " ".

idtac "#> eqb_list_true_iff".
idtac "Possible points: 3".
check_type @eqb_list_true_iff (
(forall (A : Type) (eqb : forall (_ : A) (_ : A), bool)
   (_ : forall a1 a2 : A, iff (@eq bool (eqb a1 a2) true) (@eq A a1 a2))
   (l1 l2 : list A),
 iff (@eq bool (@eqb_list A eqb l1 l2) true) (@eq (list A) l1 l2))).
idtac "Assumptions:".
Abort.
Print Assumptions eqb_list_true_iff.
Goal True.
idtac " ".

idtac "-------------------  All_forallb  --------------------".
idtac " ".

idtac "#> forallb_true_iff".
idtac "Possible points: 2".
check_type @forallb_true_iff (
(forall (X : Type) (test : forall _ : X, bool) (l : list X),
 iff (@eq bool (@forallb X test l) true)
   (@All X (fun x : X => @eq bool (test x) true) l))).
idtac "Assumptions:".
Abort.
Print Assumptions forallb_true_iff.
Goal True.
idtac " ".

idtac "-------------------  tr_rev_correct  --------------------".
idtac " ".

idtac "#> tr_rev_correct".
idtac "Possible points: 6".
check_type @tr_rev_correct (
(forall X : Type, @eq (forall _ : list X, list X) (@tr_rev X) (@rev X))).
idtac "Assumptions:".
Abort.
Print Assumptions tr_rev_correct.
Goal True.
idtac " ".

idtac "-------------------  excluded_middle_irrefutable  --------------------".
idtac " ".

idtac "#> excluded_middle_irrefutable".
idtac "Possible points: 3".
check_type @excluded_middle_irrefutable ((forall P : Prop, not (not (or P (not P))))).
idtac "Assumptions:".
Abort.
Print Assumptions excluded_middle_irrefutable.
Goal True.
idtac " ".

idtac "-------------------  not_exists_dist  --------------------".
idtac " ".

idtac "#> not_exists_dist".
idtac "Advanced".
idtac "Possible points: 3".
check_type @not_exists_dist (
(forall (_ : excluded_middle) (X : Type) (P : forall _ : X, Prop)
   (_ : not (@ex X (fun x : X => not (P x)))) (x : X),
 P x)).
idtac "Assumptions:".
Abort.
Print Assumptions not_exists_dist.
Goal True.
idtac " ".

idtac " ".

idtac "Max points - standard: 43".
idtac "Max points - advanced: 47".
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
idtac "---------- plus_is_O ---------".
Print Assumptions plus_is_O.
idtac "---------- and_assoc ---------".
Print Assumptions and_assoc.
idtac "---------- mult_is_O ---------".
Print Assumptions mult_is_O.
idtac "---------- or_commut ---------".
Print Assumptions or_commut.
idtac "---------- contrapositive ---------".
Print Assumptions contrapositive.
idtac "---------- not_both_true_and_false ---------".
Print Assumptions not_both_true_and_false.
idtac "---------- de_morgan_not_or ---------".
Print Assumptions de_morgan_not_or.
idtac "---------- or_distributes_over_and ---------".
Print Assumptions or_distributes_over_and.
idtac "---------- dist_not_exists ---------".
Print Assumptions dist_not_exists.
idtac "---------- dist_exists_or ---------".
Print Assumptions dist_exists_or.
idtac "---------- In_map_iff ---------".
Print Assumptions In_map_iff.
idtac "---------- In_app_iff ---------".
Print Assumptions In_app_iff.
idtac "---------- All_In ---------".
Print Assumptions All_In.
idtac "---------- even_double_conv ---------".
Print Assumptions even_double_conv.
idtac "---------- andb_true_iff ---------".
Print Assumptions andb_true_iff.
idtac "---------- orb_true_iff ---------".
Print Assumptions orb_true_iff.
idtac "---------- eqb_neq ---------".
Print Assumptions eqb_neq.
idtac "---------- eqb_list_true_iff ---------".
Print Assumptions eqb_list_true_iff.
idtac "---------- forallb_true_iff ---------".
Print Assumptions forallb_true_iff.
idtac "---------- tr_rev_correct ---------".
Print Assumptions tr_rev_correct.
idtac "---------- excluded_middle_irrefutable ---------".
Print Assumptions excluded_middle_irrefutable.
idtac "".
idtac "********** Advanced **********".
idtac "---------- not_PNP_informal ---------".
idtac "MANUAL".
idtac "---------- not_exists_dist ---------".
Print Assumptions not_exists_dist.
Abort.

(* 2026-01-07 13:18 *)

(* 2026-01-07 13:18 *)
