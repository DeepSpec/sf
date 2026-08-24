Set Warnings "-notation-overridden,-parsing".
From Stdlib Require Export String.
From LF Require Import Auto.

Parameter MISSING: Type.

Module Check.

Ltac check_type A B :=
    match type of A with
    | context[MISSING] => idtac "Missing:" A
    | ?T => first [unify T B; idtac "Type: ok" | idtac "Type: wrong - should be (" B ")"]
    end.

Tactic Notation "print_manual_grade" constr(A) :=
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

From LF Require Import Auto.
Import Check.

Goal True.

idtac "-------------------  pumping_constant_ge_1_redux  --------------------".
idtac " ".

idtac "#> Manually graded: Exercises.pumping_constant_ge_1_redux".
idtac "Possible points: 1".
print_manual_grade Exercises.manual_grade_for_pumping_constant_ge_1_redux.
idtac " ".

idtac "-------------------  re_opt_match_auto  --------------------".
idtac " ".

idtac "#> Manually graded: Exercises.re_opt_match''".
idtac "Possible points: 3".
print_manual_grade Exercises.manual_grade_for_re_opt_match''.
idtac " ".

idtac "-------------------  automatic_solvers  --------------------".
idtac " ".

idtac "#> cons_equal".
idtac "Possible points: 0.5".
check_type @cons_equal (
(forall (X : Type) (n m : X) (l : list X) (_ : @eq X n m),
 @eq (list X) (@cons X n l) (@cons X m l))).
idtac "Assumptions:".
Abort.
Print Assumptions cons_equal.
Goal True.
idtac " ".

idtac "#> plus_le_cancel_r".
idtac "Possible points: 0.5".
check_type @plus_le_cancel_r (
(forall (n m p : nat) (_ : le (Nat.add n p) (Nat.add m p)), le n m)).
idtac "Assumptions:".
Abort.
Print Assumptions plus_le_cancel_r.
Goal True.
idtac " ".

idtac "#> no_half".
idtac "Possible points: 0.5".
check_type @no_half ((forall n : nat, not (@eq nat (Nat.mul 2 n) 1))).
idtac "Assumptions:".
Abort.
Print Assumptions no_half.
Goal True.
idtac " ".

idtac "#> pair_equal".
idtac "Possible points: 0.5".
check_type @pair_equal (
(forall (X : Type) (a b c d : X) (e : prod X X)
   (_ : @eq (prod X (prod X X)) (@pair X (prod X X) a (@pair X X b c))
          (@pair X (prod X X) d e))
   (_ : @eq (prod X X) e (@pair X X d c)),
 @eq X b d)).
idtac "Assumptions:".
Abort.
Print Assumptions pair_equal.
Goal True.
idtac " ".

idtac " ".

idtac "Max points - standard: 6".
idtac "Max points - advanced: 6".
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
idtac "---------- pumping_constant_ge_1_redux ---------".
idtac "MANUAL".
idtac "---------- re_opt_match'' ---------".
idtac "MANUAL".
idtac "---------- cons_equal ---------".
Print Assumptions cons_equal.
idtac "---------- plus_le_cancel_r ---------".
Print Assumptions plus_le_cancel_r.
idtac "---------- no_half ---------".
Print Assumptions no_half.
idtac "---------- pair_equal ---------".
Print Assumptions pair_equal.
idtac "".
idtac "********** Advanced **********".
Abort.

(* 2026-08-24 10:03 *)

(* 2026-08-24 10:03 *)
