Set Warnings "-notation-overridden,-parsing".
From Coq Require Export String.
From PLF Require Import RecordSub.

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

From PLF Require Import RecordSub.
Import Check.

Goal True.

idtac "-------------------  subtyping_example_1  --------------------".
idtac " ".

idtac "#> Examples.subtyping_example_1".
idtac "Possible points: 2".
check_type @Examples.subtyping_example_1 ((Examples.TRcd_kj <: Examples.TRcd_j)).
idtac "Assumptions:".
Abort.
Print Assumptions Examples.subtyping_example_1.
Goal True.
idtac " ".

idtac "-------------------  subtyping_example_2  --------------------".
idtac " ".

idtac "#> Examples.subtyping_example_2".
idtac "Possible points: 1".
check_type @Examples.subtyping_example_2 (
(Arrow Top Examples.TRcd_kj <:
 Arrow (Arrow Examples.C Examples.C) Examples.TRcd_j)).
idtac "Assumptions:".
Abort.
Print Assumptions Examples.subtyping_example_2.
Goal True.
idtac " ".

idtac "-------------------  subtyping_example_3  --------------------".
idtac " ".

idtac "#> Examples.subtyping_example_3".
idtac "Possible points: 1".
check_type @Examples.subtyping_example_3 (
(Arrow RNil (RCons "j" Examples.A RNil) <:
 Arrow (RCons "k" Examples.B RNil) RNil)).
idtac "Assumptions:".
Abort.
Print Assumptions Examples.subtyping_example_3.
Goal True.
idtac " ".

idtac "-------------------  subtyping_example_4  --------------------".
idtac " ".

idtac "#> Examples.subtyping_example_4".
idtac "Possible points: 2".
check_type @Examples.subtyping_example_4 (
(RCons "x" Examples.A (RCons "y" Examples.B (RCons "z" Examples.C RNil)) <:
 RCons "z" Examples.C (RCons "y" Examples.B (RCons "x" Examples.A RNil)))).
idtac "Assumptions:".
Abort.
Print Assumptions Examples.subtyping_example_4.
Goal True.
idtac " ".

idtac "-------------------  rcd_types_match_informal  --------------------".
idtac " ".

idtac "#> Manually graded: rcd_types_match_informal".
idtac "Possible points: 3".
print_manual_grade manual_grade_for_rcd_types_match_informal.
idtac " ".

idtac "-------------------  typing_example_0  --------------------".
idtac " ".

idtac "#> Examples2.typing_example_0".
idtac "Possible points: 1".
check_type @Examples2.typing_example_0 (
(@Maps.empty ty
 |- rcons "k" (abs "z" Examples.A (var "z"))
      (rcons "j" (abs "z" Examples.B (var "z")) rnil) \in Examples.TRcd_kj)).
idtac "Assumptions:".
Abort.
Print Assumptions Examples2.typing_example_0.
Goal True.
idtac " ".

idtac "-------------------  typing_example_1  --------------------".
idtac " ".

idtac "#> Examples2.typing_example_1".
idtac "Possible points: 2".
check_type @Examples2.typing_example_1 (
(@Maps.empty ty
 |- app (abs "x" Examples.TRcd_j (rproj (var "x") "j")) Examples2.trcd_kj \in
 Arrow Examples.B Examples.B)).
idtac "Assumptions:".
Abort.
Print Assumptions Examples2.typing_example_1.
Goal True.
idtac " ".

idtac "-------------------  canonical_forms_of_arrow_types  --------------------".
idtac " ".

idtac "#> canonical_forms_of_arrow_types".
idtac "Possible points: 3".
check_type @canonical_forms_of_arrow_types (
(forall (Gamma : context) (s : tm) (T1 T2 : ty),
 Gamma |- s \in Arrow T1 T2 ->
 value s -> exists (x : String.string) (S1 : ty) (s2 : tm), s = abs x S1 s2)).
idtac "Assumptions:".
Abort.
Print Assumptions canonical_forms_of_arrow_types.
Goal True.
idtac " ".

idtac " ".

idtac "Max points - standard: 15".
idtac "Max points - advanced: 15".
idtac "".
idtac "Allowed Axioms:".
idtac "functional_extensionality".
idtac "FunctionalExtensionality.functional_extensionality_dep".
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
idtac "---------- Examples.subtyping_example_1 ---------".
Print Assumptions Examples.subtyping_example_1.
idtac "---------- Examples.subtyping_example_2 ---------".
Print Assumptions Examples.subtyping_example_2.
idtac "---------- Examples.subtyping_example_3 ---------".
Print Assumptions Examples.subtyping_example_3.
idtac "---------- Examples.subtyping_example_4 ---------".
Print Assumptions Examples.subtyping_example_4.
idtac "---------- rcd_types_match_informal ---------".
idtac "MANUAL".
idtac "---------- Examples2.typing_example_0 ---------".
Print Assumptions Examples2.typing_example_0.
idtac "---------- Examples2.typing_example_1 ---------".
Print Assumptions Examples2.typing_example_1.
idtac "---------- canonical_forms_of_arrow_types ---------".
Print Assumptions canonical_forms_of_arrow_types.
idtac "".
idtac "********** Advanced **********".
Abort.

(* 2020-06-11 14:32:04 (UTC+00) *)
