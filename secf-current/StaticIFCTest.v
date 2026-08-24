Set Warnings "-notation-overridden,-parsing".
From Stdlib Require Export String.
From SECF Require Import StaticIFC.

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

From SECF Require Import StaticIFC.
Import Check.

Goal True.

idtac "-------------------  noninterferent_secure_com1'  --------------------".
idtac " ".

idtac "#> secure_com1'_leaves_X_eq_42".
idtac "Possible points: 1".
check_type @secure_com1'_leaves_X_eq_42 (
(forall (s s' : Imp.state) (_ : Imp.ceval secure_com1' s s'),
 @eq nat (s' Imp.X) 42)).
idtac "Assumptions:".
Abort.
Print Assumptions secure_com1'_leaves_X_eq_42.
Goal True.
idtac " ".

idtac "#> noninterferent_secure_com1'".
idtac "Possible points: 1".
check_type @noninterferent_secure_com1' (
(Noninterference.noninterferent_com Noninterference.LXP secure_com1')).
idtac "Assumptions:".
Abort.
Print Assumptions noninterferent_secure_com1'.
Goal True.
idtac " ".

idtac "-------------------  not_cf_wt_noninterferent_com  --------------------".
idtac " ".

idtac "#> not_cf_wt_noninterferent_com".
idtac "Possible points: 1".
check_type @not_cf_wt_noninterferent_com (
(not
   (cf_well_typed Noninterference.LXP
      (Imp.CIf (Imp.BEq (Imp.AId Imp.Y) (Imp.ANum 0))
         (Imp.CAsgn Imp.Z (Imp.ANum 0)) Imp.CSkip)))).
idtac "Assumptions:".
Abort.
Print Assumptions not_cf_wt_noninterferent_com.
Goal True.
idtac " ".

idtac "-------------------  ts_type_checker  --------------------".
idtac " ".

idtac "#> ts_type_checker".
idtac "Possible points: 2".
check_type @ts_type_checker (
(forall (_ : Noninterference.label_map) (_ : Noninterference.label)
   (_ : Imp.com),
 bool)).
idtac "Assumptions:".
Abort.
Print Assumptions ts_type_checker.
Goal True.
idtac " ".

idtac "-------------------  ts_type_checker_sound  --------------------".
idtac " ".

idtac "#> ts_type_checker_sound".
idtac "Possible points: 2".
check_type @ts_type_checker_sound (
(forall (L : Noninterference.label_map) (pc : Noninterference.label)
   (c : Imp.com) (_ : @eq bool (ts_type_checker L pc c) true),
 ts_well_typed L pc c)).
idtac "Assumptions:".
Abort.
Print Assumptions ts_type_checker_sound.
Goal True.
idtac " ".

idtac "-------------------  ts_type_checker_complete  --------------------".
idtac " ".

idtac "#> ts_type_checker_complete".
idtac "Possible points: 2".
check_type @ts_type_checker_complete (
(forall (L : Noninterference.label_map) (pc : Noninterference.label)
   (c : Imp.com) (_ : @eq bool (ts_type_checker L pc c) false),
 not (ts_well_typed L pc c))).
idtac "Assumptions:".
Abort.
Print Assumptions ts_type_checker_complete.
Goal True.
idtac " ".

idtac "-------------------  not_ts_non_termination_com  --------------------".
idtac " ".

idtac "#> not_ts_non_termination_com".
idtac "Possible points: 1".
check_type @not_ts_non_termination_com (
(not
   (ts_well_typed Noninterference.LXP Noninterference.public
      Noninterference.termination_leak))).
idtac "Assumptions:".
Abort.
Print Assumptions not_ts_non_termination_com.
Goal True.
idtac " ".

idtac "-------------------  cf_well_typed_tsni  --------------------".
idtac " ".

idtac "#> cf_well_typed_ts_well_typed".
idtac "Possible points: 1".
check_type @cf_well_typed_ts_well_typed (
(forall (L : Noninterference.label_map) (c : Imp.com) (_ : cf_well_typed L c),
 ts_well_typed L Noninterference.public c)).
idtac "Assumptions:".
Abort.
Print Assumptions cf_well_typed_ts_well_typed.
Goal True.
idtac " ".

idtac "#> cf_well_typed_tsni".
idtac "Possible points: 1".
check_type @cf_well_typed_tsni (
(forall (L : Noninterference.label_map) (c : Imp.com) (_ : cf_well_typed L c),
 tsni_com L c)).
idtac "Assumptions:".
Abort.
Print Assumptions cf_well_typed_tsni.
Goal True.
idtac " ".

idtac "-------------------  cf_well_typed_ts_cf_secure  --------------------".
idtac " ".

idtac "#> cf_well_typed_ts_cf_secure".
idtac "Possible points: 6".
check_type @cf_well_typed_ts_cf_secure (
(forall (L : Noninterference.label_map) (c : Imp.com) (_ : cf_well_typed L c),
 ts_cf_secure L c)).
idtac "Assumptions:".
Abort.
Print Assumptions cf_well_typed_ts_cf_secure.
Goal True.
idtac " ".

idtac "-------------------  public_outputs  --------------------".
idtac " ".

idtac "#> OUTPUT.oni_type_checker_sound".
idtac "Possible points: 0.5".
check_type @OUTPUT.oni_type_checker_sound (
(forall (L : Noninterference.label_map) (pc : Noninterference.label)
   (c : OUTPUT.com) (_ : @eq bool (OUTPUT.oni_type_checker L pc c) true),
 OUTPUT.oni_well_typed L pc c)).
idtac "Assumptions:".
Abort.
Print Assumptions OUTPUT.oni_type_checker_sound.
Goal True.
idtac " ".

idtac "#> OUTPUT.oni_type_checker_complete".
idtac "Possible points: 0.5".
check_type @OUTPUT.oni_type_checker_complete (
(forall (L : Noninterference.label_map) (pc : Noninterference.label)
   (c : OUTPUT.com) (_ : @eq bool (OUTPUT.oni_type_checker L pc c) false),
 not (OUTPUT.oni_well_typed L pc c))).
idtac "Assumptions:".
Abort.
Print Assumptions OUTPUT.oni_type_checker_complete.
Goal True.
idtac " ".

idtac "#> OUTPUT.not_ni_wt_output1".
idtac "Possible points: 0.5".
check_type @OUTPUT.not_ni_wt_output1 (
(not
   (OUTPUT.oni_well_typed Noninterference.LXP Noninterference.public
      OUTPUT.output_insecure_com1))).
idtac "Assumptions:".
Abort.
Print Assumptions OUTPUT.not_ni_wt_output1.
Goal True.
idtac " ".

idtac "#> OUTPUT.not_ni_wt_output2".
idtac "Possible points: 0.5".
check_type @OUTPUT.not_ni_wt_output2 (
(not
   (OUTPUT.oni_well_typed Noninterference.LXP Noninterference.public
      OUTPUT.output_insecure_com2))).
idtac "Assumptions:".
Abort.
Print Assumptions OUTPUT.not_ni_wt_output2.
Goal True.
idtac " ".

idtac "#> OUTPUT.oni_well_typed_noninterferent".
idtac "Possible points: 3".
check_type @OUTPUT.oni_well_typed_noninterferent (
(forall (L : Noninterference.label_map) (pc : Noninterference.label)
   (c : OUTPUT.com) (_ : OUTPUT.oni_well_typed L pc c),
 OUTPUT.noninterferent L c)).
idtac "Assumptions:".
Abort.
Print Assumptions OUTPUT.oni_well_typed_noninterferent.
Goal True.
idtac " ".

idtac "#> OUTPUT.secret_run_no_output".
idtac "Possible points: 2".
check_type @OUTPUT.secret_run_no_output (
(forall (L : Noninterference.label_map) (c : OUTPUT.com)
   (s s' : Imp.state) (os : OUTPUT.outputs)
   (_ : OUTPUT.oni_well_typed L Noninterference.secret c)
   (_ : OUTPUT.oceval c s s' os),
 @eq OUTPUT.outputs os (@nil nat))).
idtac "Assumptions:".
Abort.
Print Assumptions OUTPUT.secret_run_no_output.
Goal True.
idtac " ".

idtac "#> OUTPUT.oni_well_typed_output_secure".
idtac "Possible points: 3".
check_type @OUTPUT.oni_well_typed_output_secure (
(forall (L : Noninterference.label_map) (pc : Noninterference.label)
   (c : OUTPUT.com) (_ : OUTPUT.oni_well_typed L pc c),
 OUTPUT.output_secure L c)).
idtac "Assumptions:".
Abort.
Print Assumptions OUTPUT.oni_well_typed_output_secure.
Goal True.
idtac " ".

idtac " ".

idtac "Max points - standard: 28".
idtac "Max points - advanced: 28".
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
idtac "---------- secure_com1'_leaves_X_eq_42 ---------".
Print Assumptions secure_com1'_leaves_X_eq_42.
idtac "---------- noninterferent_secure_com1' ---------".
Print Assumptions noninterferent_secure_com1'.
idtac "---------- not_cf_wt_noninterferent_com ---------".
Print Assumptions not_cf_wt_noninterferent_com.
idtac "---------- ts_type_checker ---------".
Print Assumptions ts_type_checker.
idtac "---------- ts_type_checker_sound ---------".
Print Assumptions ts_type_checker_sound.
idtac "---------- ts_type_checker_complete ---------".
Print Assumptions ts_type_checker_complete.
idtac "---------- not_ts_non_termination_com ---------".
Print Assumptions not_ts_non_termination_com.
idtac "---------- cf_well_typed_ts_well_typed ---------".
Print Assumptions cf_well_typed_ts_well_typed.
idtac "---------- cf_well_typed_tsni ---------".
Print Assumptions cf_well_typed_tsni.
idtac "---------- cf_well_typed_ts_cf_secure ---------".
Print Assumptions cf_well_typed_ts_cf_secure.
idtac "---------- OUTPUT.oni_type_checker_sound ---------".
Print Assumptions OUTPUT.oni_type_checker_sound.
idtac "---------- OUTPUT.oni_type_checker_complete ---------".
Print Assumptions OUTPUT.oni_type_checker_complete.
idtac "---------- OUTPUT.not_ni_wt_output1 ---------".
Print Assumptions OUTPUT.not_ni_wt_output1.
idtac "---------- OUTPUT.not_ni_wt_output2 ---------".
Print Assumptions OUTPUT.not_ni_wt_output2.
idtac "---------- OUTPUT.oni_well_typed_noninterferent ---------".
Print Assumptions OUTPUT.oni_well_typed_noninterferent.
idtac "---------- OUTPUT.secret_run_no_output ---------".
Print Assumptions OUTPUT.secret_run_no_output.
idtac "---------- OUTPUT.oni_well_typed_output_secure ---------".
Print Assumptions OUTPUT.oni_well_typed_output_secure.
idtac "".
idtac "********** Advanced **********".
Abort.

(* 2026-08-24 10:13 *)

(* 2026-08-24 10:13 *)
