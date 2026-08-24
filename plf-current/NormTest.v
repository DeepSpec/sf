Set Warnings "-notation-overridden,-parsing".
From Stdlib Require Export String.
From PLF Require Import Norm.

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

From PLF Require Import Norm.
Import Check.

Goal True.

idtac "-------------------  norm_fail  --------------------".
idtac " ".

idtac "#> Manually graded: norm_fail".
idtac "Possible points: 2".
print_manual_grade manual_grade_for_norm_fail.
idtac " ".

idtac "-------------------  value_halts  --------------------".
idtac " ".

idtac "#> value_halts".
idtac "Possible points: 2".
check_type @value_halts ((forall (v : tm) (_ : value v), halts v)).
idtac "Assumptions:".
Abort.
Print Assumptions value_halts.
Goal True.
idtac " ".

idtac "-------------------  step_preserves_halting  --------------------".
idtac " ".

idtac "#> step_preserves_halting".
idtac "Possible points: 3".
check_type @step_preserves_halting (
(forall (t t' : tm) (_ : step t t'), iff (halts t) (halts t'))).
idtac "Assumptions:".
Abort.
Print Assumptions step_preserves_halting.
Goal True.
idtac " ".

idtac "-------------------  N_products  --------------------".
idtac " ".

idtac "#> Manually graded: N_products".
idtac "Possible points: 3".
print_manual_grade manual_grade_for_N_products.
idtac " ".

idtac "-------------------  step_preserves_N  --------------------".
idtac " ".

idtac "#> step_preserves_N".
idtac "Possible points: 3".
check_type @step_preserves_N (
(forall (T : ty) (t t' : tm) (_ : step t t') (_ : N T t), N T t')).
idtac "Assumptions:".
Abort.
Print Assumptions step_preserves_N.
Goal True.
idtac " ".

idtac "-------------------  step_preserves_N'  --------------------".
idtac " ".

idtac "#> step_preserves_N'".
idtac "Possible points: 6".
check_type @step_preserves_N' (
(forall (T : ty) (t t' : tm) (_ : has_type (@Maps.empty ty) t T)
   (_ : step t t') (_ : N T t'),
 N T t)).
idtac "Assumptions:".
Abort.
Print Assumptions step_preserves_N'.
Goal True.
idtac " ".

idtac "-------------------  swap_subst  --------------------".
idtac " ".

idtac "#> swap_subst".
idtac "Possible points: 3".
check_type @swap_subst (
(forall (t : tm) (x x1 : String.string) (v v1 : tm)
   (_ : not (@eq String.string x x1)) (_ : closed v)
   (_ : closed v1),
 @eq tm (subst x1 v1 (subst x v t)) (subst x v (subst x1 v1 t)))).
idtac "Assumptions:".
Abort.
Print Assumptions swap_subst.
Goal True.
idtac " ".

idtac "-------------------  msubst_subst  --------------------".
idtac " ".

idtac "#> msubst_subst".
idtac "Possible points: 3".
check_type @msubst_subst (
(forall (e : env) (x : String.string) (v t : tm) (_ : closed v)
   (_ : closed_env e),
 @eq tm (msubst e (subst x v t)) (subst x v (msubst (remove x e) t)))).
idtac "Assumptions:".
Abort.
Print Assumptions msubst_subst.
Goal True.
idtac " ".

idtac "-------------------  msubst_app  --------------------".
idtac " ".

idtac "#> msubst_app".
idtac "Possible points: 2".
check_type @msubst_app (
(forall (ss : env) (t1 t2 : tm),
 @eq tm (msubst ss (tm_app t1 t2)) (tm_app (msubst ss t1) (msubst ss t2)))).
idtac "Assumptions:".
Abort.
Print Assumptions msubst_app.
Goal True.
idtac " ".

idtac "-------------------  instantiation_msubst  --------------------".
idtac " ".

idtac "#> instantiation_msubst".
idtac "Possible points: 3".
check_type @instantiation_msubst (
(forall (R : forall (_ : ty) (_ : tm), Prop) (RC : R_closed R)
   (c : tass) (e : env) (_ : instantiation R RC c e)
   (x : String.string) (T : ty)
   (_ : @eq (option ty) (tass_context c x) (@Some ty T)),
 R T (msubst e (tm_var x)))).
idtac "Assumptions:".
Abort.
Print Assumptions instantiation_msubst.
Goal True.
idtac " ".

idtac "-------------------  instantiation_env_closed  --------------------".
idtac " ".

idtac "#> instantiation_env_closed".
idtac "Possible points: 2".
check_type @instantiation_env_closed (
(forall (R : forall (_ : ty) (_ : tm), Prop) (RC : R_closed R)
   (c : tass) (e : env) (_ : instantiation R RC c e),
 closed_env e)).
idtac "Assumptions:".
Abort.
Print Assumptions instantiation_env_closed.
Goal True.
idtac " ".

idtac "-------------------  N_instantiation_preserves_typing  --------------------".
idtac " ".

idtac "#> N_instantiation_preserves_typing".
idtac "Possible points: 3".
check_type @N_instantiation_preserves_typing (
(forall (c : tass) (e : env) (_ : instantiation N N_closed c e)
   (Gamma : context) (t : tm) (S : ty) (_ : has_type (mupdate Gamma c) t S),
 has_type Gamma (msubst e t) S)).
idtac "Assumptions:".
Abort.
Print Assumptions N_instantiation_preserves_typing.
Goal True.
idtac " ".

idtac "-------------------  multistep_App2  --------------------".
idtac " ".

idtac "#> multistep_App2".
idtac "Possible points: 2".
check_type @multistep_App2 (
(forall (v t t' : tm) (_ : value v) (_ : @Smallstep.multi tm step t t'),
 @Smallstep.multi tm step (tm_app v t) (tm_app v t'))).
idtac "Assumptions:".
Abort.
Print Assumptions multistep_App2.
Goal True.
idtac " ".

idtac "-------------------  typable_N  --------------------".
idtac " ".

idtac "#> typable_N".
idtac "Possible points: 10".
check_type @typable_N (
(forall (c : tass) (t : tm) (T : ty) (_ : has_type (tass_context c) t T)
   (e : env) (_ : instantiation N N_closed c e),
 N T (msubst e t))).
idtac "Assumptions:".
Abort.
Print Assumptions typable_N.
Goal True.
idtac " ".

idtac "-------------------  Sv_products  --------------------".
idtac " ".

idtac "#> Manually graded: Sv_products".
idtac "Possible points: 3".
print_manual_grade manual_grade_for_Sv_products.
idtac " ".

idtac "-------------------  Sv_val  --------------------".
idtac " ".

idtac "#> Sv_val".
idtac "Possible points: 2".
check_type @Sv_val ((forall (T : ty) (t : tm) (_ : Sv T t), value t)).
idtac "Assumptions:".
Abort.
Print Assumptions Sv_val.
Goal True.
idtac " ".

idtac "-------------------  instantiation_closes  --------------------".
idtac " ".

idtac "#> instantiation_closes".
idtac "Possible points: 6".
check_type @instantiation_closes (
(forall (R : forall (_ : ty) (_ : tm), Prop) (RC : R_closed R)
   (c : tass) (e : env) (_ : instantiation R RC c e)
   (t : tm) (T : ty) (_ : has_type (tass_context c) t T),
 closed (msubst e t))).
idtac "Assumptions:".
Abort.
Print Assumptions instantiation_closes.
Goal True.
idtac " ".

idtac "-------------------  nf_dec  --------------------".
idtac " ".

idtac "#> nf_dec".
idtac "Possible points: 3".
check_type @nf_dec (
(forall t : tm,
 or (@Smallstep.normal_form tm step t) (@ex tm (fun t' : tm => step t t')))).
idtac "Assumptions:".
Abort.
Print Assumptions nf_dec.
Goal True.
idtac " ".

idtac "-------------------  norm_App2  --------------------".
idtac " ".

idtac "#> norm_App2".
idtac "Possible points: 2".
check_type @norm_App2 (
(forall (v1 t2 t' : tm) (_ : @Smallstep.multi tm step (tm_app v1 t2) t')
   (_ : value v1) (_ : @Smallstep.normal_form tm step t'),
 @ex tm
   (fun t2' : tm =>
    and (@Smallstep.multi tm step t2 t2')
      (and (@Smallstep.normal_form tm step t2')
         (@Smallstep.multi tm step (tm_app v1 t2') t'))))).
idtac "Assumptions:".
Abort.
Print Assumptions norm_App2.
Goal True.
idtac " ".

idtac "-------------------  syntactic_type_semantic  --------------------".
idtac " ".

idtac "#> syntactic_type_semantic".
idtac "Possible points: 10".
check_type @syntactic_type_semantic (
(forall (Gamma : context) (t : tm) (T : ty) (_ : has_type Gamma t T),
 has_semantic_type Gamma t T)).
idtac "Assumptions:".
Abort.
Print Assumptions syntactic_type_semantic.
Goal True.
idtac " ".

idtac " ".

idtac "Max points - standard: 73".
idtac "Max points - advanced: 73".
idtac "".
idtac "Allowed Axioms:".
idtac "functional_extensionality".
idtac "FunctionalExtensionality.functional_extensionality_dep".
idtac "CSeq_congruence".
idtac "fold_constants_bexp_sound".
idtac "succ_hastype_nat__hastype_nat".
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
idtac "---------- norm_fail ---------".
idtac "MANUAL".
idtac "---------- value_halts ---------".
Print Assumptions value_halts.
idtac "---------- step_preserves_halting ---------".
Print Assumptions step_preserves_halting.
idtac "---------- N_products ---------".
idtac "MANUAL".
idtac "---------- step_preserves_N ---------".
Print Assumptions step_preserves_N.
idtac "---------- step_preserves_N' ---------".
Print Assumptions step_preserves_N'.
idtac "---------- swap_subst ---------".
Print Assumptions swap_subst.
idtac "---------- msubst_subst ---------".
Print Assumptions msubst_subst.
idtac "---------- msubst_app ---------".
Print Assumptions msubst_app.
idtac "---------- instantiation_msubst ---------".
Print Assumptions instantiation_msubst.
idtac "---------- instantiation_env_closed ---------".
Print Assumptions instantiation_env_closed.
idtac "---------- N_instantiation_preserves_typing ---------".
Print Assumptions N_instantiation_preserves_typing.
idtac "---------- multistep_App2 ---------".
Print Assumptions multistep_App2.
idtac "---------- typable_N ---------".
Print Assumptions typable_N.
idtac "---------- Sv_products ---------".
idtac "MANUAL".
idtac "---------- Sv_val ---------".
Print Assumptions Sv_val.
idtac "---------- instantiation_closes ---------".
Print Assumptions instantiation_closes.
idtac "---------- nf_dec ---------".
Print Assumptions nf_dec.
idtac "---------- norm_App2 ---------".
Print Assumptions norm_App2.
idtac "---------- syntactic_type_semantic ---------".
Print Assumptions syntactic_type_semantic.
idtac "".
idtac "********** Advanced **********".
Abort.

(* 2026-08-24 10:05 *)

(* 2026-08-24 10:06 *)
