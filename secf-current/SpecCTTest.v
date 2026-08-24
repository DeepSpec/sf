Set Warnings "-notation-overridden,-parsing".
From Stdlib Require Export String.
From SECF Require Import SpecCT.

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

From SECF Require Import SpecCT.
Import Check.

Goal True.

idtac "-------------------  cct_insecure_store_is_not_cct_secure  --------------------".
idtac " ".

idtac "#> cct_insecure_store_is_not_cct_secure".
idtac "Possible points: 2".
check_type @cct_insecure_store_is_not_cct_secure (
(not (cct_secure LXYZpub LAPpub cct_insecure_store))).
idtac "Assumptions:".
Abort.
Print Assumptions cct_insecure_store_is_not_cct_secure.
Goal True.
idtac " ".

idtac "-------------------  fixing_cct_insecure_branch  --------------------".
idtac " ".

idtac "#> cct_fixed_branch_spec".
idtac "Possible points: 3".
check_type @cct_fixed_branch_spec (
(and (@eq bool (cct_typechecker LXYZpub LAPpub cct_fixed_branch) true)
   (forall (s : state) (m : mem) (s' : state) (m' : mem)
      (os : obs) (_ : cteval cct_insecure_branch s m s' m' os),
    @ex obs (fun os' : obs => cteval cct_fixed_branch s m s' m' os')))).
idtac "Assumptions:".
Abort.
Print Assumptions cct_fixed_branch_spec.
Goal True.
idtac " ".

idtac "-------------------  fixing_cct_insecure_load  --------------------".
idtac " ".

idtac "#> cct_fixed_load_spec".
idtac "Advanced".
idtac "Possible points: 6".
check_type @cct_fixed_load_spec (
(and (@eq bool (cct_typechecker LXYZpub LAPpub cct_fixed_load) true)
   (forall (s : state) (m : forall _ : String.string, list nat)
      (a0 a1 : nat) (s' : state) (os : obs)
      (_ : @eq (list nat) (m AP) (@cons nat a0 (@cons nat a1 (@nil nat))))
      (_ : cteval cct_insecure_load s m s' m os),
    @ex state
      (fun s'' : state =>
       @ex obs
         (fun os' : obs =>
          and (cteval cct_fixed_load s m s'' m os') (@eq nat (s'' V) (s' V))))))).
idtac "Assumptions:".
Abort.
Print Assumptions cct_fixed_load_spec.
Goal True.
idtac " ".

idtac "-------------------  cct_well_typed_div  --------------------".
idtac " ".

idtac "#> Manually graded: Div.cct_well_typed_div".
idtac "Possible points: 1".
print_manual_grade Div.manual_grade_for_cct_well_typed_div.
idtac " ".

idtac "-------------------  cct_well_typed_div_noninterferent  --------------------".
idtac " ".

idtac "#> Div.cct_well_typed_div_noninterferent".
idtac "Possible points: 2".
check_type @Div.cct_well_typed_div_noninterferent (
(forall (L LA : label_map) (c : Div.com) (s1 s2 : Maps.total_map nat)
   (m1 m2 : Maps.total_map (list nat)) (s1' s2' : state)
   (m1' m2' : mem) (os1 os2 : Div.obs) (_ : Div.cct_well_typed L LA c)
   (_ : @pub_equiv L nat s1 s2) (_ : @pub_equiv LA (list nat) m1 m2)
   (_ : Div.cteval c s1 m1 s1' m1' os1) (_ : Div.cteval c s2 m2 s2' m2' os2),
 and (@pub_equiv L nat s1' s2') (@pub_equiv LA (list nat) m1' m2'))).
idtac "Assumptions:".
Abort.
Print Assumptions Div.cct_well_typed_div_noninterferent.
Goal True.
idtac " ".

idtac "-------------------  cct_well_typed_div_secure  --------------------".
idtac " ".

idtac "#> Div.cct_well_typed_div_secure".
idtac "Possible points: 2".
check_type @Div.cct_well_typed_div_secure (
(forall (L LA : label_map) (c : Div.com) (_ : Div.cct_well_typed L LA c),
 Div.cct_secure L LA c)).
idtac "Assumptions:".
Abort.
Print Assumptions Div.cct_well_typed_div_secure.
Goal True.
idtac " ".

idtac "-------------------  speculation_bit_monotonic  --------------------".
idtac " ".

idtac "#> speculation_bit_monotonic".
idtac "Possible points: 1".
check_type @speculation_bit_monotonic (
(forall (c : com) (s : state) (a : mem) (b : bool)
   (ds : dirs) (s' : state) (a' : mem) (b' : bool)
   (os : obs) (_ : spec_eval c s a b ds s' a' b' os)
   (_ : @eq bool b true),
 @eq bool b' true)).
idtac "Assumptions:".
Abort.
Print Assumptions speculation_bit_monotonic.
Goal True.
idtac " ".

idtac "-------------------  ct_well_typed_seq_spec_eval_ct_secure  --------------------".
idtac " ".

idtac "#> ct_well_typed_seq_spec_eval_ct_secure".
idtac "Possible points: 1".
check_type @ct_well_typed_seq_spec_eval_ct_secure (
(forall (L LA : label_map) (c : com) (s1 s2 : Maps.total_map nat)
   (m1 m2 : Maps.total_map (list nat)) (s1' s2' : state)
   (m1' m2' : mem) (os1 os2 : obs) (_ : cct_well_typed L LA c)
   (_ : @pub_equiv L nat s1 s2) (_ : @pub_equiv LA (list nat) m1 m2)
   (_ : seq_spec_eval c s1 m1 s1' m1' os1)
   (_ : seq_spec_eval c s2 m2 s2' m2' os2),
 @eq obs os1 os2)).
idtac "Assumptions:".
Abort.
Print Assumptions ct_well_typed_seq_spec_eval_ct_secure.
Goal True.
idtac " ".

idtac "-------------------  sel_slh_store_then_load  --------------------".
idtac " ".

idtac "#> Manually graded: sel_slh_store_then_load".
idtac "Possible points: 2".
print_manual_grade manual_grade_for_sel_slh_store_then_load.
idtac " ".

idtac " ".

idtac "Max points - standard: 14".
idtac "Max points - advanced: 20".
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
idtac "---------- cct_insecure_store_is_not_cct_secure ---------".
Print Assumptions cct_insecure_store_is_not_cct_secure.
idtac "---------- cct_fixed_branch_spec ---------".
Print Assumptions cct_fixed_branch_spec.
idtac "---------- cct_well_typed_div ---------".
idtac "MANUAL".
idtac "---------- Div.cct_well_typed_div_noninterferent ---------".
Print Assumptions Div.cct_well_typed_div_noninterferent.
idtac "---------- Div.cct_well_typed_div_secure ---------".
Print Assumptions Div.cct_well_typed_div_secure.
idtac "---------- speculation_bit_monotonic ---------".
Print Assumptions speculation_bit_monotonic.
idtac "---------- ct_well_typed_seq_spec_eval_ct_secure ---------".
Print Assumptions ct_well_typed_seq_spec_eval_ct_secure.
idtac "---------- sel_slh_store_then_load ---------".
idtac "MANUAL".
idtac "".
idtac "********** Advanced **********".
idtac "---------- cct_fixed_load_spec ---------".
Print Assumptions cct_fixed_load_spec.
Abort.

(* 2026-08-24 10:13 *)

(* 2026-08-24 10:13 *)
