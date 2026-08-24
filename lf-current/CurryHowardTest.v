Set Warnings "-notation-overridden,-parsing".
From Stdlib Require Export String.
From LF Require Import CurryHoward.

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

From LF Require Import CurryHoward.
Import Check.

Goal True.

idtac "-------------------  ex_PQR_provable  --------------------".
idtac " ".

idtac "#> Implicational.ex_PQR_provable_rocq".
idtac "Possible points: 0.5".
check_type @Implicational.ex_PQR_provable_rocq (
(forall (P Q R : Prop) (_ : forall (_ : P) (_ : Q), R)
   (_ : forall _ : P, Q) (_ : P),
 R)).
idtac "Assumptions:".
Abort.
Print Assumptions Implicational.ex_PQR_provable_rocq.
Goal True.
idtac " ".

idtac "#> Implicational.ex_PQR_provable_nd".
idtac "Possible points: 1.5".
check_type @Implicational.ex_PQR_provable_nd (
(Implicational.provable (@nil Implicational.proposition) Implicational.ex_PQR)).
idtac "Assumptions:".
Abort.
Print Assumptions Implicational.ex_PQR_provable_nd.
Goal True.
idtac " ".

idtac "-------------------  more_provable_propositions  --------------------".
idtac " ".

idtac "#> Implicational.implies_trans".
idtac "Possible points: 1".
check_type @Implicational.implies_trans (
(forall P Q R : String.string,
 Implicational.provable (@nil Implicational.proposition)
   (Implicational.implies
      (Implicational.implies (Implicational.atom P) (Implicational.atom Q))
      (Implicational.implies
         (Implicational.implies (Implicational.atom Q) (Implicational.atom R))
         (Implicational.implies (Implicational.atom P) (Implicational.atom R)))))).
idtac "Assumptions:".
Abort.
Print Assumptions Implicational.implies_trans.
Goal True.
idtac " ".

idtac "#> Implicational.exfalso_quodlibet".
idtac "Possible points: 1".
check_type @Implicational.exfalso_quodlibet (
(forall P : String.string,
 Implicational.provable (@nil Implicational.proposition)
   (Implicational.implies Implicational.false (Implicational.atom P)))).
idtac "Assumptions:".
Abort.
Print Assumptions Implicational.exfalso_quodlibet.
Goal True.
idtac " ".

idtac "#> Implicational.contrapositive".
idtac "Possible points: 1".
check_type @Implicational.contrapositive (
(forall P Q : String.string,
 Implicational.provable (@nil Implicational.proposition)
   (Implicational.implies
      (Implicational.implies (Implicational.atom P) (Implicational.atom Q))
      (Implicational.implies (Implicational.not (Implicational.atom Q))
         (Implicational.not (Implicational.atom P)))))).
idtac "Assumptions:".
Abort.
Print Assumptions Implicational.contrapositive.
Goal True.
idtac " ".

idtac "-------------------  e_S_typable  --------------------".
idtac " ".

idtac "#> Implicational.e_S_typable".
idtac "Possible points: 2".
check_type @Implicational.e_S_typable (
(Implicational.hastype (@nil (prod String.string Implicational.type))
   Implicational.e_S
   (Implicational.arrow
      (Implicational.arrow
         (Implicational.tvar
            (String.String
               (Ascii.Ascii false false true false true false true false)
               String.EmptyString))
         (Implicational.arrow
            (Implicational.tvar
               (String.String
                  (Ascii.Ascii true false true false true false true false)
                  String.EmptyString))
            (Implicational.tvar
               (String.String
                  (Ascii.Ascii false true true false true false true false)
                  String.EmptyString))))
      (Implicational.arrow
         (Implicational.arrow
            (Implicational.tvar
               (String.String
                  (Ascii.Ascii false false true false true false true false)
                  String.EmptyString))
            (Implicational.tvar
               (String.String
                  (Ascii.Ascii true false true false true false true false)
                  String.EmptyString)))
         (Implicational.arrow
            (Implicational.tvar
               (String.String
                  (Ascii.Ascii false false true false true false true false)
                  String.EmptyString))
            (Implicational.tvar
               (String.String
                  (Ascii.Ascii false true true false true false true false)
                  String.EmptyString))))))).
idtac "Assumptions:".
Abort.
Print Assumptions Implicational.e_S_typable.
Goal True.
idtac " ".

idtac "-------------------  more_typable_programs  --------------------".
idtac " ".

idtac "#> Implicational.prog_B_typable".
idtac "Possible points: 1".
check_type @Implicational.prog_B_typable (
(@ex Implicational.type
   (fun T : Implicational.type =>
    Implicational.hastype (@nil (prod String.string Implicational.type))
      Implicational.prog_B T))).
idtac "Assumptions:".
Abort.
Print Assumptions Implicational.prog_B_typable.
Goal True.
idtac " ".

idtac "#> Implicational.prog_C_typable".
idtac "Possible points: 1".
check_type @Implicational.prog_C_typable (
(@ex Implicational.type
   (fun T : Implicational.type =>
    Implicational.hastype (@nil (prod String.string Implicational.type))
      Implicational.prog_C T))).
idtac "Assumptions:".
Abort.
Print Assumptions Implicational.prog_C_typable.
Goal True.
idtac " ".

idtac "#> Implicational.prog_W_typable".
idtac "Possible points: 1".
check_type @Implicational.prog_W_typable (
(@ex Implicational.expr
   (fun e : Implicational.expr =>
    Implicational.hastype (@nil (prod String.string Implicational.type)) e
      Implicational.prog_W_type))).
idtac "Assumptions:".
Abort.
Print Assumptions Implicational.prog_W_typable.
Goal True.
idtac " ".

idtac "-------------------  in_snd  --------------------".
idtac " ".

idtac "#> Implicational.in_snd".
idtac "Possible points: 2".
check_type @Implicational.in_snd (
(forall (X Y Z : Type) (x : X) (y : Y) (f : forall _ : Y, Z)
   (l : list (prod X Y)) (_ : @List.In (prod X Y) (@pair X Y x y) l),
 @List.In Z (f y)
   (@ListDef.map Y Z f (@ListDef.map (prod X Y) Y (@snd X Y) l)))).
idtac "Assumptions:".
Abort.
Print Assumptions Implicational.in_snd.
Goal True.
idtac " ".

idtac "-------------------  curry_howard  --------------------".
idtac " ".

idtac "#> Implicational.curry_howard".
idtac "Possible points: 3".
check_type @Implicational.curry_howard (
(forall (E : Implicational.tenv) (e : Implicational.expr)
   (t : Implicational.type) (_ : Implicational.hastype E e t),
 Implicational.provable (Implicational.assumptions_of_tenv E)
   (Implicational.proposition_of_type t))).
idtac "Assumptions:".
Abort.
Print Assumptions Implicational.curry_howard.
Goal True.
idtac " ".

idtac "-------------------  false_iff_inconsistency  --------------------".
idtac " ".

idtac "#> Propositional.false_iff_inconsistency".
idtac "Possible points: 2".
check_type @Propositional.false_iff_inconsistency (
(forall p : Propositional.proposition,
 Propositional.provable (@nil Propositional.proposition)
   (Propositional.iff Propositional.false
      (Propositional.and p (Propositional.not p))))).
idtac "Assumptions:".
Abort.
Print Assumptions Propositional.false_iff_inconsistency.
Goal True.
idtac " ".

idtac "-------------------  and_comm  --------------------".
idtac " ".

idtac "#> Propositional.and_comm".
idtac "Possible points: 2".
check_type @Propositional.and_comm (
(forall p q : Propositional.proposition,
 Propositional.provable (@nil Propositional.proposition)
   (Propositional.iff (Propositional.and p q) (Propositional.and q p)))).
idtac "Assumptions:".
Abort.
Print Assumptions Propositional.and_comm.
Goal True.
idtac " ".

idtac "-------------------  or_comm  --------------------".
idtac " ".

idtac "#> Propositional.or_comm".
idtac "Possible points: 2".
check_type @Propositional.or_comm (
(forall p q : Propositional.proposition,
 Propositional.provable (@nil Propositional.proposition)
   (Propositional.iff (Propositional.or p q) (Propositional.or q p)))).
idtac "Assumptions:".
Abort.
Print Assumptions Propositional.or_comm.
Goal True.
idtac " ".

idtac "-------------------  and_distr_or  --------------------".
idtac " ".

idtac "#> Propositional.and_distr_or".
idtac "Possible points: 3".
check_type @Propositional.and_distr_or (
(forall p q r : Propositional.proposition,
 Propositional.provable (@nil Propositional.proposition)
   (Propositional.iff (Propositional.and p (Propositional.or q r))
      (Propositional.or (Propositional.and p q) (Propositional.and p r))))).
idtac "Assumptions:".
Abort.
Print Assumptions Propositional.and_distr_or.
Goal True.
idtac " ".

idtac "-------------------  swap_product  --------------------".
idtac " ".

idtac "#> Propositional.swap_product".
idtac "Possible points: 2".
check_type @Propositional.swap_product (
(forall t1 t2 : Propositional.type,
 @ex Propositional.expr
   (fun e : Propositional.expr =>
    Propositional.hastype (@nil (prod String.string Propositional.type)) e
      (Propositional.arrow (Propositional.product t1 t2)
         (Propositional.product t2 t1))))).
idtac "Assumptions:".
Abort.
Print Assumptions Propositional.swap_product.
Goal True.
idtac " ".

idtac "-------------------  swap_sum  --------------------".
idtac " ".

idtac "#> Propositional.swap_sum".
idtac "Possible points: 2".
check_type @Propositional.swap_sum (
(forall t1 t2 : Propositional.type,
 @ex Propositional.expr
   (fun e : Propositional.expr =>
    Propositional.hastype (@nil (prod String.string Propositional.type)) e
      (Propositional.arrow (Propositional.sum t1 t2)
         (Propositional.sum t2 t1))))).
idtac "Assumptions:".
Abort.
Print Assumptions Propositional.swap_sum.
Goal True.
idtac " ".

idtac "-------------------  product_of_sum__sum_of_product  --------------------".
idtac " ".

idtac "#> Propositional.product_of_sum__sum_of_product".
idtac "Possible points: 3".
check_type @Propositional.product_of_sum__sum_of_product (
(forall t1 t2 t3 : Propositional.type,
 @ex Propositional.expr
   (fun e : Propositional.expr =>
    Propositional.hastype (@nil (prod String.string Propositional.type)) e
      (Propositional.arrow
         (Propositional.product t1 (Propositional.sum t2 t3))
         (Propositional.sum (Propositional.product t1 t2)
            (Propositional.product t1 t3)))))).
idtac "Assumptions:".
Abort.
Print Assumptions Propositional.product_of_sum__sum_of_product.
Goal True.
idtac " ".

idtac "-------------------  curry_howard_extended  --------------------".
idtac " ".

idtac "#> Propositional.curry_howard_extended".
idtac "Possible points: 3".
check_type @Propositional.curry_howard_extended (
(forall (E : Propositional.tenv) (e : Propositional.expr)
   (t : Propositional.type) (_ : Propositional.hastype E e t),
 Propositional.provable (Propositional.assumptions_of_tenv E)
   (Propositional.proposition_of_type t))).
idtac "Assumptions:".
Abort.
Print Assumptions Propositional.curry_howard_extended.
Goal True.
idtac " ".

idtac "-------------------  curry_howard_converse  --------------------".
idtac " ".

idtac "#> Propositional.curry_howard_converse".
idtac "Advanced".
idtac "Possible points: 6".
check_type @Propositional.curry_howard_converse (
(forall (A : list Propositional.proposition) (p : Propositional.proposition)
   (_ : Propositional.provable A p),
 @ex Propositional.expr
   (fun e : Propositional.expr =>
    Propositional.hastype (Propositional.tenv_of_assumptions A) e
      (Propositional.type_of_proposition p)))).
idtac "Assumptions:".
Abort.
Print Assumptions Propositional.curry_howard_converse.
Goal True.
idtac " ".

idtac " ".

idtac "Max points - standard: 34".
idtac "Max points - advanced: 40".
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
idtac "---------- Implicational.ex_PQR_provable_rocq ---------".
Print Assumptions Implicational.ex_PQR_provable_rocq.
idtac "---------- Implicational.ex_PQR_provable_nd ---------".
Print Assumptions Implicational.ex_PQR_provable_nd.
idtac "---------- Implicational.implies_trans ---------".
Print Assumptions Implicational.implies_trans.
idtac "---------- Implicational.exfalso_quodlibet ---------".
Print Assumptions Implicational.exfalso_quodlibet.
idtac "---------- Implicational.contrapositive ---------".
Print Assumptions Implicational.contrapositive.
idtac "---------- Implicational.e_S_typable ---------".
Print Assumptions Implicational.e_S_typable.
idtac "---------- Implicational.prog_B_typable ---------".
Print Assumptions Implicational.prog_B_typable.
idtac "---------- Implicational.prog_C_typable ---------".
Print Assumptions Implicational.prog_C_typable.
idtac "---------- Implicational.prog_W_typable ---------".
Print Assumptions Implicational.prog_W_typable.
idtac "---------- Implicational.in_snd ---------".
Print Assumptions Implicational.in_snd.
idtac "---------- Implicational.curry_howard ---------".
Print Assumptions Implicational.curry_howard.
idtac "---------- Propositional.false_iff_inconsistency ---------".
Print Assumptions Propositional.false_iff_inconsistency.
idtac "---------- Propositional.and_comm ---------".
Print Assumptions Propositional.and_comm.
idtac "---------- Propositional.or_comm ---------".
Print Assumptions Propositional.or_comm.
idtac "---------- Propositional.and_distr_or ---------".
Print Assumptions Propositional.and_distr_or.
idtac "---------- Propositional.swap_product ---------".
Print Assumptions Propositional.swap_product.
idtac "---------- Propositional.swap_sum ---------".
Print Assumptions Propositional.swap_sum.
idtac "---------- Propositional.product_of_sum__sum_of_product ---------".
Print Assumptions Propositional.product_of_sum__sum_of_product.
idtac "---------- Propositional.curry_howard_extended ---------".
Print Assumptions Propositional.curry_howard_extended.
idtac "".
idtac "********** Advanced **********".
idtac "---------- Propositional.curry_howard_converse ---------".
Print Assumptions Propositional.curry_howard_converse.
Abort.

(* 2026-08-24 09:55 *)

(* 2026-08-24 09:55 *)
