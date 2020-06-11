Set Warnings "-notation-overridden,-parsing".
From Coq Require Export String.
From VFA Require Import Extract.

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

From VFA Require Import Extract.
Import Check.

Goal True.

idtac "-------------------  lookup_relate  --------------------".
idtac " ".

idtac "#> SearchTree2.lookup_relate".
idtac "Possible points: 3".
check_type @SearchTree2.lookup_relate (
(forall (V : Type) (default : V) (k : SearchTree2.key)
   (t : SearchTree2.tree V) (cts : IntMaps.total_map V),
 SearchTree2.Abs V default t cts ->
 SearchTree2.lookup V default k t = cts (int2Z k))).
idtac "Assumptions:".
Abort.
Print Assumptions SearchTree2.lookup_relate.
Goal True.
idtac " ".

idtac "-------------------  insert_relate  --------------------".
idtac " ".

idtac "#> SearchTree2.insert_relate".
idtac "Possible points: 3".
check_type @SearchTree2.insert_relate (
(forall (V : Type) (default : V) (k : SearchTree2.key) 
   (v : V) (t : SearchTree2.tree V) (cts : IntMaps.total_map V),
 SearchTree2.Abs V default t cts ->
 SearchTree2.Abs V default (SearchTree2.insert V k v t)
   (@IntMaps.t_update V cts (int2Z k) v))).
idtac "Assumptions:".
Abort.
Print Assumptions SearchTree2.insert_relate.
Goal True.
idtac " ".

idtac "-------------------  unrealistically_strong_can_relate  --------------------".
idtac " ".

idtac "#> SearchTree2.unrealistically_strong_can_relate".
idtac "Possible points: 1".
check_type @SearchTree2.unrealistically_strong_can_relate (
(forall (V : Type) (default : V) (t : SearchTree2.tree V),
 exists cts : IntMaps.total_map V, SearchTree2.Abs V default t cts)).
idtac "Assumptions:".
Abort.
Print Assumptions SearchTree2.unrealistically_strong_can_relate.
Goal True.
idtac " ".

idtac " ".

idtac "Max points - standard: 7".
idtac "Max points - advanced: 7".
idtac "".
idtac "Allowed Axioms:".
idtac "functional_extensionality".
idtac "functional_extensionality_dep".
idtac "FunctionalExtensionality.functional_extensionality_dep".
idtac "int".
idtac "int2Z".
idtac "ltb_lt".
idtac "ltb".
idtac "Extract.int".
idtac "Extract.int2Z".
idtac "Extract.ltb_lt".
idtac "Extract.ltb".
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
idtac "---------- SearchTree2.lookup_relate ---------".
Print Assumptions SearchTree2.lookup_relate.
idtac "---------- SearchTree2.insert_relate ---------".
Print Assumptions SearchTree2.insert_relate.
idtac "---------- SearchTree2.unrealistically_strong_can_relate ---------".
Print Assumptions SearchTree2.unrealistically_strong_can_relate.
idtac "".
idtac "********** Advanced **********".
Abort.

(* 2020-06-11 15:52:02 (UTC+00) *)
