Set Warnings "-notation-overridden,-parsing".
From Coq Require Export String.
From VFA Require Import SearchTree.

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

From VFA Require Import SearchTree.
Import Check.

Goal True.

idtac "-------------------  example_map  --------------------".
idtac " ".

idtac "#> example_map".
idtac "Possible points: 2".
check_type @example_map ((forall V : Type, V -> V -> V -> V -> Maps.total_map V)).
idtac "Assumptions:".
Abort.
Print Assumptions example_map.
Goal True.
idtac " ".

idtac "-------------------  check_example_map  --------------------".
idtac " ".

idtac "#> check_example_map".
idtac "Possible points: 3".
check_type @check_example_map (
(forall (V : Type) (default v2 v4 v5 : V),
 Abs V default (example_tree V v2 v4 v5) (example_map V default v2 v4 v5))).
idtac "Assumptions:".
Abort.
Print Assumptions check_example_map.
Goal True.
idtac " ".

idtac "-------------------  lookup_relate  --------------------".
idtac " ".

idtac "#> lookup_relate".
idtac "Possible points: 3".
check_type @lookup_relate (
(forall (V : Type) (default : V) (k : key) (t : tree V)
   (cts : Maps.total_map V),
 Abs V default t cts -> lookup V default k t = cts k)).
idtac "Assumptions:".
Abort.
Print Assumptions lookup_relate.
Goal True.
idtac " ".

idtac "-------------------  insert_relate  --------------------".
idtac " ".

idtac "#> insert_relate".
idtac "Possible points: 6".
check_type @insert_relate (
(forall (V : Type) (default : V) (k : key) (v : V) 
   (t : tree V) (cts : Maps.total_map V),
 Abs V default t cts ->
 Abs V default (insert V k v t) (@Maps.t_update V cts k v))).
idtac "Assumptions:".
Abort.
Print Assumptions insert_relate.
Goal True.
idtac " ".

idtac "-------------------  elements_relate_informal  --------------------".
idtac " ".

idtac "#> Manually graded: elements_relate_informal".
idtac "Possible points: 3".
print_manual_grade manual_grade_for_elements_relate_informal.
idtac " ".

idtac "-------------------  not_elements_relate  --------------------".
idtac " ".

idtac "#> not_elements_relate".
idtac "Possible points: 6".
check_type @not_elements_relate (
(forall (V : Type) (default v : V),
 v <> default ->
 ~
 (forall (t : tree V) (cts : Maps.total_map V),
  Abs V default t cts -> list2map V default (elements V t) = cts))).
idtac "Assumptions:".
Abort.
Print Assumptions not_elements_relate.
Goal True.
idtac " ".

idtac "-------------------  empty_tree_SearchTree  --------------------".
idtac " ".

idtac "#> empty_tree_SearchTree".
idtac "Possible points: 1".
check_type @empty_tree_SearchTree ((forall V : Type, SearchTree V (empty_tree V))).
idtac "Assumptions:".
Abort.
Print Assumptions empty_tree_SearchTree.
Goal True.
idtac " ".

idtac "-------------------  insert_SearchTree  --------------------".
idtac " ".

idtac "#> insert_SearchTree".
idtac "Possible points: 3".
check_type @insert_SearchTree (
(forall (V : Type) (k : key) (v : V) (t : tree V),
 SearchTree V t -> SearchTree V (insert V k v t))).
idtac "Assumptions:".
Abort.
Print Assumptions insert_SearchTree.
Goal True.
idtac " ".

idtac "-------------------  can_relate  --------------------".
idtac " ".

idtac "#> can_relate".
idtac "Possible points: 2".
check_type @can_relate (
(forall (V : Type) (default : V) (t : tree V),
 SearchTree V t -> exists cts : Maps.total_map V, Abs V default t cts)).
idtac "Assumptions:".
Abort.
Print Assumptions can_relate.
Goal True.
idtac " ".

idtac "-------------------  unrealistically_strong_can_relate  --------------------".
idtac " ".

idtac "#> unrealistically_strong_can_relate".
idtac "Possible points: 2".
check_type @unrealistically_strong_can_relate (
(forall (V : Type) (default : V) (t : tree V),
 exists cts : Maps.total_map V, Abs V default t cts)).
idtac "Assumptions:".
Abort.
Print Assumptions unrealistically_strong_can_relate.
Goal True.
idtac " ".

idtac " ".

idtac "Max points - standard: 31".
idtac "Max points - advanced: 31".
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
idtac "---------- example_map ---------".
Print Assumptions example_map.
idtac "---------- check_example_map ---------".
Print Assumptions check_example_map.
idtac "---------- lookup_relate ---------".
Print Assumptions lookup_relate.
idtac "---------- insert_relate ---------".
Print Assumptions insert_relate.
idtac "---------- elements_relate_informal ---------".
idtac "MANUAL".
idtac "---------- not_elements_relate ---------".
Print Assumptions not_elements_relate.
idtac "---------- empty_tree_SearchTree ---------".
Print Assumptions empty_tree_SearchTree.
idtac "---------- insert_SearchTree ---------".
Print Assumptions insert_SearchTree.
idtac "---------- can_relate ---------".
Print Assumptions can_relate.
idtac "---------- unrealistically_strong_can_relate ---------".
Print Assumptions unrealistically_strong_can_relate.
idtac "".
idtac "********** Advanced **********".
Abort.

(* 2020-06-11 14:34:27 (UTC+00) *)
