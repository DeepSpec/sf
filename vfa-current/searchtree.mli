
type key = int

type 'v tree =
| E
| T of 'v tree * key * 'v * 'v tree

val empty_tree : 'a1 tree

val lookup : 'a1 -> key -> 'a1 tree -> 'a1

val insert : key -> 'a1 -> 'a1 tree -> 'a1 tree

val elements_tr : 'a1 tree -> (key*'a1) list -> (key*'a1) list

val elements : 'a1 tree -> (key*'a1) list
