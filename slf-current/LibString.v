(* This file is extracted from the TLC library.
   http://github.com/charguer/tlc
   DO NOT EDIT. *)

(**************************************************************************
* TLC: A library for Coq                                                  *
* Strings                                                                 *
**************************************************************************)

Set Implicit Arguments.
From SLF Require Import LibTactics LibReflect.
Require Export Coq.Strings.String.

(* ********************************************************************** *)
(* ################################################################# *)
(** * Inhabited *)

Instance Inhab_string : Inhab string.
Proof using. apply (Inhab_of_val EmptyString). Qed.

(* 2022-02-25 13:46 *)
