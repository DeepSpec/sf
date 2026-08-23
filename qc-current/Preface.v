(** * Preface *)

(** This volume of _Software Foundations_ introduces QuickChick, a
    property-based random testing tool for Rocq. *)

(* ################################################################# *)
(** * Setup *)

(** For working with this material, you will need to install
    QuickChick. This version of the book requires QuickChick 2.2 or
    later, which can be installed by simply running:

    [ opam install coq-quickchick ]

    If you already have an earlier version, upgrade it with

    [ opam upgrade coq-quickchick ]

    (QuickChick 2.2 renamed the command for automatic instance
    derivation from [Derive] to [QCDerive], so the examples here will
    not compile against older versions.)

    The [QuickChickInterface] chapter serves as a reference
    manual for QuickChick.  The rest of the book explains its features
    more gently. *)

(* ################################################################# *)
(** * Practicalities *)
(* ================================================================= *)
(** ** Recommended Citation Format *)

(** If you want to refer to this volume in your own writing, please
    do so as follows:

    @book            {Lampropoulos:SF4,
    author       =   {Leonidas Lampropoulos and Benjamin C. Pierce},
    editor       =   {Benjamin C. Pierce},
    title        =   "QuickChick: Property-Based Testing in Rocq",
    series       =   "Software Foundations",
    volume       =   "4",
    year         =   "2026",
    publisher    =   "Electronic textbook",
    note         =   {Version 2.1, \URL{http://softwarefoundations.cis.upenn.edu} },
    }
*)

(* ################################################################# *)
(** * Thanks *)

(** Development of the _Software Foundations_ series has been
    supported, in part, by the National Science Foundation under the
    NSF Expeditions grant 1521523, _The Science of Deep
    Specification_.  Work on this volume was also supported by NSF
    grant 1421243, _Random Testing for Language Design_. *)

(* 2026-08-23 16:01 *)
