(** * Preface *)

(* ################################################################# *)
(** * Formal foundations for program security *)

(** This volume uses Rocq to lay down formal foundations for the security of
    programs, by (1) setting clear _security goals_, (2) investigating
    _enforcement mechanisms_, and (3) _proving_ that the mechanisms achieve
    their goals.  In a bit more detail: *)

(** (1) We set clear _security goals_ by mathematically defining what it means
    for a program to be secure with respect to a precise attacker model.
    The security goals we investigate are various information-flow
    security properties, formalized as variants of noninterference.
    Noninterference precisely expresses what it means for a program
    to not leak secrets to attackers with various capabilities.
    For instance, we investigate attackers that can observe (part of)
    the final result or state of the computation, or explicit program outputs
    happening during execution, or side-channel observations
    (e.g., the branches and memory addresses accessed by the program,
    as assumed by cryptographic constant-time programming discipline).
    We also investigate Spectre attackers that can influence the program by
    causing speculative execution to take the wrong branch in a conditional. *)

(** (2) We investigate various static and dynamic information-flow control
    _enforcement mechanisms_ aimed at achieving specific noninterference
    properties. In particular we investigate enforcement via various security
    type systems, secure multi-execution, and a program transformation called
    Speculative Load Hardening (SLH). *)

(** (3) Finally, we _prove_ in Rocq that these enforcement mechanisms do indeed
    achieve their desired security goal. For instance, we prove that a standard
    type system that prevents branch conditions and memory accesses that may
    depend on secrets indeed achieves cryptographic constant-time security, and
    also that together with the SLH transformation it achieves speculative
    constant-time security. *)

(* ################################################################# *)
(** * Expected audience *)

(** This volume can be of interest to anyone curious about the security
    applications of the concepts from the _Logical Foundations_ volume and, more
    generally, those interested in a formal approach to security that is
    solidly grounded in fully mechanized Rocq proofs. This volume can also serve
    as a start for research in this area, and the [Postscript] presents a
    few illustrative security research projects involving machine-checked proofs.

    This volume directly builds on the material in the _Logical Foundations_
    volume and the two can be used together in a one-semester course.  We try
    not to assume prior knowledge in security and would appreciate your feedback
    if you find places in the volume where this can be improved. *)

(* ################################################################# *)
(** * Further reading *)

(** This volume is intended to be self-contained, but readers looking for a
    deeper treatment of particular topics will find some suggestions for further
    reading as citations in the technical chapters and in the [Postscript]
    chapter. Bibliographic information for all cited works can be found in the
    [Bib] file. *)

(* ################################################################# *)
(** * Recommended citation format *)

(** If you want to refer to this volume in your own writing,
    please do so as follows:

    @book            {Hritcu:SF7,
    author       =   {  Cătălin Hriţcu and
  Yonghyun Kim},
    editor       =   {Benjamin C. Pierce},
    title        =   "Security Foundations",
    series       =   "Software Foundations",
    volume       =   "7",
    year         =   "2026",
    publisher    =   "Electronic textbook",
    note         =   {Version 1.2,
                      \URL{http://softwarefoundations.cis.upenn.edu} },
    }
*)

(* ################################################################# *)
(** * Feedback or any other contribution welcome *)

(** We plan to continue improving and expanding this volume, so any feedback on
    it or any other contribution would be much appreciated. *)

(* ################################################################# *)
(** * Thanks *)

(** This volume originated from teaching materials for courses we taught at Ruhr
    Uni Bochum and we would like to thank the students taking these courses for
    putting up with very rough early drafts of these materials.  We also thank
    all people who have contributed to this volume (the people we remembered are
    listed on the cover page of this volume).  *)

(* 2026-08-23 16:10 *)
