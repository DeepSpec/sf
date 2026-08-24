(** * Postscript *)

(* ################################################################# *)
(** * Looking Back *)

(** Here is a quick summary of the topics we covered in this volume: *)

(** ** Noninterference
- definitions for pure functions, state transformers,
  and imperative programs
- termination-insensitive noninterference (TINI)
- termination-sensitive noninterference (TSNI) *)

(** ** Secure multi-execution
- sound and transparent dynamic enforcement of TINI *)

(** ** Information-flow control type systems
- type-checkers enforcing TINI and TSNI
- for imperative programs with state and outputs *)

(** ** Side channels
- control flow security and type system enforcing it
- cryptographic constant-time security and type system enforcing it *)

(** ** Speculative execution attacks
- speculative constant-time security definition
- speculative load hardening (SLH) transformation achieving it *)

(* ################################################################# *)
(** * Looking Around *)

(** The topics above have found practical applications in system security. Below
    we highlight a few recent research projects involving machine-checked proofs: *)

(* ================================================================= *)
(** ** Proving Noninterference by Parametricity *)

(** While in [StaticIFC] we showed how to build specialized type systems
    for noninterference, research has shown that in functional programming
    languages with strong type-abstraction mechanisms, information-flow control
    can be implemented as a library. Recent research has shown that in this
    setting simple and elegant noninterference proofs can be built by relying on
    the theory of parametricity, both for libraries doing static enforcement
    [Algehed and Bernardy 2019] (in Bib.v) and for ones doing dynamic enforcement
    [Algehed et al 2021] (in Bib.v). These noninterference proofs have been
    machine-checked in Agda. *)

(* ================================================================= *)
(** ** Formal verification of a constant-time preserving C compiler *)

(** This work [Barthe et al 2020] (in Bib.v) shows that a mildly modified version of
    the CompCert verified C compiler preserves cryptographic constant-time
    security. In particular the authors prove in Rocq that the compiler does
    not introduce secret dependencies into control flow or memory access. Their
    Rocq formalization is aimed at maximizing reuse of the CompCert correctness
    proof, through the use of novel proof techniques for constant-time
    preservation. *)

(* ================================================================= *)
(** ** Jasmin programming language and compiler *)

(** Jasmin is a low-level domain-specific language for implementing
    high-assurance and high-speed cryptography [Jasmin] (in Bib.v). Jasmin programs
    can be verified for correctness, cryptographic security, and side-channel
    resistance by translation to the EasyCrypt proof assistant
    [Almeida et al 2020] (in Bib.v). The Jasmin type checker enforces cryptographic
    constant-time [Shivakumar et al 2022] (in Bib.v) and also speculative
    constant-time for manually SLH-hardened code [Shivakumar et al 2023b] (in Bib.v).
    The Jasmin compiler was formally verified in Rocq to be correct
    [Almeida et al 2020] (in Bib.v) [Arranz-Olmos et al 2025b] (in Bib.v), to preserve
    constant-time security [Barthe et al 2021] (in Bib.v), and in more recent work
    to also preserve cryptographic security [Arranz-Olmos et al 2025b] (in Bib.v).
    In recent work also a core compiler inspired by Jasmin was proved in Rocq to
    preserve speculative constant-time [Arranz-Olmos et al 2025] (in Bib.v). *)

(* ================================================================= *)
(** ** Mechanized Speculative Load Hardening *)

(** The [SpecCT] chapter and the two projects above are
    aimed at achieving security for cryptographic code. Yet Spectre attacks
    are also a serious threat for non-cryptographic code, since without any
    defenses attackers can construct "universal read gadgets" that leak a
    sensitive program's entire memory. SLH is, however, not strong enough for
    protecting code that does not respect the constant-time discipline, leading
    to the introduction of Ultimate SLH [Zhang et al 2023] (in Bib.v), which provides
    protection for arbitrary programs, but has too large an overhead for general
    use, since it conservatively assumes that all data is secret. More recent
    work introduces Flexible SLH [Baumann et al 2025] (in Bib.v), which achieves the
    best of both worlds by generalizing both the selective SLH variant from
    [SpecCT] and Ultimate SLH. Baumann et al prove in Rocq that Flexible
    SLH and Ultimate SLH satisfy a relative security property: any
    transformed program running with speculation must not leak more than what
    the source program leaks sequentially. Their Rocq formalization originated
    as an extension of the simple development from the [SpecCT] chapter.
    Another recent extension combines Ultimate SLH with protection against
    speculative control-flow hijacking attacks (Spectre BTB and RSB) into a
    formally secure defense called Triosecuris [Baumann et al 2026] (in Bib.v). *)

(* ================================================================= *)
(** ** Strong Timing Isolation of Hardware Enclaves *)

(** This work [Lau et al 2024] (in Bib.v) introduced a RISC-V processor design that is
    formally verified in Rocq to achieve strong timing isolation for enclaves,
    which is formalized in terms of "air-gapped machines". *)

(* ################################################################# *)
(** * Looking Forward *)

(** For readers interested in research, here are the main conferences
    publishing papers on formal foundations of security:
- Computer Security Foundations (CSF)
- Principles of Programming Languages (POPL)
- International Conference on Functional Programming (ICFP)
- Certified Programs and Proofs (CPP)
- Interactive Theorem Proving (ITP)
- Computer and Communications Security (CCS)
  - Formal Methods and Programming Languages track
- IEEE Security and Privacy (SP)

There are also a few workshops in this space:
- Principles of Secure Compilation (PriSC)
- Programming Languages and Analysis for Security (PLAS)
- Foundations of Computer Security (FCS)

 *)

(* 2026-08-24 10:13 *)
