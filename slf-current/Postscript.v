(** * Postscript: Conclusion and Perspectives *)

(* ################################################################# *)
(** * Beyond the Scope of This Course *)

(** This course has focused on the foundations of Separation Logic for
    sequential programs, and discussed the set up of tooling for computing
    weakest preconditions.

    There are numerous aspects of Separation Logic that were not covered
    in this course, including:

    - Concurrent Separation Logic, for reasoning about concurrent behaviors,
      or even, behaviors of weak memory models.
    - Automated reasoning using Separation Logic, typically for a restricted
      fragment of Separation Logic.
    - Separation Logic for low-level programs, at the byte level, and with
      assembly-style code written in continuation-passing style.
    - Separation Logic for object-oriented programs.
    - Reasoning about I/O, integer overflows, floatting-point arithmetics,
      etc. *)

(* ################################################################# *)
(** * Historical Notes *)

(** The most relevant historical notes were included near the end of each
    chapter. Additional information may be found in the ICFP'20 paper
    _Separation Logic for Sequential Programs_, by Arthur Charguéraud.
    http://www.chargueraud.org/research/2020/seq_seplogic/seq_seplogic.pdf *)

(** In addition, the reader may be interested in checking out Peter O'Hearn's
    account of the early days of Separation Logic:
    http://www0.cs.ucl.ac.uk/staff/p.ohearn/SeparationLogic/Separation_Logic/Early_Days.html *)

(* ################################################################# *)
(** * Tools Leveraging Separation Logic *)

(** Ideas of Separation Logic have had significant influence on the field
    of programming languages from various perspectives. For a broad survey
    of Separation Logic, we refer to Peter O'Hearn's CACM paper [2019].
    https://dl.acm.org/doi/10.1145/3211968
    (Make sure to also download the "supplementary material" link at the bottom
    of the page.)

    Here is a non-exhaustive list of active projects leveraging Separation
    Logic.

    - The tool "Infer" leverages for static analysis, that is, fully automated
      program analysis to produce a list of potential bugs.
      https://fbinfer.com/
      https://fbinfer.com/docs/separation-logic-and-bi-abduction/

    - The programming language "Rust" features a type system with "borrows", a
      notion directly inspired by Separation Logic.

    - The tool "VeriFast" targets C and Java programs.
      https://people.cs.kuleuven.be/~bart.jacobs/verifast  and
      https://github.com/verifast/verifast

    - The tool "Verifiable C" tool, from the VST project, targets the
      verification of C code, using interactive Coq proofs based on Separation
      Logic.
      https://vst.cs.princeton.edu/
      See also volume 5 of Software Foundations.

    - The tool "Viper" is based on a variant of Separation Logic, its front-end
      supports several languages, and its backend leverages the SMT solver Z3;
      it also supports user annotations in the code for guiding proofs.
      https://www.pm.inf.ethz.ch/research/viper.html

    - The "Isabelle Refinement Framework" leverages Separation Logic is the
      process of refining monadic high-order logic definitions into efficient
      imperative code. It can be used to produce verified ML code, as well as
      LLVM IR code.
      https://www21.in.tum.de/~lammich/pub/itp15_sepref.pdf

    - The tool "CFML", which targets the verification of OCaml programs.
      The original version of CFML leverages a version of characteristic
      formulae slightly more complicated than the one presented in this
      volume. The new version, CFML 2.0, directly leverages all the ideas
      from this course. It is still under active development.

    - The verified compiler "CakeML" implements technology similar to that
      of CFML, and leverages it to verify components from its standard library
      and from its runtime.

    - The Iris project develops advanced logics for reasoning about concurrent
      programs using Separation Logic. *)

(* ################################################################# *)
(** * Related Courses *)

(** The following courses focus on reasoning about programs, and should be of
    interest to the reader:

    - Verifiable C, volume 5 of Sofware Foundations, by Andrew Appel.
      https://softwarefoundations.cis.upenn.edu/vc-current/index.html

    - Formal Reasoning About Programs, by Adam Chlipala.
      http://adam.chlipala.net/frap/

    - The Iris tutorial, by Birkedal and Bizjak, presents the core ideas of
      Iris' concurrent Separation Logic.
      https://iris-project.org/tutorial-material.html *)

(** Teaser: Arthur Charguéraud has for project to write a follow-up course on
    practical program verification using CFML, focusing on the specification
    and verification of classic data structures and algorithms. *)

(* ################################################################# *)
(** * Acknowledgments *)

(** The lead author of this volume, Arthur Charguéraud, wishes to thank:

    - Benjamin Pierce, for demonstrating the benefits of Coq-based teaching,
      for coordinating the Software Foundations series, and for encouraging
      me to write this volume.
    - The Software Foundations (SF) community, for helping to polish the course
      material and the tooling, and contributing to the success of teaching
      using this material.
    - François Pottier, with whom I developed several extensions of Separation
      Logic, and thereby obtained a deeper understanding of this logic.
    - Jacques-Henri Jourdan, who introduced me to a number of techniques used
      in the Iris project, and contributed to the definition of [mkstruct].
    - Xavier Leroy, with whom I had numerous discussions on mechanized
      semantics.
    - Jean-Christophe Filliâtre, for numerous discussions on program
      verification.
    - Andrew Appel, Lars Birkedal, Adam Chlipala, Magnus Myreen, Gerwin Klein,
      Peter Lammich, and Zhong Shao, who kindly answered questions on related
      work aspects.

   Thanks also to users who contributed feedback and helped fixing typos:
    - Jonathan Leivent
    - Ori Lahav
    - Shachar Itzhaky.

*)

(* 2022-01-12 18:11 *)
