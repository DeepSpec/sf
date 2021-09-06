(** * Preface *)

(* ################################################################# *)
(** * Welcome *)

(** Here's a good way to build formally verified correct software:
    - Write your program in an expressive language with a good proof
      theory (the Gallina language embedded in Coq's logic).
    - Prove it correct in Coq.
    - Extract it to ML and compile it with an optimizing ML compiler.

    Unfortunately, for some applications you cannot afford to use a
    higher-order garbage-collected functional programming language
    such as Gallina or ML.  Perhaps you are writing an
    operating-system kernel, or a bit-shuffling cryptographic
    primitive, or the runtime system and garbage-collector of your
    functional language!  In those cases, you might want to use a
    low-level imperative systems programming language such as C.

    But you still want your OS, or crypto, or GC, to be correct!  So
    you should use machine-checked program verification in Coq.  For
    that purpose, you can use _Verifiable C_, a program logic and
    proof system for C.

    What is a program logic?  One example of a program logic is the
    Hoare logic that you studied in the _Programming Language
    Foundations_ volume of this series.  (If you have not done so
    already, study the Hoare and Hoare2 chapters of that volume, and
    do the exercises.)

    Verifiable C is based on a 21st-century version of Hoare logic
    called _higher-order impredicative concurrent separation logic_.
    Back in the 20th century, computer scientists discovered that
    Hoare Logic was not very good at verifying programs with pointer
    data structures; so _separation logic_ was developed.  Hoare Logic
    was clumsy at verifying concurrent programs, so _concurrent
    separation logic_ was developed.  Hoare Logic could not handle
    higher-order object-oriented programming patterns or
    function-closures, so _higher-order impredicative program logics_
    were developed.

    This electronic book is Volume 5 of the _Software Foundations_
    series, which presents the mathematical underpinnings of reliable
    software.  The principal novelty of _Software Foundations_ is that
    it is one hundred percent formalized and machine-checked: the
    entire text is literally a script for Coq.  It is intended to be
    read alongside an interactive session with Coq.  All the details
    in the text are fully formalized in Coq, and the exercises are
    designed to be worked using Coq.

    Before studying this volume, you should be a competent user of
    Coq:
    - Study _Software Foundations Volume 1_ (Logical Foundations), and
      do the exercises!
    - Study the Hoare and Hoare2 chapters of _Software Foundations
      Volume 2_ (Programming Language Foundations), and do the
      exercises!
    - Study the Sort, SearchTree, and ADT chapters of _Software
      Foundations Volume 3_ (Verified Functional Algorithms), and do
      the exercises!

    You will also need a working knowledge of the C programming language. *)

(* ################################################################# *)
(** * Practicalities *)

(* ================================================================= *)
(** ** System Requirements *)

(** Coq runs on Windows, Linux, and OS X.  The Preface of Volume 1
   describes the Coq installation you will need.  This edition was
   built with Coq 8.13.0.

   You will need VST 2.8 installed.  You can do that either by installing
   it as part of the standard "Coq Platform" that is released with each
   new version of Coq, or using opam (the package is named coq-vst).
   At the end of this chapter is a test to make sure you have the right
   version of VST installed.

   _IF YOU USE OPAM_, you can install Coq and CoqIDE using the
     instructions at https://coq.inria.fr/opam-using.html
   and then continue with,
   - opam update   (_as necessary_)
   - opam install coq-vst.2.8 (_this will take 30 minutes or more_)

   _You do not need to install CompCert clightgen_ to do the exercises
   in this volume.  But if you wish to modify and reparse the .c files,
   or verify C programs of your own, install the CompCert verified
   optimizing C compiler.  You can get CompCert in the standard "Coq Package"
   or by opam (the package is named coq-compcert). *)

(* ================================================================= *)
(** ** Downloading the Coq Files *)

(** A tar file containing the full sources for the "release version"
    of this book (as a collection of Coq scripts and HTML files) is
    available at {https://softwarefoundations.cis.upenn.edu}.

    (If you are using the book as part of a class, your professor may
    give you access to a locally modified version of the files, which
    you should use instead of the release version.) *)

(* ================================================================= *)
(** ** Installation *)

(** Unpack the [vc.tgz] tar file into a vc directory.
    In this [vc] directory, the [make] command builds it. *)

(* ================================================================= *)
(** ** Exercises *)

(** Each chapter includes exercises.  Each is marked with a
    "star rating," which can be interpreted as follows:

       - One star: easy exercises that underscore points in the text
         and that, for most readers, should take only a minute or two.
         Get in the habit of working these as you reach them.

       - Two stars: straightforward exercises (five or ten minutes).

       - Three stars: exercises requiring a bit of thought (ten
         minutes to half an hour).

       - Four and five stars: more difficult exercises (half an hour
         and up).

    _Please do not post solutions to the exercises in any public place_: 
    Software Foundations is widely used both for self-study and for
    university courses.  Having solutions easily available makes it
    much less useful for courses, which typically have graded homework
    assignments.  The authors especially request that readers not post
    solutions to the exercises anyplace where they can be found by
    search engines. *)

(* ================================================================= *)
(** ** Recommended Citation Format *)

(** If you want to refer to this volume in your own writing, please
    do so as follows:

    @book            {Appel:SF5,
    author       =   {Andrew W. Appel, Lennart Beringer, and Qinxiang Cao},
    editor       =   {Benjamin C. Pierce},
    title        =   "Verifiable C",
    series       =   "Software Foundations",
    volume       =   "5",
    year         =   "2021",
    publisher    =   "Electronic textbook",
    note         =   {Version 1.1.1, \URL{http://softwarefoundations.cis.upenn.edu} },
    }
*)

(* ================================================================= *)
(** ** For Instructors and Contributors *)

(** If you plan to use these materials in your own course, you will
    undoubtedly find things you'd like to change, improve, or add.
    Your contributions are welcome!  Please see the [Preface]
    to _Logical Foundations_ for instructions. *)

(* ################################################################# *)
(** * Thanks *)

(** Development of the _Software Foundations_ series has been supported, in
    part, by the National Science Foundation under the NSF Expeditions grant
    1521523, _The Science of Deep Specification_. *)

(*** Check for the right version of VST *)
Require Import Coq.Strings.String.
Open Scope string.
Require Import VST.veric.version.  (* If this line fails, it means
  you don't have a VST installed. *)
Definition release_needed := "2.8".
Goal release = release_needed.
reflexivity ||
let need := constr:(release_needed) in let need := eval hnf in need in
let rel := constr:(release) in let rel := eval hnf in rel in
fail "The wrong version of VST is installed.
You have VST version"
rel "but this version of 'Software Foundations Volume 5: Verifiable C'"
"demands version" need ". If possible, install VST version" need
"using the Coq Platform or using opam.  Or, if not from Coq Platform or opam,"
"for instructions about building VST from source and accessing that version,
see the README file in this directory."
"Or, instead of installing VST" need ","
"if you want to proceed using VST version" rel ","
"then edit the Definition release_needed in Preface.v".
Abort.

Require Import ZArith.
Local Open Scope Z_scope.

Require VC.stack.  (* If this line fails, do 'make stack.vo' *)
Goal VC.stack.Info.bitsize = VST.veric.version.bitsize.
reflexivity ||
let b1 := constr:(VST.veric.version.bitsize) in let b1 := eval compute in b1 in
let b2 := constr:(VC.stack.Info.bitsize) in let b2 := eval compute in b2 in
fail "Your installed VST is configured to verify C programs compiled with"
  b1 "bit pointers,"
 "but the .c files in the local directory have been clightgen'ed as if compiled with"
 b2 "bit pointers."
"You can fix this by executing the shell command,
"
"bash cfiles-bitsize" b1 "
to install the properly configured clightgen outputs."
"It is not necessary to have clightgen installed".
Abort.

(* 2021-09-06 14:16 *)
