(** * Basic: Basic Proofs in Separation Logic *)

Set Implicit Arguments.
From SLF Require Import LibSepReference.
Import ProgramSyntax DemoPrograms.

Implicit Types n m : int.
Implicit Types p q : loc.

(* ################################################################# *)
(** * A First Taste *)

(** This chapter gives an overview of the basic features of Separation Logic,
    by means of examples. The examples are specified and verified using a
    Separation Logic framework whose construction is explained throughout the
    course. *)

(* ================================================================= *)
(** ** Parsing of Programs *)

(** The source code of the programs considered are written within Coq, using a
    "custom grammar" that allows writing code that reads almost like OCaml
    code. For example, consider the function [incr], which increments the
    contents of a mutable cell that stores an integer. In OCaml syntax, this
    function could be defined as:

OCaml:

  let incr =
    fun p ->
      let n = !p in
      let m = n + 1 in
      p := m
*)

(** In Coq, we describe the corresponding program as shown below. Observe that
    all variable names are prefixed with a quote symbol. This presentation
    avoids conflict between program variables and Coq constants. The function
    defined, named [incr], admits the type [val]. This type is defined by the
    framework. *)

Definition incr : val :=
  <{ fun 'p =>
      let 'n = ! 'p in
      let 'm = 'n + 1 in
      'p := 'm }>.

(** There is no need to learn how to write programs in this custom syntax:
    source code is provided for all the programs involved in this course. *)

(** To simplify the implementation of the framework and the reasoning about
    programs, we make throughout the course the simplifying assumption that
    programs are written in "A-normal form": all intermediate expressions must
    be named using a let-binding. *)

(* ================================================================= *)
(** ** Specification of the Increment Function *)

(** The specification of [incr p] is expressed using a "Separation Logic
    triple", that is, a predicate of the form [triple t H Q]. The term [t]
    here corresponds to the application of the function [incr] to the argument
    [p]. We could write this application in the form [<{ incr p }>], using
    the custom syntax for parsing programs. That said, we can also write the
    same term in the form [(incr p)], leveraging Coq's coercion facility to
    reuse Coq's syntax for application. In other words, the specification of
    [incr] can be written in the form [triple (incr p) H Q].

    The components [H] and [Q] correspond to the precondition and to the
    postcondition, which are explained next. To improve readability, we follow
    the convention of writing both the precondition and the postcondition on
    separate lines. *)

Lemma triple_incr : forall (p:loc) (n:int),
  triple <{ incr p }>
    (p ~~> n)
    (fun _ => (p ~~> (n+1))).

(** In the specification above, [p] denotes the "location", that is, the
    address in memory, of the reference cell provided as argument to the
    increment function. Locations have type [loc] in the framework.

    The precondition is written [p ~~> n]. This Separation Logic predicate
    describes a memory state in which the contents of the location [p] is the
    value [n]. In the present example, [n] stands for an integer value.

    The behavior of the operation [incr p] consists of updating the memory
    state by incrementing the contents of the cell at location [p], updating
    its contents to [n+1]. Thus, the memory state posterior to the increment
    operation is described by the predicate [p ~~> (n+1)].

    The result value returned by [incr p] is the unit value, which does not
    carry any useful information. In the specification of [incr], the
    postcondition is of the form [fun _ => ...] to indicate that there is
    no need to bind a name for the result value. *)

(** The general pattern of a specification thus includes:

    - Quantification of the arguments of the functions---here, the variable
      [p].
    - Quantification of the "ghost variables" used to describe the input
      state---here, the variable [n].
    - The application of the predicate [triple] to the function application
      [incr p]---here, the term being specified by the triple.
    - The precondition describing the input state---here, the predicate
      [p ~~> n].
    - The postcondition describing both the output value and the output state.
      The general pattern is [fun r => H'], where [r] names the result and
      [H'] describes the final state. Here, [r] is just an underscore symbol,
      and the final state is described by [p ~~> (n+1)]. *)

(** Note that we have to write [p ~~> (n+1)] using parentheses around [n+1],
    because [p ~~> n+1] would get parsed as [(p ~~> n) + 1]. *)

(* ================================================================= *)
(** ** Verification of the Increment Function *)

(** Our next step is to prove the specification lemma [triple_incr] which
    specifies the behavior of the function [incr]. We conduct the proof using
    tactics provided by the frameworks, called the "x-tactics" because their
    name start with the letter "x". These tactics include [xwp] for starting
    a proof, [xapp] for reasoning about a function call, and [xsimpl] for
    proving that a description of a state entails another one. *)

Proof.
(** [xwp] begins the verification proof. The proof obligation is displayed
    using a custom notation of the form [PRE H CODE F POST Q]. In the [CODE],
    one should be able to somewhat recognize the body of [incr]. Indeed,
    if we ignore the details and perform the alpha-renaming from [v] to [n]
    and [v0] to [m], the [CODE] section reads like:

              Let n := (App val_get p) in
              Let m := (App val_add n 1) in
              App val_set p m

    which is somewhat similar to the original source code. *)
    (* -- TODO: update the syntax above -- TODO: use custom entry for WP *)
  xwp.
(** The remainder of the proof performs essentially a symbolic execution of
    the code. At each step, one should not attempt to read the full proof
    obligation, but instead only look at the current state, described by the
    [PRE] part (here, [p ~~> n]), and at the first line only of the [CODE]
    part, which corresponds to the next operation to reason about. Each of
    the operations involved here is handled using the tactic [xapp]. *)

(** First, we reason about the operation [!p] that reads into [p]; this read
    operation returns the value [n]. *)
  xapp.
(** Second, we reason about the addition operation [n+1]. *)
  xapp.
(** Third, we reason about the update operation [p := n+1], thereby updating
    the state to [p ~~> (n+1)]. *)
  xapp.
(** At this stage, the proof obligation takes the form [H1 ==> H2]. It
    requires us to check that the final state matches what is claimed in the
    postcondition. We discharge it using the tactic [xsimpl]. *)
  xsimpl.
Qed.

(** This completes the verification of the lemma [triple_incr], which
    establishes a formal specification for the increment function. Before
    moving on to another function, we associate using the command shown below
    the lemma [triple_incr] with the function [incr] in a hint database called
    [triple]. Doing so, when we verify a function that features a call to
    [incr], the [xapp] tactic will be able to automatically invoke the lemma
    [triple_incr]. *)

Hint Resolve triple_incr : triple.

(** The reader may be curious to know what the notation [PRE H CODE F POST Q]
    stands for, and what the x-tactics are doing. Everything will be explaiend
    throughout the course. This chapter and the next one focus presenting the
    features of Separation Logic, and on showing how x-tactics can be used to
    verify programs in Separation Logic. *)

(* ================================================================= *)
(** ** A Function with a Return Value *)

(** As a second example, let us specify a function that performs simple
    arithmetic computations. The function, whose code appears below, expects
    an integer argument [n] (in [Z]). It evaluates [a] as [n+1], then
    evaluates [b] as  [n-1], and finally returns the sum [a+b]. The function
    thus always returns [2*n]. *)

Definition example_let : val :=
  <{ fun 'n =>
      let 'a = 'n + 1 in
      let 'b = 'n - 1 in
      'a + 'b }>.

(** The specification takes the form [triple (example_let n) H (fun r => H')],
    where [r], of type [val], denotes the output value.

    The precondition [H] describes what we need to assume about the input
    state. For this function, we need not assume anything, hence we write
    [\[]] to denote the empty precondition. The program might have allocated
    data prior to the call to the function [example_let], however this
    function will not interfer in any way with this previously-allocated data.

    The postcondition describes what the function produces. More precisely, it
    describes in general both the output that the function returns, and the
    data from memory that the function has allocated, accessed, or updated.
    The function [example_let] does not interact with the state, thus the
    postcondition could be described using the empty predicate [\[]].

    Yet, if we write just [fun (r:val) => \[]] as postcondition, we would have
    said nothing about the output value [r] produced by a call [example_let].
    Instead, we would like to specify that the result [r] is equal to [2*n].
    To that end, we write the postcondition [fun r => \[r = 2*n]]. Here,
    we use the predicate [\[P]], which allows to embed "pure facts", of type
    [Prop] in preconditions and postconditions.

    The equality [r = 2*n] actually resolves to [r = val_int (2*n)]], where
    [val_int] is a coercion that translates the integer value [2*n] into the
    corresponding integer value, of type [val], from the programming language.
    If you do not know what a coercion is, just ignore the previous sentence,
    and wait until chapter [Rules] to learn about coercions. *)

Lemma triple_example_let : forall (n:int),
  triple (example_let n)
    \[]
    (fun r => \[r = 2*n]).

(** The proof script is quite similar to the previous one: [xwp] begins the
    proof, [xapp] performs symbolic execution. and [xsimpl] simplifies the
    entailment. Ultimately, we need to check that the expression computed,
    [(n + 1) + (n - 1)], is equal to the specified result, that is, [2*n].
    To prove this equality, we invoke the tactic [math], which is a variant
    of the tactic [lia] provided by the TLC library. Recall from the preface
    that this course leverages TLC for enhanced definitions and tactics. *)

Proof using.
  xwp. xapp. xapp. xapp. xsimpl. math.
Qed.

(** From here on, we use the command [Proof using] for introducing a proof
    instead of writing just [Proof]. Doing so enables asynchronous proof
    checking, a feature that may enable faster processing of scripts. *)

(** **** Exercise: 1 star, standard, especially useful (triple_quadruple) *)

(** Consider the function [quadruple], which expects an integer [n] and
    returns its quadruple, that is, the value [4*n]. *)

Definition quadruple : val :=
  <{ fun 'n =>
       let 'm = 'n + 'n in
       'm + 'm }>.

(** Specify and verify the function [quadruple] to express that it returns
    [4*n]. Hint: follow the pattern of the previous proof. *)

(* FILL IN HERE *)

(** [] *)

(** **** Exercise: 2 stars, standard, especially useful (triple_inplace_double) *)

(** Consider the function [inplace_double], which expects a reference on an
    integer, reads its contents, then updates the contents with the double
    of the original value. *)

Definition inplace_double : val :=
  <{ fun 'p =>
       let 'n = !'p in
       let 'm = 'n + 'n in
       'p := 'm }>.

(** Specify and verify the function [inplace_double]. Hint: follow the
    pattern of the first example, namely [triple_incr]. *)

(* FILL IN HERE *)

(** [] *)

(* ################################################################# *)
(** * Separation Logic Operators *)

(* ================================================================= *)
(** ** Increment of Two References *)

(** Consider the following function, which expects the addresses
    of two reference cells, and increments both of them. *)

Definition incr_two : val :=
  <{ fun 'p 'q =>
       incr 'p;
       incr 'q }>.

(** The specification of this function takes the form
    [triple (incr_two p q) H (fun _ => H')], where the underscore symbol
    denotes the result value. We do not bother binding a name for that result
    value because it always consists of the unit value.

    The precondition describes two references cells: [p ~~> n] and [q ~~> m].
    To assert that the two cells are distinct from each other, we separate
    their description with the operator [\*]. Thus, the precondition
    is [(p ~~> n) \* (q ~~> m)], or simply [p ~~> n \* q ~~> m].
    The operator [\*] is called the "separating conjunction" of Separation
    Logic. It is also known as the "star" operator.

    The postcondition describes the final state in a similar way, as
    [p ~~> (n+1) \* q ~~> (m+1)]. This predicate reflects the fact that the
    contents of both references gets increased by one unit.

    The specification triple for [incr_two] is thus as follows. The proof
    follows the same pattern as in the previous examples. *)

Lemma triple_incr_two : forall (p q:loc) (n m:int),
  triple (incr_two p q)
    (p ~~> n \* q ~~> m)
    (fun _ => p ~~> (n+1) \* q ~~> (m+1)).
Proof using.
  xwp. xapp. xapp. xsimpl.
Qed.

(** Because we will make use of the function [incr_two] later in this chapter,
    we register the specification [triple_incr_two] in the [triple] database. *)

Hint Resolve triple_incr_two : triple.

(** A quick point of vocabulary before moving on: Separation Logic expressions
    such as [p ~~> n] or [\[]] or [H1 \* H2] are called "heap predicates",
    because they corresponding to predicates over "heaps", i.e., predicates
    over memory states. *)

(* ================================================================= *)
(** ** Aliased Arguments *)

(** The specification [triple_incr_two] stated above describes the behavior
    of calls to the function [incr_two] only for cases where the two arguments
    provided correspond to distinct reference cells. It says nothing, however,
    about a call of the form [incr_two p p]. Indeed, in Separation Logic,
    a state described by [p ~~> n] cannot be matched against a state described
    by [p ~~> n \* p ~~> n], because the star operator requires its operand to
    correspond to disjoint pieces of state.

    What happens if we nevertheless try to exploit [triple_incr_two] to reason
    about a call of the form [incr_two p p], that is, with aliased arguments?
    Let's find out, by considering the operation [aliased_call p], which does
    execute such a call. *)

Definition aliased_call : val :=
  <{ fun 'p =>
       incr_two 'p 'p }>.

(** A call to [aliased_call p] increases the contents of [p] by [2]. This
    property can be specified as follows. *)

Lemma triple_aliased_call : forall (p:loc) (n:int),
  triple (aliased_call p)
    (p ~~> n)
    (fun _ => p ~~> (n+2)).

(** If we attempt the proof, we get stuck. The tactic [xapp] reports its
    failure by issueing a proof obligation of the form
    [\[] ==> (p ~~> ?m) \* _]. This proof obligation requires us to show that,
    from the empty heap predicate state, one can extract a heap predicate
    [p ~~> ?m] describing a reference at location [p] with some integer
    contents [?m]. *)

Proof using.
  xwp. xapp.
Abort.

(** On the one hand, the precondition of the specification [triple_incr_two],
    with [q = p], requires providing [p ~~> ?n \* p ~~> ?m]. On the other
    hand, the current state is described as [p ~~> n]. When trying to match
    the two, the internal simplification tactic [xsimpl] is able to cancel out
    one occurence of [p ~~> n] from both expressions, but then there remains
    to match the empty heap predicate [\[]] against [(p ~~> ?m)]. The issue
    here is that the specification [triple_incr_two] is specialized for the
    case of "non-aliased" references. *)

(** One thing we can do is to state and prove an alternative specification for
    the function [incr_two], to cover the case of aliased arguments. The
    precondition of this alternative specification mentions a single reference,
    [p ~~> n], and the postcondition asserts that the contents of that
    reference gets increased by two units. This alternative specification is
    stated and proved as follows. *)

Lemma triple_incr_two_aliased : forall (p:loc) (n:int),
  triple (incr_two p p)
    (p ~~> n)
    (fun _ => p ~~> (n+2)).
Proof using.
  xwp. xapp. xapp. xsimpl. math.
Qed.

(** By exploiting the alternative specification for [incr_two], we are able
    to prove the specification of the function [aliased_call]. In order to
    indicate to the tactic [xapp] that it should not invoke the lemma
    [triple_incr_two] registered for [incr_two], but instead invoke the
    lemma [triple_incr_two_aliased], we provide that lemma as argument to
    [xapp]. Concretely, we write [xapp triple_incr_two_aliased]. *)

Lemma triple_aliased_call : forall (p:loc) (n:int),
  triple (aliased_call p)
    (p ~~> n)
    (fun _ => p ~~> (n+2)).
Proof using.
  xwp. xapp triple_incr_two_aliased. xsimpl.
Qed.

(** Taking a step back, it may appear somewhat disappointing that we need
    two different specifications for a same function, depending on whether
    its arguments are aliased on not. There exists advanced features of
    Separation Logic that allow handling the two cases through a single
    specification. However, for such a simple function it is easiest to just
    state and prove the two specifications separately. *)

(* ================================================================= *)
(** ** A Function that Takes Two References and Increments One *)

(** Consider the following function, which expects the addresses of two
    reference cells and increments only the first one. What is interesting
    about this function is precisely the fact that it does nothing with its
    second argument. *)

Definition incr_first : val :=
  <{ fun 'p 'q =>
       incr 'p }>.

(** We can specify this function by describing its input state as
    [p ~~> n \* q ~~> m], and describing its output state as
    [p ~~> (n+1) \* q ~~> m]. Formally: *)

Lemma triple_incr_first : forall (p q:loc) (n m:int),
  triple (incr_first p q)
    (p ~~> n \* q ~~> m)
    (fun _ => p ~~> (n+1) \* q ~~> m).
Proof using.
  xwp. xapp. xsimpl.
Qed.

(** The second reference plays absolutely no role in the execution of the
    function. Thus, we could equally well consider a specification that
    mentions only the existence of the first reference. *)

Lemma triple_incr_first' : forall (p q:loc) (n:int),
  triple (incr_first p q)
    (p ~~> n)
    (fun _ => p ~~> (n+1)).
Proof using.
  xwp. xapp. xsimpl.
Qed.

(** Interestingly, the specification [triple_incr_first], which mentions the
    two references, is derivable from the specification [triple_incr_first'],
    which mentions only the first reference. To prove the implication, it
    suffices to invoke the tactic [xapp] with argument [triple_incr_first']. *)

Lemma triple_incr_first_derived : forall (p q:loc) (n m:int),
  triple (incr_first p q)
    (p ~~> n \* q ~~> m)
    (fun _ => p ~~> (n+1) \* q ~~> m).
Proof using.
  intros. xapp triple_incr_first'. xsimpl.
Qed.

(** More generally, in Separation Logic, if a specification triple holds,
    then this triple remains valid when we add the same heap predicate to both
    the precondition and the postcondition. This is the "frame" principle, a
    key modularity feature that we'll come back to later on in the course. *)

(* ================================================================= *)
(** ** Transfer from one Reference to Another *)

(** Consider the [transfer] function, whose code appears below. *)

Definition transfer : val :=
  <{ fun 'p 'q =>
       let 'n = !'p in
       let 'm = !'q in
       let 's = 'n + 'm in
       'p := 's;
       'q := 0 }>.

(** **** Exercise: 1 star, standard, especially useful (triple_transfer)

    State and prove a lemma called [triple_transfer] specifying the
    behavior of [transfer p q] in the case where [p] and [q] denote
    two distinct references. *)

(* FILL IN HERE *)

(** [] *)

(** **** Exercise: 1 star, standard, especially useful (triple_transfer_aliased)

    State and prove a lemma called [triple_transfer_aliased] specifying
    the behavior of [transfer] when it is applied twice to the same
    argument. It should take the form [triple (transfer p p) H Q]. *)

(* FILL IN HERE *)

(** [] *)

(* ================================================================= *)
(** ** Specification of Allocation *)

(** Consider the operation [ref v], which allocates a memory cell with
    contents [v]. How can we specify this operation using a triple?

    The precondition of this triple should be the empty heap predicate,
    written [\[]], because the allocation can execute in an empty state.

    The postcondition should assert that the output value is a pointer
    [p], such that the final state is described by [p ~~> v].

    It would be tempting to write the postcondition [fun p => p ~~> v].
    Yet, the triple would be ill-typed, because the postcondition of a
    triple must be of type [val->hprop], and [p] is an address of type [loc].

    Instead, we need to write the postcondition in the form [fun (r:val) => H'],
    where [r] denotes the result value, and somehow we need to assert
    that [r] is a value of the form [val_loc p], for some location [p],
    where [val_loc] is the constructor that injects locations into the
    grammar of program values.

    To formally quantify the variable, we use an existential quantifier
    for heap predicates, written [\exists]. The correct postcondition for
    [ref v] is [fun (r:val) => \exists (p:loc), \[r = val_loc p] \* (p ~~> v)].

    The complete statement of the specification appears below. Note that the
    primitive operation [ref v] is written [ref v] in the Coq syntax. *)

(* TODO: explain the notation triple <{   vs triple (). *)
Parameter triple_ref : forall (v:val),
  triple <{ ref v }>
    \[]
    (fun r => \exists p, \[r = val_loc p] \* p ~~> v).

(** The pattern [fun r => \exists p, \[r = val_loc p] \* H)] occurs
    whenever a function returns a pointer. Thus, this pattern appears
    pervasively. To improve concision, we introduce a specific
    notation for this pattern, shortening it to [funloc p => H]. *)

Notation "'funloc' p '=>' H" :=
  (fun r => \exists p, \[r = val_loc p] \* H)
  (at level 200, p ident, format "'funloc'  p  '=>'  H").

(** Using this notation, the specification [triple_ref] can be reformulated
    more concisely, as follows. *)

Parameter triple_ref' : forall (v:val),
  triple <{ ref v }>
    \[]
    (funloc p => p ~~> v).

(** Remark: the CFML tool features a technique that generalizes the
    notation [funloc] to all return types, by leveraging type-classes.
    Unfortunately, the use of type-classes involves a number of
    technicalities that we wish to avoid in this course. For that
    reason, we employ only the [funloc] notation, and use existential
    quantifiers explicitly for other types. *)

(* ================================================================= *)
(** ** Allocation of a Reference with Greater Contents *)

(** Consider the following function, which takes as argument the
    address [p] of a memory cell with contents [n], allocates a
    fresh memory cell with contents [n+1], then returns the address
    of that fresh cell. *)

Definition ref_greater : val :=
  <{ fun 'p =>
       let 'n = !'p in
       let 'm = 'n + 1 in
       ref 'm }>.

(** The precondition of [ref_greater] needs to assert the existence of a cell
    [p ~~> n]. The postcondition of [ref_greater] should asserts the existence
    of two cells, [p ~~> n] and [q ~~> (n+1)], where [q] denotes the
    location returned by the function. The postcondition is thus written
    [funloc q => p ~~> n \* q ~~> (n+1)], which is a shorthand for
    [fun (r:val) => \exists q, \[r = val_loc q] \* p ~~> n \* q ~~> (n+1)].

    The complete specification of [ref_greater] is: *)

Lemma triple_ref_greater : forall (p:loc) (n:int),
  triple (ref_greater p)
    (p ~~> n)
    (funloc q => p ~~> n \* q ~~> (n+1)).
Proof using.
  xwp. xapp. xapp. xapp. intros q. xsimpl. auto.
Qed.

(** [] *)

(** **** Exercise: 2 stars, standard, especially useful (triple_ref_greater_abstract)

    State another specification for the function [ref_greater],
    called [triple_ref_greater_abstract], with a postcondition that
    does not reveal the contents of the fresh reference [q], but
    instead only asserts that it is greater than the contents
    of [p]. To that end, introduce in the postcondition an existentially
    quantified variable called [m], with [m > n].

    Then, derive the new specification from the former one, following
    the proof pattern employed in the proof of [triple_incr_first_derived]. *)

(* FILL IN HERE *)

(** [] *)

(* ================================================================= *)
(** ** Deallocation in Separation Logic *)

(** Separation Logic tracks allocated data. In its simplest form,
    Separation Logic enforces that all allocated data is eventually
    deallocated. Technically, the logic is said to "linear" as opposed
    to "affine". *)

(** Let us illustrate what happens if we forget to deallocate a reference.

    Consider the following program, which computes
    the successor of a integer [n] by storing it into a reference cell,
    then incrementing that reference, and finally returning its contents. *)

Definition succ_using_incr_attempt :=
  <{ fun 'n =>
       let 'p = ref 'n in
       incr 'p;
       ! 'p }>.

(** The operation [succ_using_incr_attempt n] admits an empty
    precondition, and a postcondition asserting that the final
    result is [n+1]. Yet, if we try to prove this specification,
    we get stuck. *)

Lemma triple_succ_using_incr_attempt : forall (n:int),
  triple (succ_using_incr_attempt n)
    \[]
    (fun r => \[r = n+1]).
Proof using.
  xwp. xapp. intros p. xapp. xapp. xsimpl. { auto. }
Abort.

(** In the above proof script, we get stuck with the entailment
    [p ~~> (n+1) ==> \[]], which indicates that the current state contains
    a reference, whereas the postcondition describes an empty state. *)

(** We could attempt to patch the specification to account for the left-over
    reference. This yields a provable specification. *)

Lemma triple_succ_using_incr_attempt' : forall (n:int),
  triple (succ_using_incr_attempt n)
    \[]
    (fun r => \[r = n+1] \* \exists p, (p ~~> (n+1))).
Proof using.
  xwp. xapp. intros p. xapp. xapp. xsimpl. { auto. }
Qed.

(** However, while the above specification is provable, it is not
    especially useful, since the piece of postcondition
    [\exists p, p ~~> (n+1)] is of absolutely no use to the caller
    of the function. Worse, the caller will have its _own_ state polluted with
    [\exists p, p ~~> (n+1)] and will have no way to get rid of it apart
    from incorporating it into its own postcondition. *)

(** The right solution is to alter the code to free the reference once
    it is no longer needed, as shown below. We assume the source language
    includes a deallocation operation written [free p]. (This operation
    does not exist in OCaml, but let us nevertheless continue using OCaml
    syntax for writing programs.) *)

Definition succ_using_incr :=
  <{ fun 'n =>
       let 'p = ref 'n in
       incr 'p;
       let 'x = ! 'p in
       free 'p;
       'x }>.

(** This program may now be proved correct with respect to the intended
    specification. Observe in particular the last call to [xapp] below,
    which corresponds to the [free] operation.

    The final result is the value of the variable [x]. To reason about it,
    we exploit the tactic [xval], as illustrated below. *)

Lemma triple_succ_using_incr : forall n,
  triple (succ_using_incr n)
    \[]
    (fun r => \[r = n+1]).
Proof using.
  xwp. xapp. intros p. xapp. xapp. xapp. xval. xsimpl. auto.
Qed.

(** Remark: if we verify programs written in a language equipped with
    a garbage collector (like, e.g., OCaml), we need to tweak the
    Separation Logic to account for the fact that some heap predicates
    can be freely discarded from postconditions. This variant of
    Separation Logic will be described in the chapter [Affine]. *)

(* ================================================================= *)
(** ** Combined Reading and Freeing of a Reference *)

(** The function [get_and_free] takes as argument the address [p] of a
    reference cell. It reads the contents of that cell, frees the cell,
    and returns its contents. *)

Definition get_and_free : val :=
  <{ fun 'p =>
      let 'v = ! 'p in
      free 'p;
      'v }>.

(** **** Exercise: 2 stars, standard, especially useful (triple_get_and_free)

    Prove the correctness of the function [get_and_free]. *)

Lemma triple_get_and_free : forall p v,
  triple (get_and_free p)
    (p ~~> v)
    (fun r => \[r = v]).
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

Hint Resolve triple_get_and_free : triple.

(* ################################################################# *)
(** * Recursive Functions *)

(* ================================================================= *)
(** ** Axiomatization of the Mathematical Factorial Function *)

(** Our next example consists of a program that evaluates the factorial
    function. To specify this function, we consider a Coq axiomatization
    of the mathematical factorial function, named [facto]. *)

Module Import Facto.

Parameter facto : int -> int.

Parameter facto_init : forall n,
  0 <= n <= 1 ->
  facto n = 1.

Parameter facto_step : forall n,
  n > 1 ->
  facto n = n * (facto (n-1)).

End Facto.

(** Note that we have purposely not specified the value of [facto] on
    negative arguments. *)

(* ================================================================= *)
(** ** A Partial Recursive Function, Without State *)

(** In the rest of the chapter, we consider recursive functions that
     manipulate the state. To gently introduce the necessary techniques
    for reasoning about recursive functions, we first consider a recursive
    function that does not involve any mutable state.

    The function [factorec] computes the factorial of its argument.

OCaml:

    let rec factorec n =
      if n <= 1 then 1 else n * factorec (n-1)

    The corresonding code in A-normal form is slightly more verbose. *)

Definition factorec : val :=
  <{ fix 'f 'n =>
       let 'b = 'n <= 1 in
       if 'b
         then 1
         else let 'x = 'n - 1 in
              let 'y = 'f 'x in
              'n * 'y }>.

(** A call [factorec n] can be specified as follows:

    - the initial state is empty,
    - the final state is empty,
    - the result value [r] is such that [r = facto n], when [n >= 0].

    In case the argument is negative (i.e., [n < 0]), we have two choices:

    - either we explicitly specify that the result is [1] in this case,
    - or we rule out this possibility by requiring [n >= 0].

    Let us follow the second approach, in order to illustrate the
    specification of partial functions.

    There are two possibilities for expressing the constraint [n >= 0]:

    - either we use as precondition [\[n >= 0]],
    - or we place an assumption [(n >= 0) -> _] to the front of the triple,
      and use an empty precondition, that is, [\[]].

    The two presentations are totally equivalent. By convention, we follow
    the second presentation, which tends to improve both the readability of
    specifications and the conciseness of proof scripts.

    The specification of [factorec] is thus stated as follows. *)

Lemma triple_factorec : forall n,
  n >= 0 ->
  triple (factorec n)
    \[]
    (fun r => \[r = facto n]).

(** Let's walk through the proof script in detail, to see in particular
    how to set up the induction, how to reason about the recursive call,
    and how to deal with the precondition [n >= 0]. *)

Proof using. unfold factorec.
(** We set up a proof by induction on [n] to obtain an induction
    hypothesis for the recursive calls. Recursive calls are made
    each time on smaller values, and the last recursive call is
    made on [n = 1]. The well-founded relation [downto 1] captures
    this recursion pattern. The tactic [induction_wf] is provided
    by the TLC library to assist in setting up well-founded inductions.
    It is exploited as follows. *)
  intros n. induction_wf IH: (downto 1) n.
(** Observe the induction hypothesis [IH]. By unfolding [downto]
    as done in the next step, this hypothesis asserts that the
    specification that we are trying to prove already holds for
    arguments that are smaller than the current argument [n],
    and that are greater than or equal to [1]. *)
  unfold downto in IH.
(** We may then begin the interactive verification proof. *)
  intros Hn. xwp.
(** We reason about the evaluation of the boolean condition [n <= 1]. *)
  xapp.
(** The result of the evaluation of [n <= 1] in the source program
    is described by the boolean value [isTrue (n <= 1)], which appears
    in the [CODE] section after [Ifval]. The operation [isTrue] is
    provided by the TLC library as a conversion function from [Prop]
    to [bool]. The use of such a conversion function (which leverages
    classical logic) greatly simplifies the process of automatically
    performing substitutions after calls to [xapp].

    We next perform the case analysis on the test [n <= 1]. *)
  xif.
(** Doing so gives two cases. *)

(** In the "then" branch, we can assume [n <= 1]. *)
  { intros C.
(** Here, the return value is [1]. *)
    xval. xsimpl.
(** We check that [1 = facto n] when [n <= 1]. *)
    rewrite facto_init; math. }
(** In the "else" branch, we can assume [n > 1]. *)
  { intros C.
(** We reason about the evaluation of [n-1] *)
    xapp.
(** We reason about the recursive call, implicitly exploiting
    the induction hypothesis [IH] with [n-1]. *)
    xapp.
(** We justify that the recursive call is indeed made on a smaller
    argument than the current one, that is, [n]. *)
    { math. }
(** We justify that the recursive call is made to a nonnegative argument,
    as required by the specification. *)
    { math. }
(** We reason about the multiplication [n * facto(n-1)]. *)
    xapp.
(** We check that [n * facto (n-1)] matches [facto n]. *)
    xsimpl. rewrite (@facto_step n); math. }
Qed.

(* ================================================================= *)
(** ** A Recursive Function with State *)

(** The example of [factorec] was a warmup. Let's now tackle a recursive
    function involving mutable state.

    The function [repeat_incr p m] makes [m] times a call to [incr p].
    Here, [m] is assumed to be a nonnegative value.

OCaml:

    let rec repeat_incr p m =
      if m > 0 then (
        incr p;
        repeat_incr p (m - 1)
      )

    In the concrete syntax for programs, conditionals without an 'else'
    branch are written [if t1 then t2 end]. The keyword [end] avoids
    ambiguities in cases where this construct is followed by a semi-column. *)

Definition repeat_incr : val :=
  <{ fix 'f 'p 'm =>
       let 'b = 'm > 0 in
       if 'b then
         incr 'p;
         let 'x = 'm - 1 in
         'f 'p 'x
       end }>.

(** The specification for [repeat_incr p] requires that the initial
    state contains a reference [p] with some integer contents [n],
    that is, [p ~~> n]. Its postcondition asserts that the resulting
    state is [p ~~> (n+m)], which is the result after incrementing
    [m] times the reference [p]. Observe that this postcondition is
    only valid under the assumption that [m >= 0]. *)

Lemma triple_repeat_incr : forall (m n:int) (p:loc),
  m >= 0 ->
  triple (repeat_incr p m)
    (p ~~> n)
    (fun _ => p ~~> (n + m)).

(** **** Exercise: 2 stars, standard, especially useful (triple_repeat_incr)

    Prove the specification of the function [repeat_incr].
    Hint: the structure of the proof resembles that of [triple_factorec']. *)

Proof using. unfold repeat_incr. (* FILL IN HERE *) Admitted.

(** [] *)

(** In the previous examples of recursive functions, the induction
    was always performed on the first argument quantified in the
    specification. When the decreasing argument is not the first one,
    additional manipulations are required for re-generalizing into
    the goal the variables that may change during the course of the
    induction. Here is an example illustrating how to deal with such
    a situation. *)

Lemma triple_repeat_incr' : forall (p:loc) (n m:int),
  m >= 0 ->
  triple (repeat_incr p m)
    (p ~~> n)
    (fun _ => p ~~> (n + m)).
Proof using.
  (* First, introduces all variables and hypotheses. *)
  intros n m Hm.
  (* Next, generalize those that are not constant during the recursion. *)
  gen n Hm.
  (* Then, set up the induction. *)
  induction_wf IH: (downto 0) m. unfold downto in IH.
  (* Finally, re-introduce the generalized hypotheses. *)
  intros.
Abort.

(* ================================================================= *)
(** ** Trying to Prove Incorrect Specifications *)

(** We established for [repeat_incr p n] a specification with the
    constraint [m >= 0]. What if we did omit it? Where would we get
    stuck in the proof?

    Clearly, something should break, because when [m < 0], the call
    [repeat_incr p m] terminates immediately. Thus, when [m < 0] the
    final state is like the initial state [p ~~> n], and not equal to
    [p ~~> (n + m)]. Let us investigate how the proof breaks. *)

Lemma triple_repeat_incr_incorrect : forall (p:loc) (n m:int),
  triple (repeat_incr p m)
    (p ~~> n)
    (fun _ => p ~~> (n + m)).
Proof using.
  intros. revert n. induction_wf IH: (downto 0) m. unfold downto in IH.
  intros. xwp. xapp. xif; intros C.
  { (* In the 'then' branch: [m > 0] *)
    xapp. xapp. xapp. { math. } xsimpl. math. }
  { (* In the 'else' branch: [m <= 0] *)
    xval.
(** At this point, we are requested to justify that the current state
    [p ~~> n] matches the postcondition [p ~~> (n + m)], which
    amounts to proving [n = n + m]. *)
    xsimpl.
Abort.

(** When the specification features the assumption [m >= 0],
    we can prove this equality because the fact that we are
    in the else branch means that [m <= 0], thus [m = 0].
    However, without the assumption [m >= 0], the value of
    [m] could very well be negative. *)

(** Note that there exists a valid specification for [repeat_incr]
    that does not constrain [m] but instead specifies that the state
    always evolves from [p ~~> n] to [p ~~> (n + max 0 m)].

    The corresponding proof scripts exploits two properties of the
    [max] function. *)

Lemma max_l : forall n m,
  n >= m ->
  max n m = n.
Proof using. introv M. unfold max. case_if; math. Qed.

Lemma max_r : forall n m,
  n <= m ->
  max n m = m.
Proof using. introv M. unfold max. case_if; math. Qed.

(** Here is the most general specification for the function
    [repeat_incr]. *)

Lemma triple_repeat_incr' : forall (p:loc) (n m:int),
  triple (repeat_incr p m)
    (p ~~> n)
    (fun _ => p ~~> (n + max 0 m)).
Proof using.
  intros. gen n. induction_wf IH: (downto 0) m.
  xwp. xapp. xif; intros C.
  { xapp. xapp. xapp. { math. }
    xsimpl. repeat rewrite max_r; math. }
  { xval. xsimpl. rewrite max_l; math. }
Qed.

(* ================================================================= *)
(** ** A Recursive Function Involving two References *)

(** Consider the function [step_transfer p q], which repeatedly increments
    a reference [p] and decrements a reference [q], until [q] reaches zero.

OCaml:

    let rec step_transfer p q =
      if !q > 0 then (
        incr p;
        decr q;
        step_transfer p q
      )
*)

Definition step_transfer :=
  <{ fix 'f 'p 'q =>
       let 'm = !'q in
       let 'b = 'm > 0 in
       if 'b then
         incr 'p;
         decr 'q;
         'f 'p 'q
       end }>.

(** The specification of [step_transfer] is essentially the same as
    that of the function [transfer] presented previously, the
    only difference being that we here assume the contents of [q] to be
    nonnegative. *)

Lemma triple_step_transfer : forall p q n m,
  m >= 0 ->
  triple (step_transfer p q)
    (p ~~> n \* q ~~> m)
    (fun _ => p ~~> (n + m) \* q ~~> 0).

(** **** Exercise: 2 stars, standard, especially useful (triple_step_transfer)

    Verify the function [step_transfer].
    Hint: to set up the induction, follow the pattern shown in
    the proof of [triple_repeat_incr']. *)

Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(* ################################################################# *)
(** * Summary *)

(** This chapter introduces the following notions:

    - "Heap predicates", which are used to describe memory states in
      Separation Logic.
    - "Specification triples", of the form [triple t H Q], which
      relate a term [t], a precondition [H], and a postcondition [Q].
    - "Entailment proof obligations", of the form [H ==> H'] or
      [Q ===> Q'], which assert that a pre- or post-condition is weaker
      than another one.
    - "Verification proof obligations", of the form [PRE H CODE F POST Q],
      which internally leverage a form of weakest-precondition.
    - Custom proof tactics, called "x-tactics", which are specialized
      tactics for carrying out the verification proofs.

    The "heap predicates" used to describe memory states are presented
    throughout the chapter. They include:
    - [p ~~> n], which describes a memory cell at location [p] with
      contents [n],
    - [\[]], which describes an empty state,
    - [\[P]], which also describes an empty state, and moreover
      asserts that the proposition [P] is true,
    - [H1 \* H2], which describes a state made of two disjoint parts:
      [H1] and [H2],
    - [\exists x, H], which is used to quantify variables in
      postconditions.

    All these heap predicates admit the type [hprop], which describes
    predicates over memory states. Technically, [hprop] is defined as
    [state->Prop].

    The verification of practical programs is carried out using
    x-tactics, identified by the leading "x" letter in their
    name. These tactics include:
    - [xwp] to begin a proof, or [xapp] to invoke an existing specification,
    - [xapp] to reason about an application,
    - [xval] to reason about a return value,
    - [xif] to reason about a conditional,
    - [xsimpl] to simplify or prove entailments ([H ==> H'] or
      [Q ===> Q']).

    In addition to x-tactics, the proof scripts exploit standard Coq
    tactics, as well as tactics from the TLC library.
    SOONER: Recall what the TLC library is.
    The relevant TLC
    tactics, which are described when first use, include:
    - [math], which is a variant of [lia] for proving mathematical
      goals,
    - [induction_wf], which sets up proofs by well-founded induction,
    - [gen], which is a shorthand for [generalize dependent], a tactic
      also useful to set up induction principles.
*)

(* ################################################################# *)
(** * Historical Notes *)

(** The key ideas of Separation Logic were devised by John Reynolds, inspired
    in part by older work by [Burstall 1972] (in Bib.v). Reynolds presented his ideas
    in lectures given in the fall of 1999. The proposed rules turned out to be
    unsound, but [Ishtiaq and O'Hearn 2001] (in Bib.v) noticed a strong relationship
    with the logic of bunched implications by [O'Hearn and Pym 1999] (in Bib.v),
    leading to ideas on how to set up a sound program logic. Soon afterwards,
    the seminal publications on Separation Logic appeared at the CSL workshop
    [O'Hearn, Reynolds, and Yang 2001] (in Bib.v) and at the LICS conference
    [Reynolds 2002] (in Bib.v).

    The Separation Logic specifications and proof scripts using x-tactics
    presented in this file are directly adapted from the CFML tool (2010-2020),
    which is developed mainly by Arthur Charguéraud. The notations for
    Separation Logic predicates are directly inspired from those introduced in
    the Ynot project (2006-2008). See chapter [Postface] for references. *)

(* 2021-05-18 18:14 *)
