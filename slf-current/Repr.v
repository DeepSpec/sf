(** * Repr: Representation Predicates *)

Set Implicit Arguments.
From SLF Require Import LibSepReference.
Import ProgramSyntax DemoPrograms.
From SLF Require Import Basic.
Open Scope liblist_scope.

Implicit Types n m : int.
Implicit Types p q s c : loc.
Implicit Types x : val.

(* ################################################################# *)
(** * First Pass *)

(** A representation predicate is a heap predicate that describes a mutable data
    structure. For example, the heap predicate [MList L p] describes a mutable
    linked list whose head cell is at location [p], and whose elements are
    described by the Coq list [L]. In this chapter, we'll see how to define
    [MList], and to use this predicate for specifying and verifying functions
    that operate on mutable linked lists. We will also study representation
    predicates for mutable trees, as well as for counter functions, which
    feature an internal state.

    As explained in the [Preface], this chapter, like all the following
    ones, is decomposed in three parts:

    - The _First Pass_ section presents the most important ideas only.
    - The _More Details_ section presents additional material explaining
      in more depth the meaning and the consequences of the key results.
      By default, readers would eventually read all this material.
    - The _Optional Material_ section contains more advanced material,
      for readers who can afford to invest more time in the topic. *)

(* ================================================================= *)
(** ** Formalization of the List Representation Predicate *)

(** The implementation of mutable lists and trees involves the use of records.
    For simplicity, field names are represented as natural numbers. For example,
    to represent a list cell with a head and a tail field, we define [head] as
    the constant zero, and [tail] as the constant one. *)

Definition head : field := 0%nat.
Definition tail : field := 1%nat.

(** The heap predicate [p ~~~>`{ head := x; tail := q }] describes a record
    allocated at location [p], with a head field storing [x] and a tail field
    storing [q]. The arrow [~~~>] is provided by the framework for describing
    records. The notation [`{...}] is a handy notation for a list of pairs of
    field names and values of arbitrary types. (Further details on the
    formalization of records are presented in chapter [Struct].)

    A mutable list consists of a chain of cells. Each cell stores a tail pointer
    that gives the location of the next cell in the chain. The last cell stores
    the [null] value in its tail field.

    The heap predicate [MList L p] describes a list whose head cell is at
    location [p], and whose elements are described by the list [L]. This
    predicate is defined recursively on the structure of [L]:

    - if [L] is empty, then [p] is the null pointer,
    - if [L] is of the form [x::L'], then [p] is not null, and the
      head field of [p] contains [x], and the tail field of [p]
      contains a pointer [q] such that [MList L' q] describes the
      tail of the list.

    This definition is formalized as follows. *)

Fixpoint MList (L:list val) (p:loc) : hprop :=
  match L with
  | nil => \[p = null]
  | x::L' => \exists q, (p ~~~> `{ head := x; tail := q}) \* (MList L' q)
  end.

(* ================================================================= *)
(** ** Alternative Characterizations of [MList] *)

(** Carrying out proofs directly with [MList] can be slightly cumbersome, mainly
    due to Coq's limited support for folding back definitions. We find it more
    practical to explicitly state equalities that paraphrase the definition of
    [MList]. There is one equality for the [nil] case, and one for the [cons]
    case. *)

Lemma MList_nil : forall p,
  (MList nil p) = \[p = null].
Proof using. auto. Qed.

Lemma MList_cons : forall p x L',
  MList (x::L') p =
  \exists q, (p ~~~> `{ head := x; tail := q}) \* (MList L' q).
Proof using. auto. Qed.

(** In addition, it is also very useful in proofs to reformulate the definition
    of [MList L p] in the form of a case analysis on whether the pointer [p] is
    null or not. This corresponds to the programming pattern
    [if p == null then ... else]. This alternative characterization of
    [MList L p] asserts that:

    - if [p] is null, then [L] is empty,
    - otherwise, [L] decomposes as [x::L'], the head field of [p] contains [x],
      and the tail field of [p] contains a pointer [q] such that [MList L' q]
      describes the tail of the list.

    The corresponding lemma, shown below, is stated using the
    [If P then X else Y] construction, which generalizes Coq's construction
    [if b then X else Y] to discriminate over a proposition [P] as opposed to a
    boolean value [b]. The [If] construct leverages (strong) classical logic. It
    is provided by the TLC library, just like the tactic [case_if] which is
    convenient for performing the case analysis on whether [P] is true or false.
    *)
Lemma MList_if : forall (p:loc) (L:list val),
      (MList L p)
  ==> (If p = null
        then \[L = nil]
        else \exists x q L', \[L = x::L']
             \* (p ~~~> `{ head := x; tail := q}) \* (MList L' q)).
(** The proof is a bit technical, it may be skipped for a first reading. *)
Proof using.
(** Let's prove this result by case analysis on [L]. *)
  intros. destruct L as [|x L'].
(** Case [L = nil]. By definition of [MList], we have [p = null]. *)
  { xchange MList_nil. intros M.
(** We have to justify [L = nil], which is trivial. The TLC [case_if] tactic
    performs a case analysis on the argument of the first visible [if]. *)
    case_if. xsimpl. auto. }
(** Case [L = x::L'].

    One possibility is to perform a rewrite operation using [MList_cons] on its
    first occurrence. Then using CFML the tactic [xpull] to extract the
    existential quantifiers out from the precondition:
    [rewrite MList_cons. xpull. intros q.]
    A more efficient approach is to use the dedicated CFML tactic [xchange],
    which is specialized for performing updates in the current state. *)
    { xchange MList_cons. intros q.
(** Because a record is allocated at location [p], the pointer [p] cannot be
    null. The lemma [hrecord_not_null] allows us to exploit this property,
    extracting the hypothesis [p <> null]. We use again the tactic [case_if] to
    simplify the case analysis. *)
    xchange hrecord_not_null. intros N. case_if.
(** To conclude, it suffices to correctly instantiate the existential
    quantifiers. The tactic [xsimpl] is able to guess the appropriate
    instantiations. *)
     xsimpl. auto. }
Qed.

(** Note that the reciprocal entailment to the one stated in [MList_if] is also
    true, but we do not need it so we do not bother proving it here. In the rest
    of the course, we will never unfold the definition [MList], but only work
    using [MList_nil], [MList_cons], and [MList_if]. So, we can make [MList]
    opaque, thereby avoiding undesired simplifications. *)

Global Opaque MList.

(* ================================================================= *)
(** ** In-place Concatenation of Two Mutable Lists *)

(** The function [append] expects two arguments: a pointer [p1] on a nonempty
    list, and a pointer [p2] on another list (possibly empty). The function
    updates the last cell from the first list in such a way that its tail points
    to the head cell of [p2]. After this operation, the pointer [p1] points to a
    list that corresponds to the concatenation of the two input lists.

OCaml:

    let rec append p1 p2 =
      if p1.tail == null
        then p1.tail <- p2
        else append p1.tail p2
*)

Definition append : val :=
  <{ fix 'f 'p1 'p2 =>
       let 'q1 = 'p1`.tail in
       let 'b = ('q1 = null) in
       if 'b
         then 'p1`.tail := 'p2
         else 'f 'q1 'p2 }>.

(** The append function is specified and verified as shown below. The proof
    pattern is representative of that of many list-manipulating functions, so it
    is essential that the reader follow through every step of this proof. *)

Lemma triple_append : forall (L1 L2:list val) (p1 p2:loc),
  p1 <> null ->
  triple (append p1 p2)
    (MList L1 p1 \* MList L2 p2)
    (fun _ => MList (L1++L2) p1).
Proof using.
(** The induction principle provides an hypothesis for the tail of [L1], i.e.,
    for the list [L1'], such that the relation [list_sub L1' L1] holds. *)
  introv K. gen p1. induction_wf IH: list_sub L1. introv N. xwp.
(** To begin the proof, we reveal the head cell of [p1]. We let [q1] denote the
    tail of [p1], and [L1'] the tail of [L1]. *)
  xchange (MList_if p1). case_if. xpull. intros x q1 L1' ->.
(** We then reason about the case analysis. *)
  xapp. xapp. xif; intros Cq1.
(** If [q1'] is null, then [L1'] is empty. *)
  { xchange (MList_if q1). case_if. xpull. intros ->.
(** In this case, we set the pointer, then we fold back the head cell. *)
    xapp. xchange <- MList_cons. }
(** Otherwise, if [q1'] is not null, we reason about the recursive call using
    the induction hypothesis, then we fold back the head cell. *)
  { xapp. xchange <- MList_cons. }
Qed.

(* ================================================================= *)
(** ** Smart Constructors for Linked Lists *)

(** We next introduce two smart constructors for linked lists, called [mnil] and
    [mcons]. The operation [mnil()] creates an empty list. Its implementation
    simply returns the value [null]. Its specification asserts that the return
    value is a pointer [p] such that [MList nil p] holds. *)

Definition mnil : val :=
  <{ fun 'u =>
       null }>.

Lemma triple_mnil :
  triple (mnil ())
    \[]
    (funloc p => MList nil p).
(** The proof uses the tactic [xchanges*], which is a shorthand for [xchange]
    followed with [xsimpl*]. *)
Proof using. xwp. xval. xchanges* <- (MList_nil null). Qed.

Hint Resolve triple_mnil : triple.

(** Observe that the specification [triple_mnil] does not mention the [null]
    pointer anywhere. This specification may thus be used to specify the
    behavior of operations on mutable lists without having to reveal low-level
    implementation details that involve the [null] pointer. *)

(** The operation [mcons x q] creates a fresh list cell, with [x] in the head
    field and [q] in the tail field. Its implementation allocates and
    initializes a fresh record made of two fields. The allocation operation
    leverages the allocation construct written [`{ head := 'x; tail := 'q }] in
    the code. This construct is in fact a notation for an operation called
    [val_new_hrecord_2], which we here view as a primitive operation. *)

Definition mcons : val :=
  <{ fun 'x 'q =>
       `{ head := 'x; tail := 'q } }>.

(** The operation [mcons] admits two specifications. The first one describes
    only the production of a heap predicate for the freshly allocated record. *)

Lemma triple_mcons : forall x q,
  triple (mcons x q)
    \[]
    (funloc p => p ~~~> `{ head := x ; tail := q }).
Proof using. xwp. xapp triple_new_hrecord_2; auto. xsimpl*. Qed.

(** The second specification assumes that the argument [q] comes with a list
    representation of the form [Mlist q L], and it specifies that the function
    [mcons] produces the representation predicate [Mlist p (x::L)]. This second
    specification is derivable from the first one, by folding the representation
    predicate [MList] using the tactic [xchange]. *)

Lemma triple_mcons' : forall L x q,
  triple (mcons x q)
    (MList L q)
    (funloc p => MList (x::L) p).
Proof using.
  intros. xapp triple_mcons.
  intros p. xchange <- MList_cons. xsimpl*.
Qed.

(** In practice, this second specification is more often useful than the first
    one, hence we register it in the database for [xapp]. It remains possible to
    invoke [xapp triple_mcons] for exploiting the first specification, where
    needed. *)

Hint Resolve triple_mcons' : triple.

(* ================================================================= *)
(** ** Copy Function for Lists *)

(** The function [mcopy] takes a mutable linked list and builds an independent
    copy of it, with help of the functions [mnil] and [mcons].

OCaml:

    let rec mcopy p =
      if p == null
        then mnil ()
        else mcons (p.head) (mcopy p.tail)
*)

Definition mcopy : val :=
  <{ fix 'f 'p =>
       let 'b = ('p = null) in
       if 'b
         then mnil ()
         else
           let 'x = 'p`.head in
           let 'q = 'p`.tail in
           let 'q2 = ('f 'q) in
           mcons 'x 'q2 }>.

(** The precondition of [mcopy] requires a linked list described as [MList L p].
    The postcondition asserts that the function returns a pointer [p'] and a
    list described as [MList L p'], in addition to the original list [MList L p]
    . The two lists are totally disjoint and independent, as captured by the
    separating conjunction symbol (the star). *)

Lemma triple_mcopy : forall L p,
  triple (mcopy p)
    (MList L p)
    (funloc p' => (MList L p) \* (MList L p')).
(** The proof is structure is like the previous ones. While playing the script,
    try to spot the places where:

    - [mnil] produces an empty list of the form [MList nil p'],
    - the recursive call produces a list of the form [MList L' q'],
    - [mcons] produces a list of the form [MList (x::L') p'].

*)

Proof using.
  intros. gen p. induction_wf IH: list_sub L.
  xwp. xapp. xchange MList_if. xif; intros C; case_if; xpull.
  { intros ->. xapp. xsimpl*. subst. xchange* <- MList_nil. }
  { intros x q L' ->. xapp. xapp. xapp. intros q'.
    xapp. intros p'. xchange <- MList_cons. xsimpl*. }
Qed.

(* ================================================================= *)
(** ** Length Function for Lists *)

(** The function [mlength] computes the length of a mutable linked list.

OCaml:

    let rec mlength p =
      if p == null
        then 0
        else 1 + mlength p.tail
*)

Definition mlength : val :=
  <{ fix 'f 'p =>
       let 'b = ('p = null) in
       if 'b
         then 0
         else (let 'q = 'p`.tail in
               let 'n = 'f 'q in
               'n + 1) }>.

(** **** Exercise: 3 stars, standard, especially useful (triple_mlength)

    Prove the correctness of the function [mlength]. *)

Lemma triple_mlength : forall L p,
  triple (mlength p)
    (MList L p)
    (fun r => \[r = val_int (length L)] \* (MList L p)).
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(* ================================================================= *)
(** ** Alternative Length Function for Lists *)

(** In this section, we consider an alternative implementation of [mlength] that
    uses an auxiliary reference cell, called [c], to keep track of the number of
    cells traversed so far. The list is traversed recursively, incrementing the
    contents of the reference once for every cell.

OCaml:

    let rec listacc c p =
      if p == null
        then ()
        else (incr c; listacc c p.tail)

    let mlength' p =
      let c = ref 0 in
      listacc c p;
      !c
*)

Definition acclength : val :=
  <{ fix 'f 'c 'p =>
       let 'b = ('p <> null) in
       if 'b then
         incr 'c;
         let 'q = 'p`.tail in
         'f 'c 'q
       end }>.

Definition mlength' : val :=
  <{ fun 'p =>
       let 'c = ref 0 in
       acclength 'c 'p;
       get_and_free 'c }>.

(** **** Exercise: 3 stars, standard, especially useful (triple_mlength')

    Prove the correctness of the function [mlength']. Hint: start by stating a
    lemma [triple_acclength] expressing the specification of the recursive
    function [acclength]. Make sure to generalize the appropriate variables
    before applying the well-founded induction tactic. Then, complete the proof
    of the specification [triple_mlength'], using [xapp triple_acclength] to
    reason about the call to the auxiliary function. *)

(* FILL IN HERE *)

Lemma triple_mlength' : forall L p,
  triple (mlength' p)
    (MList L p)
    (fun r => \[r = val_int (length L)] \* (MList L p)).
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(* ================================================================= *)
(** ** In-Place Reversal Function for Lists *)

(** The function [mrev] takes as argument a pointer on a mutable list, and
    returns a pointer on the reverse list, that is, a list with elements in the
    reverse order. The cells from the input list are reused for constructing the
    output list. The operation is said to be "in place".

OCaml:

    let rec mrev_aux p1 p2 =
      if p2 == null
        then p1
        else (let p3 = p2.tail in
              p2.tail <- p1;
              mrev_aux p2 p3)

    let mrev p =
      mrev_aux p null
*)

Definition mrev_aux : val :=
  <{ fix 'f 'p1 'p2 =>
       let 'b = ('p2 = null) in
       if 'b
         then 'p1
         else (
           let 'p3 = 'p2`.tail in
           'p2`.tail := 'p1;
           'f 'p2 'p3) }>.

Definition mrev : val :=
  <{ fun 'p =>
       mrev_aux null 'p }>.

(** **** Exercise: 5 stars, standard, optional (triple_mrev)

    Prove the correctness of the functions [mrev_aux] and [mrev]. Hint: here
    again, start by stating a lemma [mtriple_rev_aux] expressing the
    specification of the recursive function [mrev_aux]. Make sure to generalize
    the appropriate variables before applying the well-founded induction tactic.
    Then, complete the proof of [triple_mrev], using [xapp triple_mrev_aux]. *)

(* FILL IN HERE *)

Lemma triple_mrev : forall L p,
  triple (mrev p)
    (MList L p)
    (funloc q => MList (rev L) q).
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(* ################################################################# *)
(** * More Details *)

(* ================================================================= *)
(** ** Sized Stack *)

Module SizedStack.

(** In this section, we consider the implementation of a mutable stack featuring
    a constant-time access to the size of the stack. This stack structure
    consists of a 2-field record, storing a pointer on a mutable linked list,
    and an integer storing the length of that list. The implementation includes
    a function [create] to allocate an empty stack, a function [sizeof] for
    reading the size, and three functions [push], [top] and [pop] for operating
    at the top of the stack.

OCaml:

    type 'a stack = { data : 'a list; size : int }

    let create () =
      { data = nil; size = 0 }

    let sizeof s =
      s.size

    let push p x =
      s.data <- mcons x s.data;
      s.size <- s.size + 1

    let top s =
      let p = s.data in
      p.head

    let pop s =
      let p = s.data in
      let x = p.head in
      let q = p.tail in
      delete p;
      s.data <- q in
      s.size <- s.size - 1;
      x
*)

(** The representation predicate for the stack takes the form [Stack L s], where
    [s] denotes the location of the record describing the stack, and where [L]
    denotes the list of items stored in the stack. The underlying mutable list
    is described as [MList L p], where [p] is the location [p] stored in the
    first field of the record. The definition of [Stack] is as follows. *)

Definition data : field := 0%nat.
Definition size : field := 1%nat.

Definition Stack (L:list val) (s:loc) : hprop :=
  \exists p, s ~~~>`{ data := p; size := length L } \* (MList L p).

(** Observe that the predicate [Stack] does not expose the location of the
    mutable list; this location is existentially quantified in the definition.
    The predicate [Stack] also does not expose the size of the stack, as this
    value can be deduced by computing [length L]. Let's start with the
    specification and verification of [create] and [sizeof]. *)

Definition create : val :=
  <{ fun 'u =>
      `{ data := null; size := 0 } }>.

Lemma triple_create :
  triple (create ())
    \[]
    (funloc s => Stack nil s).
Proof using.
  xwp. xapp triple_new_hrecord_2; auto. intros s.
  unfold Stack. xsimpl*. xchange* <- (MList_nil null).
Qed.

(** The [sizeof] operation returns the contents of the [size] field of a stack.
    *)

Definition sizeof : val :=
  <{ fun 'p =>
      'p`.size }>.

Lemma triple_sizeof : forall L s,
  triple (sizeof s)
    (Stack L s)
    (fun r => \[r = length L] \* Stack L s).
Proof using.
  xwp. unfold Stack. xpull. intros p. xapp. xsimpl*.
Qed.

(** The [push] operation extends the head of the list, and increments the size
    field. *)

Definition push : val :=
  <{ fun 's 'x =>
       let 'p = 's`.data in
       let 'p2 = mcons 'x 'p in
       's`.data := 'p2;
       let 'n = 's`.size in
       let 'n2 = 'n + 1 in
       's`.size := 'n2 }>.

(** **** Exercise: 3 stars, standard, especially useful (triple_push)

    Prove the following specification for the [push] operation. *)

Lemma triple_push : forall L s x,
  triple (push s x)
    (Stack L s)
    (fun u => Stack (x::L) s).
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** The [pop] operation extracts the element at the head of the list, updates
    the [data] field to the tail of the list, and decrements the size field. *)

Definition pop : val :=
  <{ fun 's =>
       let 'p = 's`.data in
       let 'x = 'p`.head in
       let 'p2 = 'p`.tail in
       delete 'p;
       's`.data := 'p2;
       let 'n = 's`.size in
       let 'n2 = 'n - 1 in
       's`.size := 'n2;
       'x }>.

(** **** Exercise: 4 stars, standard, especially useful (triple_pop)

    Prove the following specification for the [pop] operation. *)

Lemma triple_pop : forall L s,
  L <> nil ->
  triple (pop s)
    (Stack L s)
    (fun x => \exists L', \[L = x::L'] \* Stack L' s).
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** The [top] operation extracts the element at the head of the list. *)

Definition top : val :=
  <{ fun 's =>
       let 'p = 's`.data in
       'p`.head }>.

(** **** Exercise: 2 stars, standard, optional (triple_top)

    Prove the following specification for the [top] operation. *)

Lemma triple_top : forall L s,
  L <> nil ->
  triple (top s)
    (Stack L s)
    (fun x => \exists L', \[L = x::L'] \* Stack L s).
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

End SizedStack.

(* ================================================================= *)
(** ** Formalization of the Tree Representation Predicate *)

(** In this section, we generalize the ideas presented for linked lists to
    binary trees. For simplicity, let us consider binary trees that store
    integer values in the nodes. Just like mutable lists are specified with
    respect to Coq's purely functional lists, mutable binary trees are specified
    with respect to Coq trees. Consider the following inductive definition of
    the type [tree]. A leaf is represented by the constructor [Leaf], and a node
    takes the form [Node n T1 T2], where [n] is an integer and [T1] and [T2]
    denote the two subtrees. *)

Inductive tree : Type :=
  | Leaf : tree
  | Node : int -> tree -> tree -> tree.

Implicit Types T : tree.

(** In a program manipulating a mutable tree, an empty tree is represented using
    the [null] pointer, and a node is represented in memory using a three-cell
    record. The first field, named "item", stores an integer. The other two
    fields, named "left" and "right", store pointers to the left and right
    subtrees, respectively. *)

Definition item : field := 0%nat.
Definition left : field := 1%nat.
Definition right : field := 2%nat.

(** The heap predicate [p ~~~>`{ item := n; left := p1; right := p2 }] describes
    a record allocated at location [p], storing the integer [n] and the two
    pointers [p1] and [p2].

    The representation predicate [MTree T p], of type [hprop], asserts that the
    mutable tree structure with root at location [p] describes the logical tree
    [T]. The predicate is defined recursively on the structure of [T]:

    - if [T] is a [Leaf], then [p] is the null pointer,
    - if [T] is a node [Node n T1 T2], then [p] is not null, and at location
      [p] one finds a record with field contents [n], [p1] and [p2], with
      [MTree T1 p1] and [MTree T2 p2] describing the two subtrees. *)

Fixpoint MTree (T:tree) (p:loc) : hprop :=
  match T with
  | Leaf => \[p = null]
  | Node n T1 T2 => \exists p1 p2,
         (p ~~~>`{ item := n; left := p1; right := p2 })
      \* (MTree T1 p1)
      \* (MTree T2 p2)
  end.

(* ================================================================= *)
(** ** Alternative Characterization of [MTree] *)

(** Just like for [MList], it is very useful for proofs to state three lemmas
    that paraphrase the definition of [MTree]. The first two lemmas correspond
    to the folding/unfolding rules for leaves and nodes. *)

Lemma MTree_Leaf : forall p,
  (MTree Leaf p) = \[p = null].
Proof using. auto. Qed.

Lemma MTree_Node : forall p n T1 T2,
  (MTree (Node n T1 T2) p) =
  \exists p1 p2,
       (p ~~~>`{ item := n; left := p1; right := p2 })
    \* (MTree T1 p1) \* (MTree T2 p2).
Proof using. auto. Qed.

(** The third lemma reformulates [MTree T p] using a case analysis on whether
    [p] is the null pointer. This formulation matches the case analysis
    typically perform in the code of functions that operates on trees. *)

Lemma MTree_if : forall (p:loc) (T:tree),
      (MTree T p)
  ==> (If p = null
        then \[T = Leaf]
        else \exists n p1 p2 T1 T2, \[T = Node n T1 T2]
             \* (p ~~~>`{ item := n; left := p1; right := p2 })
             \* (MTree T1 p1) \* (MTree T2 p2)).
Proof using.
  intros. destruct T as [|n T1 T2].
  { xchange MTree_Leaf. intros M. case_if. xsimpl*. }
  { xchange MTree_Node. intros p1 p2.
    xchange hrecord_not_null. intros N. case_if. xsimpl*. }
Qed.

Opaque MTree.

(* ================================================================= *)
(** ** Additional Tooling for [MTree] *)

(** For reasoning about recursive functions over trees, it is useful to exploit
    the well-founded order associated with "immediate subtrees". Concretely,
    [tree_sub T1 T] asserts that the tree [T1] is either the left or the right
    subtree of the tree [T]. This order may be exploited for verifying recursive
    functions over trees using the tactic [induction_wf IH: tree_sub T]. *)

Inductive tree_sub : binary (tree) :=
  | tree_sub_1 : forall n T1 T2,
      tree_sub T1 (Node n T1 T2)
  | tree_sub_2 : forall n T1 T2,
      tree_sub T2 (Node n T1 T2).

Lemma tree_sub_wf : wf tree_sub.
Proof using.
  intros T. induction T; constructor; intros t' H; inversions~ H.
Qed.

Hint Resolve tree_sub_wf : wf.

(** For allocating fresh tree nodes as a 3-field record, we introduce the
    operation [mnode n p1 p2], defined and specified as follows. *)

Definition mnode : val :=
  val_new_hrecord_3 item left right.

(** A first specification of [mnode] describes the allocation of a record. *)

Lemma triple_mnode : forall n p1 p2,
  triple (mnode n p1 p2)
    \[]
    (funloc p => p ~~~> `{ item := n ; left := p1 ; right := p2 }).
Proof using. intros. applys* triple_new_hrecord_3. Qed.

(** A second specification, derived from the first, asserts that, if provided
    the description of two subtrees [T1] and [T2] at locations [p1] and [p2],
    the operation [mnode n p1 p2] builds, at a fresh location [p], a tree
    described by [Mtree [Node n T1 T2] p]. Compared with the first
    specification, this second specification is said to perform "ownership
    transfer". *)

(** **** Exercise: 2 stars, standard, optional (triple_mnode')

    Prove the specification [triple_mnode'] for node allocation. *)

Lemma triple_mnode' : forall T1 T2 n p1 p2,
  triple (mnode n p1 p2)
    (MTree T1 p1 \* MTree T2 p2)
    (funloc p => MTree (Node n T1 T2) p).
Proof using. (* FILL IN HERE *) Admitted.

Hint Resolve triple_mnode' : triple.

(** [] *)

(* ================================================================= *)
(** ** Tree Copy *)

(** The operation [tree_copy] takes as argument a pointer [p] on a mutable tree
    and returns a fresh copy of that tree. It is defined in a similar way to the
    function [mcopy] for lists.

OCaml:

    let rec tree_copy p =
      if p = null
        then null
        else mnode p.item (tree_copy p.left) (tree_copy p.right)
*)

Definition tree_copy :=
  <{ fix 'f 'p =>
       let 'b = ('p = null) in
       if 'b then null else (
         let 'n = 'p`.item in
         let 'p1 = 'p`.left in
         let 'p2 = 'p`.right in
         let 'q1 = 'f 'p1 in
         let 'q2 = 'f 'p2 in
         mnode 'n 'q1 'q2
      ) }>.

(** **** Exercise: 3 stars, standard, optional (triple_tree_copy)

    Prove the specification of [tree_copy]. *)

Lemma triple_tree_copy : forall p T,
  triple (tree_copy p)
    (MTree T p)
    (funloc q => (MTree T p) \* (MTree T q)).
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(* ================================================================= *)
(** ** Computing the Sum of the Items in a Tree *)

(** The operation [mtreesum] takes as argument the location [p] of a mutable
    tree, and it returns the sum of all the integers stored in the nodes of that
    tree. Consider the implementation that traverses the tree, using an
    auxiliary reference cell to maintain the sum of all the items visited so
    far.

OCaml:

    let rec treeacc c p =
      if p <> null then (
        c := !c + p.item;
        treeacc c p.left;
        treeacc c p.right)

    let mtreesum p =
      let c = ref 0 in
      treeacc c p;
      !c
*)

Definition treeacc : val :=
  <{ fix 'f 'c 'p =>
       let 'b = ('p <> null) in
       if 'b then
         let 'm = ! 'c in
         let 'x = 'p`.item in
         let 'm2 = 'm + 'x in
         'c := 'm2;
         let 'p1 = 'p`.left in
         'f 'c 'p1;
         let 'p2 = 'p`.right in
         'f 'c 'p2
       end }>.

Definition mtreesum : val :=
  <{ fun 'p =>
       let 'c = ref 0 in
       treeacc 'c 'p;
       get_and_free 'c }>.

(** The specification of [mtreesum] is expressed in terms of the Coq function
    [treesum], which computes the sum of the node items stored in a logical
    tree. This operation is defined by recursion over the tree. *)

Fixpoint treesum (T:tree) : int :=
  match T with
  | Leaf => 0
  | Node n T1 T2 => n + treesum T1 + treesum T2
  end.

(** **** Exercise: 4 stars, standard, optional (triple_mtreesum)

    Prove the correctness of the function [mlength']. Hint: to begin with, state
    and prove the specification lemma [triple_treeacc]. *)

(* FILL IN HERE *)

Lemma triple_mtreesum : forall T p,
  triple (mtreesum p)
    (MTree T p)
    (fun r => \[r = treesum T] \* (MTree T p)).
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(* ================================================================= *)
(** ** Verification of a Counter Function with Local State *)

(** This section is concerned with the verification of counter functions, which
    feature internal, mutable state. A counter function [f] is a function that,
    each time it is called, returns the next integer. Concretely, the first call
    to [f()] returns [1], the second call to [f()] returns [2], the third call
    to [f()] returns [3], and so on.

    A counter function can be implemented using a reference cell, named [p],
    that stores the integer last returned by the counter. Initially, the
    contents of the reference [p] is zero. Each time the counter function is
    called, the contents of [p] is increased by one unit, and the new value of
    the contents is returned to the caller.

    The function [create_counter] produces a fresh counter function. Concretely,
    [create_counter()] returns a counter function [f] independent from any other
    previously existing counter function.

OCaml:

    let create_counter () =
       let p = ref 0 in
       (fun () -> (incr p; !p))
*)

Definition create_counter : val :=
  <{ fun 'u =>
       let 'p = ref 0 in
       (fun_ 'u => (incr 'p; !'p)) }>.

(** In this section, we present two specifications for counter functions. The
    first specification is the most direct, however it exposes the existence of
    the reference cell, revealing implementation details about the counter
    function. The second specification is more abstract: it hides from the
    client the internal representation of the counter, by means of using an
    abstract representation predicate. *)

(** Let us begin with the simple, direct specification. The proposition
    [CounterSpec f p] asserts that [f] is a counter function [f] whose internal
    state is stored in a reference cell at location [p]. Thus, invoking [f] in a
    state [p ~~> m] updates the state to [p ~~> (m+1)], and produces the output
    value [m+1]. *)

Definition CounterSpec (f:val) (p:loc) : Prop :=
  forall m, triple (f ())
                    (p ~~> m)
                    (fun r => \[r = m+1] \* p ~~> (m+1)).

Implicit Type f : val.

(** The function [create_counter] creates a fresh counter. Its precondition is
    empty. Its postcondition asserts that the function [f] being returned
    satisfies [CounterSpec f p], and the output state contains a cell [p ~~> 0]
    for some existentially quantified location [p]. *)

Lemma triple_create_counter :
  triple (create_counter ())
    \[]
    (fun f => \exists p, (p ~~> 0) \* \[CounterSpec f p]).
Proof using.
  xwp. xapp. intros p.
(** The proof involves the use of a new tactic, called [xfun], for reasoning
    about local function definitions. Here, [xfun] gives us the hypothesis [Hf]
    that specifies the code of [f] *)
  xfun. intros f Hf.
  xsimpl.
  { intros m.
(** To reason about the call to the function [f], we can exploit [Hf], either
    explicitly by calling [applys Hf], or automatically by simply calling [xapp]
    . *)
    xapp.
    xapp. xapp. xsimpl. auto. }
Qed.

(** Consider now a call to a counter function [f], under the assumption
    [CounterSpec f p]. Assume the input state to be of the form [p ~~> n] for
    some [n]. Then, the call produces a state [p ~~> (n+1)], and returns the
    value [n+1]. The specification shown below captures this logic, for any [f].
    *)

Lemma triple_apply_counter : forall f p n,
  CounterSpec f p ->
  triple (f ())
    (p ~~> n)
    (fun r => \[r = n+1] \* (p ~~> (n+1))).
(** The specification above is in fact nothing but a reformulation of the
    definition of [CounterSpec]. Thus, its proof is straightforwards. (The proof
    may actually be reduced to just [auto], however in general one needs to use
    [xapp] for reasoning about an abstract function.) *)
Proof using. introv Hf. unfolds in Hf. xapp. xsimpl*. Qed.

(* ================================================================= *)
(** ** Verification of a Counter Function with Local State, With Abstraction *)

(** Let us move on to the presentation of more abstract specifications. The goal
    is to hide from the client the existence of the reference cell used to
    represent the internal state of the counter functions. To that end, we
    introduce the heap predicate [IsCounter f n], which relates a function [f],
    its current value [n], and the piece of memory state involved in the
    implementation of this function. This piece of memory is of the form
    [p ~~> n], for some location [p], such that [CounterSpec f p] holds. *)

Definition IsCounter (f:val) (n:int) : hprop :=
  \exists p, p ~~> n \* \[CounterSpec f p].

(** Using [IsCounter], we can reformulate the specification of [create_counter]
    with a postcondition asserting that the output function [f] is described by
    the heap predicate [IsCounter f 0]. *)

Lemma triple_create_counter_abstract :
  triple (create_counter ())
    \[]
    (fun f => IsCounter f 0).
(** This lemma is the same as the previous specification [triple_create_counter]
    , except that the reference cell [p] is no longer visible. *)
Proof using. unfold IsCounter. applys triple_create_counter. Qed.

(** We can also reformulate the specification of a call to a counter function. A
    call to [f()], in a state satisfying [IsCounter f n], produces a state
    satisfying [IsCounter f (n+1)], and returns [n+1]. *)

(** **** Exercise: 4 stars, standard, especially useful (triple_apply_counter_abstract)

    Prove the abstract specification for a counter function. You will need to
    begin the proof using the tactic [xtriple], for turning goal into a form on
    which [xpull] can be invoked to extract facts from the precondition. *)

Lemma triple_apply_counter_abstract : forall f n,
  triple (f ())
    (IsCounter f n)
    (fun r => \[r = n+1] \* (IsCounter f (n+1))).
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

Opaque IsCounter.

(* ################################################################# *)
(** * Optional Material *)

(* ================================================================= *)
(** ** Specification of a Higher-Order Repeat Operator *)

(** Consider the higher-order iterator [repeat]: a call to [repeat f n] executes
    [n] times the call [f()].

OCaml:

    let rec repeat f n =
      if n > 0 then (f(); repeat f (n-1))
*)

Definition repeat : val :=
  <{ fix 'g 'f 'n =>
       let 'b = ('n > 0) in
       if 'b then
         'f ();
         let 'n2 = 'n - 1 in
         'g 'f 'n2
       end }>.

(** For simplicity, let us assume for now [n >= 0]. The specification of
    [repeat n f] can be expressed in terms of an invariant, named [I],
    describing the state in between every two calls to [f]. We assume that the
    initial state satisfies [I 0]. Moreover, we assume that, for every index [i]
    in the range from [0] (inclusive) to [n] (exclusive), a call [f()] can
    execute in a state that satisfies [I i] and produce a state that satisfies
    [I (i+1)]. The specification below asserts that, under these two
    assumptions, after the [n] calls to [f()], the final state satisfies [I n].
    The specification takes the form:

    n >= 0 ->
    Hypothesis_on_f ->
    triple (repeat f n)
      (I 0)
      (fun u => I n)

    where [Hypothesis_on_f] is a proposition that captures the following
    specification:

    forall i,
    0 <= i < n ->
    triple (f ())
      (I i)
      (fun u => I (i+1))

    The complete specification of [repeat n f] is thus as shown below. *)

Lemma triple_repeat : forall (I:int->hprop) (f:val) (n:int),
  n >= 0 ->
  (forall i, 0 <= i < n ->
    triple (f ())
      (I i)
      (fun u => I (i+1))) ->
  triple (repeat f n)
    (I 0)
    (fun u => I n).
Proof using.
  introv Hn Hf.

(** To establish this specification, we carry out a proof by induction over a
    generalized specification, covering the case where there remains [m]
    iterations to perform, for any value of [m] between [0] and [n] inclusive.

    forall m, 0 <= m <= n ->
    triple (repeat f m)
      (I (n-m))
      (fun u => I n))

    We use the TLC tactics [cuts], a variant of [cut], to state show that the
    generalized specification entails the statement of [triple_repeat]. *)
  cuts G: (forall m, 0 <= m <= n ->
    triple (repeat f m)
      (I (n-m))
      (fun u => I n)).
  { applys_eq G. { fequals. math. } { math. } }
(** We then carry a proof by induction: during the execution, the value of [m]
    decreases step by step down to [0]. *)
  intros m. induction_wf IH: (downto 0) m. intros Hm.
  xwp. xapp. xif; intros C.
(** We reason about the call to [f] *)
  { xapp. { math. } xapp.
(** We next reason about the recursive call. *)
    xapp. { math. } { math. }
    math_rewrite ((n - m) + 1 = n - (m - 1)). xsimpl. }
(** Finally, when [m] reaches zero, we check that we obtain [I n]. *)
  { xval. math_rewrite (n - m = n). xsimpl. }
Qed.

(* ================================================================= *)
(** ** Specification of an Iterator on Mutable Lists *)

(** The operation [miter] takes as argument a function [f] and a pointer [p] on
    a mutable list, and invokes [f] on each of the items stored in that list.

OCaml:

    let rec miter f p =
      if p <> null then (f p.head; miter f p.tail)
*)

Definition miter : val :=
  <{ fix 'g 'f 'p =>
       let 'b = ('p <> null) in
       if 'b then
         let 'x = 'p`.head in
         'f 'x;
         let 'q = 'p`.tail in
         'g 'f 'q
       end }>.

(** The specification of [miter] follows the same structure as that of the
    function [repeat] from the previous section, with two main differences. The
    first difference is that the invariant is expressed not in terms of an index
    [i] ranging from [0] to [n], but in terms of a prefix of the list [L] being
    traversed. This prefix ranges from [nil] to the full list [L]. The second
    difference is that the operation [miter f p] requires in its precondition,
    in addition to [I nil], the description of the mutable list [MList L p].
    This predicate is returned in the postcondition, unchanged, reflecting the
    fact that the iteration process does not alter the contents of the list. *)

(** **** Exercise: 5 stars, standard, especially useful (triple_miter)

    Prove the correctness of [triple_miter]. *)

Lemma triple_miter : forall (I:list val->hprop) L (f:val) p,
  (forall x L1 L2, L = L1++x::L2 ->
    triple (f x)
      (I L1)
      (fun u => I (L1++(x::nil)))) ->
  triple (miter f p)
    (MList L p \* I nil)
    (fun u => MList L p \* I L).
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** For exploiting the specification [triple_miter] to reason about a call to
    [miter], it is necessary to provide an invariant [I] of type
    [list val -> hprop], that is, of the form [fun (K:list val) => ...]. This
    invariant, which cannot be inferred automatically, should describe the state
    at the point where the iteration has traversed a prefix [K] of the list [L].
    Concretely, for reasoning about a call to [miter], one should exploit the
    tactic [xapp (triple_iter (fun K => ...))]. An example appears next. *)

(* ================================================================= *)
(** ** Computing the Length of a Mutable List using an Iterator *)

(** The function [mlength_using_miter] computes the length of a mutable list by
    iterating over that list a function that increments a reference cell once
    for every item.

OCaml:

    let mlength_using_miter p =
      let c = ref 0 in
      miter (fun x -> incr c) p;
      !c
*)

(** **** Exercise: 4 stars, standard, especially useful (triple_mlength_using_miter)

    Prove the correctness of [mlength_using_iter]. Hint: as explained earlier,
    use [xfun; intros f Hf] for reasoning about the function definition, then
    use [xapp] for reasoning about a call to [f]. *)

Definition mlength_using_miter : val :=
  <{ fun 'p =>
       let 'c = ref 0 in
       let 'f = (fun_ 'x => incr 'c) in
       miter 'f 'p;
       get_and_free 'c }>.

Lemma triple_mlength_using_miter : forall p L,
  triple (mlength_using_miter p)
    (MList L p)
    (fun r => \[r = length L] \* MList L p).
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(* ================================================================= *)
(** ** A Continuation-Passing-Style, In-Place Concatenation Function *)

(** This section presents an example verification of a function involving
    "continuations". The function [cps_append] is similar to the function
    [append] presented previously: it also performs in-place concatenation of
    two lists. The main difference is that it is implemented using an auxiliary
    recursive function in "continuation-passing style" (CPS).

    The presentation of [cps_append p1 p2] is also slightly different: this
    operation returns a pointer [p3] that describes the head of the result of
    the concatenation. In the general case, [p3] is equal to [p1], but if [p1]
    is the null pointer, meaning that the first list is empty, then [p3] is
    equal to [p2].

    The code of [cps_append] involves the auxiliary function
    [cps_append_aux p1 p2 k], which invokes the continuation function [k] on the
    result of concatenating the lists at locations [p1] and [p2]. Its code
    appears at first quite puzzling, because the recursive call is performed
    inside the continuation. It takes a good drawing and at least several
    minutes to figure out how the function works.

OCaml:

    let rec cps_append_aux p1 p2 k =
      if p1 == null
        then k p2
        else cps_append_aux p1.tail p2 (fun r => (p1.tail <- r); k p1)

    let cps_append p1 p2 =
      cps_append_aux p1 p2 (fun r => r)
*)

Definition cps_append_aux : val :=
  <{ fix 'f 'p1 'p2 'k =>
       let 'b = ('p1 = null) in
       if 'b
         then 'k 'p2
         else
           let 'q1 = 'p1`.tail in
           let 'k2 = (fun_ 'r => ('p1`.tail := 'r; 'k 'p1)) in
           'f 'q1 'p2 'k2 }>.

Definition cps_append : val :=
  <{ fun 'p1 'p2 =>
      let 'f = (fun_ 'r => 'r) in
      cps_append_aux 'p1 'p2 'f }>.

(** **** Exercise: 5 stars, standard, optional (triple_cps_append)

    Specify and verify [cps_append_aux], then verify [cps_append]. *)

(* FILL IN HERE *)

Lemma triple_cps_append : forall (L1 L2:list val) (p1 p2:loc),
  triple (cps_append p1 p2)
    (MList L1 p1 \* MList L2 p2)
    (funloc p3 => MList (L1++L2) p3).
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(* ================================================================= *)
(** ** Historical Notes *)

(** The representation predicate for lists appears in the seminal papers on
    Separation Logic: the notes by Reynolds from the summer 1999, updated the
    next summer [Reynolds 2000] (in Bib.v), and the publication by
    [O’Hearn, Reynolds, and Yang 2001] (in Bib.v). The function [cps_append] was
    proposed in Reynolds's article as an open challenge for verification.

    Most presentations of Separation Logic target partial correctness, whereas
    this chapters targets total correctness. The specifications of recursive
    functions are established using the built-in induction mechanism offered by
    Coq.

    The specification of higher-order iterators requires higher-order Separation
    Logic. Being embedded in the higher-order logic of Coq, the Separation Logic
    that we work with is inherently higher-order. Further information on the
    history of higher-order Separation Logic for higher-order programs may be
    found in section 10.2 of
    http://www.chargueraud.org/research/2020/seq_seplogic/seq_seplogic.pdf . *)

(* 2021-11-09 17:42 *)
