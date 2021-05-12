(** * Repr: Representation Predicates *)

Set Implicit Arguments.
From SLF Require Import LibSepReference.
Import ProgramSyntax DemoPrograms.
From SLF Require Import Basic.
Open Scope liblist_scope.

Implicit Types n m : int.
Implicit Types p q s c : loc.

(* ################################################################# *)
(** * First Pass *)

(** SOONER AC: polish
    As explained in the preface
    chapters from there on are made of 3 parts:
    first pass, more details, optional material.
    *)

(** This chapter introduces the notion of representation predicate,
    which is typically used for describing mutable data structures.
    For example, this chapter introduces the heap predicate [MList L p]
    to describe a mutable linked list whose head cell is at location [p],
    and whose elements are described by the Coq list [L].

    This chapter explains how to specify and verify functions that
    operate on mutable linked lists and mutable trees. It also presents
    representation predicates for functions that capture local state,
    such as a counter function.

    This chapter assumes a programming language featuring records,
    and it assumes the Separation Logic to support heap predicates for
    describing records. For example, [p ~~~>`{ head := x; tail := q}]
    describes a record allocated at location [p], with a head field
    storing the value [x] and a tail field storing the value [q].
    In this course, for simplicity, we implement field names as natural
    numbers---e.g., [head] is defined as [0] and [tail] as [1]. Details
    on the formalization of records are postponed to chapter [Struct].

    This chapter introduces a few additional tactics:

    - [xfun] to reason about a function definition.
    - [xchange] for exploiting transitivity of [==>]. *)

(* ================================================================= *)
(** ** Formalization of the List Representation Predicate *)

(** A mutable list cell is a two-cell record, featuring a head field and a
    tail field. *)

Definition head : field := 0%nat.
Definition tail : field := 1%nat.

(** The heap predicate [p ~~~>`{ head := x; tail := q}] describes a
    record allocated at location [p], with a head field storing [x]
    and a tail field storing [q]. *)

(** A mutable list consists of a chain of cells, terminated by [null].

    The heap predicate [MList L p] describes a list whose head cell is
    at location [p], and whose elements are described by the list [L].
    This predicate is defined recursively on the structure of [L]:

    - if [L] is empty, then [p] is the null pointer,
    - if [L] is of the form [x::L'], then [p] is not null, the
      head field of [p] contains [x], and the tail field of [p]
      contains a pointer [q] such that [MList L' q] describes the
      tail of the list. *)

Fixpoint MList (L:list val) (p:loc) : hprop :=
  match L with
  | nil => \[p = null]
  | x::L' => \exists q, (p ~~~> `{ head := x; tail := q}) \* (MList L' q)
  end.

(* ================================================================= *)
(** ** Alternative Characterizations of [MList] *)

(** The following reformulations are helpful in proofs, allowing us to
    fold or unfold the definition using a tactic called [xchange]. *)

Lemma MList_nil : forall p,
  (MList nil p) = \[p = null].
Proof using. auto. Qed.

Lemma MList_cons : forall p x L',
  MList (x::L') p =
  \exists q, (p ~~~> `{ head := x; tail := q}) \* (MList L' q).
Proof using. auto. Qed.

(** Another characterization of [MList L p] is useful for proofs. Whereas
    the original definition is by case analysis on whether [L] is empty,
    the alternative one is by case analysis on whether [p] is null:

    - if [p] is null, then [L] is empty,
    - otherwise, [L] decomposes as [x::L'], the head field of [p] contains [x],
      and the tail field of [p] contains a pointer [q] such that [MList L' q]
      describes the tail of the list.

    The lemma below is stated using an entailment. The reciprocal entailment
    is also true, but we do not need it so we do not bother proving it here. *)

Lemma MList_if : forall (p:loc) (L:list val),
      (MList L p)
  ==> (If p = null
        then \[L = nil]
        else \exists x q L', \[L = x::L']
             \* (p ~~~> `{ head := x; tail := q}) \* (MList L' q)).
Proof using.
  (* Let's prove this result by case analysis on [L]. *)
  intros. destruct L as [|x L'].
  { (* Case [L = nil]. By definition of [MList], we have [p = null]. *)
    xchange MList_nil. intros M.
    (* We have to justify [L = nil], which is trivial.
       The TLC [case_if] tactic performs a case analysis on the argument
       of the first visible [if] conditional. *)
    case_if. xsimpl. auto. }
  { (* Case [L = x::L']. *)
  (* One possibility is to perform a rewrite operation using [MList_cons]
     on its first occurrence. Then using CFML the tactic [xpull] to extract
     the existential quantifiers out from the precondition:
     [rewrite MList_cons. xpull. intros q.]
     A more efficient approach is to use the dedicated CFML tactic [xchange],
     which is specialized for performing updates in the current state. *)
    xchange MList_cons. intros q.
    (* Because a record is allocated at location [p], the pointer [p]
       cannot be null. The lemma [hrecord_not_null] allows us to exploit
       this property, extracting the hypothesis [p <> null]. We use again
       the tactic [case_if] to simplify the case analysis. *)
    xchange hrecord_not_null. intros N. case_if.
    (* To conclude, it suffices to correctly instantiate the existential
       quantifiers. The tactic [xsimpl] is able to guess the appropriate
       instantiations. *)
     xsimpl. auto. }
Qed.

Global Opaque MList.

(* ================================================================= *)
(** ** In-place Concatenation of Two Mutable Lists *)

(** The function [append] shown below expects a nonempty list [p1] and a list
    [p2], and it updates [p1] in place so that its tail gets extended by the
    cells from [p2].

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

(** The append function is specified and verified as follows. The
    proof pattern is representative of that of many list-manipulating
    functions, so it is essential that the reader follow through every
    step of the proof. *)

Lemma triple_append : forall (L1 L2:list val) (p1 p2:loc),
  p1 <> null ->
  triple (append p1 p2)
    (MList L1 p1 \* MList L2 p2)
    (fun _ => MList (L1++L2) p1).
Proof using.
(** The induction principle provides an hypothesis for the tail of [L1],
    i.e., for the list [L1'], such that the relation [list_sub L1' L1]
    holds. *)
  introv K. gen p1. induction_wf IH: list_sub L1. introv N. xwp.
(** To begin the proof, we reveal the head cell of [p1].
    We let [q1] denote the tail of [p1], and [L1'] the tail of [L1]. *)
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

Implicit Types x : val.

(** This section introduces two smart constructors for linked lists,
    called [mnil] and [mcons].

    The operation [mnil()] is intended to create an empty list.
    Its implementation simply returns the value [null]. Its
    specification asserts that the return value is a pointer [p]
    such that [MList nil p] holds. *)

Definition mnil : val :=
  <{ fun 'u =>
       null }>.

Lemma triple_mnil :
  triple (mnil ())
    \[]
    (funloc p => MList nil p).
Proof using. xwp. xval. xchanges* <- (MList_nil null). Qed.

Hint Resolve triple_mnil : triple.

(** Observe that the specification [triple_mnil] does not mention
    the [null] pointer anywhere. This specification may thus be
    used to specify the behavior of operations on mutable lists
    without having to reveal low-level implementation details that
    involve the [null] pointer. *)

(** The operation [mcons x q] is intended to allocate a fresh list cell,
    with [x] in the head field and [q] in the tail field. The implementation
    of this operation allocates and initializes a fresh record made of
    two fields. The allocation operation leverages the [New] construct, which
    is notation for a operation called [val_new_hrecord_2], which we here view
    as a primitive operation. (The chapter [Struct] describes an encoding
    of this function in terms of the allocation and write operations.) *)

Definition mcons : val :=
  <{ fun 'x 'q =>
       `{ head := 'x; tail := 'q } }>.

(** The operation [mcons] admits two specifications: one that describes only
    the fresh record allocated, and one that combines it with a list
    representation of the form [Mlist q L] to produce as postcondition
    an extended list of the form [Mlist p (x::L)].

    The first specification is as follows. *)

Lemma triple_mcons : forall x q,
  triple (mcons x q)
    \[]
    (funloc p => p ~~~> `{ head := x ; tail := q }).
Proof using. xwp. xapp triple_new_hrecord_2; auto. xsimpl*. Qed.

(** The second specification is derived from the first. *)

Lemma triple_mcons' : forall L x q,
  triple (mcons x q)
    (MList L q)
    (funloc p => MList (x::L) p).
Proof using.
  intros. xapp triple_mcons.
  intros p. xchange <- MList_cons. xsimpl*.
Qed.

Hint Resolve triple_mcons' : triple.

(* ================================================================= *)
(** ** Copy Function for Lists *)

(** The function [mcopy] takes a mutable linked list and builds
    an independent copy of it.

    This program illustrates the use the of functions [mnil] and
    [mcons], and gives another example of a proof by induction.

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

(** The precondition of [mcopy] requires a linked list [MList L p].
    Its postcondition asserts that the function returns a pointer [p']
    and a list [MList L p'], in addition to the original list [MList L p].
    The two lists are totally disjoint and independent, as captured by
    the separating conjunction symbol (the star). *)

Lemma triple_mcopy : forall L p,
  triple (mcopy p)
    (MList L p)
    (funloc p' => (MList L p) \* (MList L p')).
(** The proof script is very similar in structure to the previous ones.
    While playing the script, try to spot the places where:

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

(** The function [mlength] takes a mutable linked list and computes its
    length.

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

(** In the previous section, the function [mlength] computes the length using a
    recursive function that returns an integer. In this section, we consider an
    alternative implementation that uses an auxiliary reference cell to
    keep track of the number of cells traversed so far. The list is traversed
    recursively, incrementing the contents of the reference once for every
    cell. The corresponding implementation is shown below. The variable [c]
    denotes the location of the auxiliary reference cell.

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

    Prove the correctness of the function [mlength'].
    Hint: start by stating a lemma [triple_acclength] expressing the
    specification of the recursive function [acclength]. Then, register
    that specification for subsequent use by [xapp] using the command
    [Hint Resolve triple_acclength : triple]. Finally, complete the
    proof of the specification [triple_mlength']. *)

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
    returns a pointer on the reverse list, that is, a list with elements in
    the reverse order. The cells from the input list are reused for
    constructing the output list---the operation is "in-place". Its
    implementation appears next.

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

    Prove the correctness of the functions [mrev_aux] and [mrev].

    Hint: start by stating a lemma [mtriple_rev_aux] expressing the
    specification of the recursive function [mrev_aux]. Then, register
    the specification using [Hint Resolve triple_acclength : triple.].
    Finally, complete the proof of [triple_mrev].

    Hint: don't forget to generalize all the necessary variables before
    applying the well-founded induction principle. *)

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

(** In this section, we consider the implementation of a mutable stack with
    constant-time access to its size, i.e., to the number of items it stores.
    The stack structure consists of a 2-field record, storing a pointer on a
    mutable linked list, and an integer storing the length of that list.
    The stack implementation exposes a function to create an empty stack, a
    function for reading the size, and [push] and [pop] methods for operating
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

(** Observe that the predicate [Stack] does not expose the address of the
    mutable list; this adress is existentially quantified in the definition.
    The predicate [Stack] also does not expose the size of the stack, as this
    value can be deduced as [length L]. *)

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

(** The [sizeof] operation returns the contents of the [size] field of a
    stack. *)

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

(** The [push] operation extracts the element at the head of the list, updates
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

End SizedStack.

(* ================================================================= *)
(** ** Formalization of the Tree Representation Predicate *)

(** So far in this chapter, we have presented the representation of mutable
    lists in Separation Logic. We next consider the generalization to mutable
    binary trees.

    Just like mutable lists are specified with respect to Coq's purely
    functional lists, mutable binary trees are specified with respect to
    purely functional trees. For simplicity, let us consider a definition
    specialized for trees storing integer values in the nodes.

    The corresponding inductive definition is as shown below. A node from a
    logical tree takes the form [Node n T1 T2], where [n] is an integer and
    [T1] and [T2] denote the two subtrees. A leaf is represented by the
    constructor [Leaf]. *)

Inductive tree : Type :=
  | Leaf : tree
  | Node : int -> tree -> tree -> tree.

Implicit Types T : tree.

(** A mutable tree node consists of a three-cell record, featuring an field
    storing an integer named "item", and two pointers named "left" and "right",
    denoting the pointers to the left and right subtrees, respectively. *)

Definition item : field := 0%nat.
Definition left : field := 1%nat.
Definition right : field := 2%nat.

(** The heap predicate [p ~~~>`{ item := n; left := p1; right := p2 }]
    describes a record allocated at location [p], describing a node storing
    the integer [n], with its two subtrees at locations [p1] and [p2].
    An empty tree is represented using the [null] pointer.

    The representation predicate [MTree T p], of type [hprop], asserts that
    the mutable tree structure with root at location [p] describes the logical
    tree [T]. The predicate is defined recursively on the structure of [T]:

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

(** Just like for [MList], it is very useful for proofs to state three
    lemmas that paraphrase the definition of [MTree]. The first two
    lemmas correspond to folding/unfolding rules for leaves and nodes. *)

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
    typically perform in the code of functions operating on trees. *)

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

(** For reasoning about recursive functions over trees, it is useful to
    exploit the well-founded order associated with "immediate subtrees".
    This order, named [tree_sub], can be exploited for a tree [T] by
    invoking the tactic [induction_wf IH: tree_sub T]. *)

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

(** The first specification of [mnode] describes the allocation of a record. *)

Lemma triple_mnode : forall n p1 p2,
  triple (mnode n p1 p2)
    \[]
    (funloc p => p ~~~> `{ item := n ; left := p1 ; right := p2 }).
Proof using. intros. applys* triple_new_hrecord_3. Qed.

(** The second specification, derived from the first, asserts that, if provided
    the description of two subtrees [T1] and [T2] at locations [p1] and [p2],
    the operation [mnode n p1 p2] builds, at a fresh location [p], a tree
    described by [Mtree [Node n T1 T2] p]. *)

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
    and returns a fresh copy of that tree. It is constructed in similar way to
    the function [mcopy] for lists.

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
    tree, and it returns the sum of all the integers stored in the nodes of
    that tree. Consider the implementation that traverses the tree and uses
    an auxiliary reference cell for maintaining the sum of all the items
    visited so far.

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

(** The specification of [mtreesum] is expressed in terms of the logical
    operation [treesum] which computes the sum of the node items stored
    in a logical tree. This operation is defined in Coq as a fixed point. *)

Fixpoint treesum (T:tree) : int :=
  match T with
  | Leaf => 0
  | Node n T1 T2 => n + treesum T1 + treesum T2
  end.

(** **** Exercise: 4 stars, standard, optional (triple_mtreesum)

    Prove the correctness of the function [mlength'].
    Hint: start by stating a lemma [triple_treeacc], then register it
    using the command [Hint Resolve triple_treeacc : triple.]. Finally,
    complete the proof of the specification [triple_mtreesum]. *)

(* FILL IN HERE *)

Lemma triple_mtreesum : forall T p,
  triple (mtreesum p)
    (MTree T p)
    (fun r => \[r = treesum T] \* (MTree T p)).
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(* ================================================================= *)
(** ** Verification of a Counter Function with Local State *)

(** In this section, we present another kind of representation predicate:
    one that describes a function with an internal, mutable state. *)

Implicit Type f : val.

(** A counter function is a function [f] such that, each time it
    is invoked, returns the next integer, starting from 1.

    The function [create_counter] produces a fresh counter function.
    Concretely, if [create_counter()] produces the counter [f],
    then the first call to [f()] returns [1], the second call to
    [f()] returns [2], the third call to [f()] returns [3], and so on.

    The counter function can be implemented using a reference cell,
    named [p], that stores the integer last returned by the counter.
    Initially, the contents of the reference [p] is zero. Each time
    the counter is queried, the contents of [p] is increased by one
    unit, and the new value of the contents is returned to the caller.

OCaml:

    let create_counter () =
       let p = ref 0 in
       (fun () -> (incr p; !p))
*)

Definition create_counter : val :=
  <{ fun 'u =>
       let 'p = ref 0 in
       (fun_ 'u => (incr 'p; !'p)) }>.

(** The remaining of this section presents two set of specifications,
    each covering both the specification of a counter function and
    the specification of a function that creates a fresh counter function.

    The first specification is the most direct: it exposes the existence
    of a reference [p]. Doing so, however, reveals implementation details
    about the counter function.

    The second specification is more abstract: it successfully hides
    the description of the internal representation of the counter,
    and states specification only in terms of a representation predicate,
    called [IsCounter f n], that exposes only the identity of the
    counter function and its current value, but not the existence of
    the reference [p]. *)

(** Let's begin with the simple, direct specification. The proposition
    [CounterSpec f p] asserts that the counter function [f] has its
    internal state stored in a reference cell at location [p], in the
    sense that invoking [f] in a state [p ~~> m] updates the state to
    [p ~~> (m+1)] and produces the output value [m+1]. *)

Definition CounterSpec (f:val) (p:loc) : Prop :=
  forall m, triple (f ())
                    (p ~~> m)
                    (fun r => \[r = m+1] \* p ~~> (m+1)).

(** The function [create_counter] creates a fresh counter. Its precondition
    is empty. Its postcondition describes the existence of a reference
    cell [p ~~> 0], for an existentially quantified location [p], and such
    that the proposition [CounterSpec f p] holds. Observe the use of the
    tactic [xfun] for reasoning about a function definition. *)

Lemma triple_create_counter :
  triple (create_counter ())
    \[]
    (fun f => \exists p, (p ~~> 0) \* \[CounterSpec f p]).
Proof using.
  xwp. xapp. intros p. xfun. intros f Hf. xsimpl.
  { intros m. applys Hf. xapp. xapp. xsimpl. auto. }
Qed.

(** Given a counter function described by [CounterSpec f p], a call to the
    function [f] on a unit argument, in an input state of the form [p ~~> n]
    for some [n], produces the state [p ~~> (n+1)] and the output value [n+1].
    Observe how this specification applies to any function [f] satisfying
    [CounterSpec f p]. *)

Lemma triple_apply_counter : forall f p n,
  CounterSpec f p ->
  triple (f ())
    (p ~~> n)
    (fun r => \[r = n+1] \* (p ~~> (n+1))).
Proof using. introv Hf. applys Hf. Qed.

(** In the proof above, we were able to directly apply the assumption [Hf].
    In general, however, for reasoning about a call to an abstract function
    [f], it is generally needed to first invoke the tactic [xwp]. *)

Lemma triple_apply_counter_alternative_proof : forall f p n,
  CounterSpec f p ->
  triple (f ())
    (p ~~> n)
    (fun r => \[r = n+1] \* (p ~~> (n+1))).
Proof using.
  introv Hf. lets H: Hf n. xapp. xsimpl. auto.
Qed.

(** Let's now make the specifications more abstract, by hiding away the
    description of the reference cells from the client of the specifications.

    To that end, we introduce the heap predicate [IsCounter f n], which
    relates a function [f], its current value [n], and the piece of memory
    state involved in the implementation of this function. This piece of
    memory is of the form [p ~~> n] for some location [p], such that
    [CounterSpec f p] holds. Here, [p] gets quantified existentially. *)

Definition IsCounter (f:val) (n:int) : hprop :=
  \exists p, p ~~> n \* \[CounterSpec f p].

(** Using [IsCounter], we can reformulate the specification of
    [create_counter] is a more abstract and more concise manner,
    with a postcondition simply asserting that the fresh counter
    function [f] initialized at zero is described by the heap
    predicate [IsCounter f 0]. *)

Lemma triple_create_counter_abstract :
  triple (create_counter ())
    \[]
    (fun f => IsCounter f 0).
Proof using. unfold IsCounter. applys triple_create_counter. Qed.

(** Likewise, we can reformulate the specification of a call to a counter
    function [f]. Such a call, under precondition [IsCounter f n] for some
    [n], admits the precondition [IsCounter f (n+1)], and returns [n+1]. *)

(** **** Exercise: 3 stars, standard, especially useful (triple_apply_counter_abstract)

    Prove the abstract specification for a counter function.
    You can use the [xtriple] tactic to turn the [triple] goal into a form
    on which [xpull] can be invoked to extract facts from the precondition. *)

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

(** As a warm-up before presenting the specifications of higher-order iterators
    such as [iter] and [fold] over mutable lists, we present the specification
    of an higher-order operator named [repeat]. A call to [repeat f n] executes
    [n] successives calls to [f] on the unit value, that is, calls to [f()].

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
    [repeat n f] is expressed in terms of an invariant, named [I],
    describing the state in-between every two calls to [f]. Initially, we
    assume the state to satisfy [f 0]. We assume that, for every index [i]
    in the range from [0] (inclusive) to [n] (exclusive), a call [f()] takes
    the state from one satisfying [f i] to one satisfying [f (i+1)]. The
    specification below asserts that, under these assumptions, after the [n]
    calls to [f()], the final state satisfies [f n].

    The specification takes the form:

    n >= 0 ->
    Hypothesis_on_f ->
    triple (repeat f n)
      (I 0)
      (fun u => I n).

    where the hypothesis of [f] captures the following specification:

    0 <= i < n ->
    triple (f ())
      (I i)
      (fun u => I (i+1))

    The complete specification of [repeat n f] appears below. *)

Lemma triple_repeat : forall (I:int->hprop) (f:val) (n:int),
  n >= 0 ->
  (forall i, 0 <= i < n ->
    triple (f ())
      (I i)
      (fun u => I (i+1))) ->
  triple (repeat f n)
    (I 0)
    (fun u => I n).

(** To establish that specification, we carry out a proof by induction over the
    judgment:

    triple (repeat f m)
      (I (n-m))
      (fun u => I n)).

    which asserts that, when there remains [m] calls to perform, the current
    state is described by [I (n-m)], that is, the current index [i] is equal
    to [n-m]. *)

Proof using.
  introv Hn Hf.
  cuts G: (forall m, 0 <= m <= n ->
    triple (repeat f m)
      (I (n-m))
      (fun u => I n)).
  { applys_eq G. { fequals. math. } { math. } }
  intros m. induction_wf IH: (downto 0) m. intros Hm.
  xwp. xapp. xif; intros C.
  { xapp. { math. } xapp. xapp. { math. } { math. }
    math_rewrite ((n - m) + 1 = n - (m - 1)). xsimpl. }
  { xval. math_rewrite (n - m = n). xsimpl. }
Qed.

(* ================================================================= *)
(** ** Specification of an Iterator on Mutable Lists *)

(** The operation [miter] takes as argument a function [f] and a pointer [p]
    on a mutable list, and invokes [f] on each of the items stored in that
    list.

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
    function [repeat] from the previous section, with two main differences.
    The first difference is that the invariant is expressed not in terms of
    an index [i] ranging from [0] to [n], but in terms of a prefix of the
    list [L] being traversed, ranging from [nil] to the full list [L].
    The second difference is that the operation [miter f p] requires in its
    precondition, in addition to [I nil], the description of the mutable list
    [MList L p]. This predicate is returned in the postcondition, unchanged,
    reflecting on the fact that the iteration does not alter the list. *)

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
    tactic [xapp (triple_iter (fun K => ...))]. *)

(* ================================================================= *)
(** ** Computing the Length of a Mutable List using an Iterator *)

(** We can compute the length of a mutable list by iterating over that list a
    function that increments a reference cell once for every item.

OCaml:

    let mlength_using_miter p =
      let c = ref 0 in
      miter (fun x -> incr c) p;
      !c
*)

(** **** Exercise: 4 stars, standard, especially useful (triple_mlength_using_miter)

    Prove the correctness of [mlength_using_iter].
    Hint: use [xfun. intros f Hf] for reasoning about the function definition,
    then use [xapp] for reasoning about a call to [f] by inlining its code. *)

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

(** The following program was proposed in the original article on
    Separation Logic by John Reynolds as a challenge for verification.

    This function, called [cps_append], is similar to the function [append]
    presented previously: it also performs in-place concatenation of two lists.
    It differs in that it is implemented using a recursive, continuation-passing
    style function to perform the work.

    The presentation of [cps_append p1 p2] is also slightly different: this
    operation returns a pointer [p3] that describes the head of the result
    of the concatenation, and it works even if [p1] corresponds to an empty
    list.

    The code of [cps_append] involves an auxiliary function [cps_append_aux].
    This code appears at first like a puzzle: it takes a good drawing and
    several minutes to figure out how it works. Observe in particular how the
    recursive call is invoked as part of the continuation. *)

(**

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

(** The main function [cps_append] simply invokes [cps_append_aux]
    with a trivial continuation. *)

Lemma triple_cps_append : forall (L1 L2:list val) (p1 p2:loc),
  triple (cps_append p1 p2)
    (MList L1 p1 \* MList L2 p2)
    (funloc p3 => MList (L1++L2) p3).
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

(** This concludes the formal verification of Reynolds' verification
    challenge. *)

(* ================================================================= *)
(** ** Historical Notes *)

(** The representation predicate for lists appears in the seminal papers on
    Separation Logic: the notes by Reynolds from the summer 1999, updated the
    next summer [Reynolds 2000] (in Bib.v), and the publication by
    [O’Hearn, Reynolds, and Yang 2001] (in Bib.v).

    Most presentations of Separation Logic target partial correctness, whereas
    this chapters targets total correctness. The specifications of recursive
    functions are established using the built-in induction mechanism offered by
    Coq.

    The specification of higher-order iterators requires higher-order
    Separation Logic. Being embedded in the higher-order logic of Coq, the
    Separation Logic that we work with is inherently higher-order. Further
    information on the history of higher-order Separation Logic for
    higher-order programs may be found in section 10.2 of
    http://www.chargueraud.org/research/2020/seq_seplogic/seq_seplogic.pdf . *)

(* 2021-05-12 01:22 *)
