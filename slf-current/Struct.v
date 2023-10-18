(** * Struct: Arrays and Records *)

Set Implicit Arguments.
From SLF Require Import LibSepReference LibSepTLCbuffer.
#[global]
Hint Rewrite conseq_cons' : rew_listx.

Implicit Types P : Prop.
Implicit Types H : hprop.
Implicit Types Q : val->hprop.
Implicit Type p q : loc.
Implicit Type k : nat.
Implicit Type i n : int.
Implicit Type v : val.
Implicit Type L : list val.
Implicit Types z : nat.

(* ################################################################# *)
(** * First Pass *)

(** This chapter introduces support for reasoning about arrays and records.

    In the first part of this chapter, we present the representation predicates
    for these structures, and present the statement of the specifications
    associated with operations on arrays and records.

    In the second part of this chapter, we show how these specifications can
    be realized, with respect to a memory model that exposes a representation
    of headers for allocated blocks. More precisely, we show how to implement
    array and record operations using a pointer arithmetic primitive operation,
    and we establish the correctness of the specifications with respect to
    the semantics of the allocation, deallocation, and pointer arithmetic
    operations.

    The memory model that we consider is somewhat artificial, in the sense that
    it does not perfectly match the memory model of an existing language----it
    lies somewhere between the memory model of C and that of OCaml.
    Nevertheless, this memory model has the benefits of its simplicity, and it
    suffices to illustrate formal proofs involving block headers and pointer
    arithmetics. *)

(* ================================================================= *)
(** ** Representation of a Set of Consecutive Cells *)

(** The cells from an array of length [k] can be represented as a range of [k]
    consecutive cells, starting at some location [p]. In other words, the
    array cells have addresses from [p] inclusive to [p+k] exclusive.

    The heap predicate [hcells L p] represents a consecutive set of cells
    starting at location [p] and whose elements are described by the list [L].
    The length of the list [L] corresponds to the length of the array.

    On paper, we could write something along the lines of:
    [\bigstar_{x at index i in L} { (p+i) ~~> x }].

    In Coq, we define the predicate [hcells L p] by recursion on the list [L],
    with the pointer [p] incremented by one unit at each cell, as follows. *)

Fixpoint hcells (L:list val) (p:loc) : hprop :=
  match L with
  | nil => \[]
  | x::L' => (p ~~> x) \* (hcells L' (p+1)%nat)
  end.

(** The description of a set of consecutive cells can be split in two
    parts, at an arbitrary index. Concretely, if we have
    [hcells (L1++L2) p], then we can separate the left part
    [hcells L1 p] from the right part [hcells L2 q], where the address
    [q] is equal to [p + length L1]. Reciprocally, the two parts can
    be merged back into the original form at any time. *)

Parameter hcells_concat_eq : forall p L1 L2,
  hcells (L1++L2) p = (hcells L1 p \* hcells L2 (length L1 + p)%nat).

(** This "splitting lemma for arrays" is useful for carrying out local
    reasoning on arrays. For example, in the recursive quicksort algorithm,
    the specification requires a description of the segment to be sorted;
    the representation of this segment is split so that subsegments
    can be provided for reasoning about the recursive calls. One thereby
    obtains for free the fact that the cells outside of the targeted
    segment remain unmodified. *)

(* ================================================================= *)
(** ** Representation of an Array with a Block Header *)

(** An array consists of a "header", and of the description of its cells.
    The header is a heap predicate that describes the length of the array.

    - In OCaml, the header consists of a physical memory cell at the
      head of the array. This cell may be queried to obtain the length
      of the array.
    - In C, the header is a logical notion. It describes the length of
      the allocated block, and it used in Separation Logic to specify
      the behavior of the deallocation function, which can only be called
      on the address of an allocated block, deallocating the full block
      at once.

   In this course, we follow the OCaml view, with physical headers.

   The predicate [hheader k p] asserts the existence of an allocated
   block at location [p], such that the contents of the block is made
   of [k] cells, not counting the header cell. For the moment, we leave
   its definition abstract. *)

Parameter hheader : forall (k:nat) (p:loc), hprop.

(** The heap predicate [hheader k p] should capture the information that [p]
    is not null. Indeed blocks cannot be allocated at the null location. *)

Parameter hheader_not_null : forall p k,
  hheader k p ==> hheader k p \* \[p <> null].

(** An array is described by the predicate [harray L p], where the list
    [L] describes the contents of the cells. This heap predicate covers
    both the header, which describes a block of length equal to [length L],
    and the contents of the cells, described by [hcells L (p+1)].

    Note that [p+1] corresponds to the address of the first cell of the array,
    located immediately past the header cell that sits at location [p]. *)

Definition harray (L:list val) (p:loc) : hprop :=
  hheader (length L) p \* hcells L (p+1)%nat.

(* ================================================================= *)
(** ** Specification of Allocation *)

(** The primitive operation [val_alloc k] allocates a block made of
    [k] consecutive cells. *)

Parameter val_alloc : prim.

(** The operation [val_alloc k] is specified as producing an array
    whose cells contain the special "uninitialized value", written
    [val_uninit]. The assume [val_uninit] to be part of the grammar
    of values.

    Check val_uninit : val.
*)

(** More precisely, the postcondition of [val_alloc k] is of the form
   [funloc p => harray L p], where the list [L] is defined as the
   repetition of [k] times the value [val_uninit]. This list is written
   [LibList.make k val_uninit]. *)

Parameter triple_alloc_nat : forall k,
  triple (val_alloc k)
    \[]
    (funloc p => harray (LibList.make k val_uninit) p).

(** In practice, the operation [val_alloc] is applied to a non-negative
    integer, which might not necessarily be syntactically a natural number.
    Hence, the following lemma, which specifies [val_alloc n] for [n >= 0],
    is more handy to use. *)

Parameter triple_alloc : forall n,
  n >= 0 ->
  triple (val_alloc n)
    \[]
    (funloc p => harray (LibList.make (abs n) val_uninit) p).

(** The specification above turns out to be often unnecessarily precise.
    For most applications, it is sufficient for the postcondition to
    describe the array as [harray L p] for some unspecified list [L]
    of length [n]. This weaker specification is stated and proved next. *)

Parameter triple_alloc_array : forall n,
  n >= 0 ->
  triple (val_alloc n)
    \[]
    (funloc p => \exists L, \[n = length L] \* harray L p).

(** Remark: in OCaml, one must provide an initialization value explicitly,
    so there is no such thing as [val_uninit]; in JavaScript, [val_uninit]
    is called [undefined]; in Java, arrays are initialized with zeros;
    in C, uninitialized data should not be read. In that language, one would
    typically implement this policy by restricting the evaluation rule for
    the read operation, adding a premise of the form [v <> val_uninit] to
    ensure that uninitialized values cannot be read. *)

(* ================================================================= *)
(** ** Specification of the Deallocation *)

(** The deallocation operation [val_dealloc p] deallocates the block
    allocated at location [p]. *)

Parameter val_dealloc : prim.

(** The specification of [val_dealloc p] features a precondition that
    requires an array of the form [harray L p], and an empty postcondition. *)

Parameter triple_dealloc : forall L p,
  triple (val_dealloc p)
    (harray L p)
    (fun _ => \[]).

(** Observe that the [harray L p] predicate includes a header of the form
    [hheader k p], ensuring that a block can be deallocated only once. *)

(* ================================================================= *)
(** ** Specification of Array Operations *)

(** The operation [val_array_get p i] returns the contents of the [i]-th
    cell of the array at location [p]. *)

Parameter val_array_get : val.

(** The specification of [val_array_get] is as follows. The precondition
    describes the array in the form [harray L p], with a premise that
    requires the index [i] to be in the valid range, that is, between
    zero (inclusive) and the length of [L] (exclusive). The postcondition
    asserts that the result value is [nth (abs i) L], and mentions
    the unmodified array, still described by [harray L p]. *)

Parameter triple_array_get : forall L p i,
  0 <= i < length L ->
  triple (val_array_get p i)
    (harray L p)
    (fun r => \[r = LibList.nth (abs i) L] \* harray L p).

(** The operation [val_array_set p i v] updates the contents of the [i]-th
    cell of the array at location [p]. *)

Parameter val_array_set : val.

(** The specification of [val_array_set] admits the same precondition as
    [val_array_get], with [harray L p] and the constraint [0 <= i < length L].
    Its postcondition describes the updated array using a predicate of the
    form [harray L' p], where [L'] corresponds to [update (abs i) v L]. *)

Parameter triple_array_set : forall L p i v,
  0 <= i < length L ->
  triple (val_array_set p i v)
    (harray L p)
    (fun _ => harray (LibList.update (abs i) v L) p).

(** The operation [val_array_length p] returns the length of the array
    allocated at location [p]. *)

Parameter val_array_length : val.

(** There are two useful specifications for [val_array_length]. The first
    one operates with the heap predicate [harray L p]. The return value is
    the length of the list [L]. *)

Parameter triple_array_length : forall L p,
  triple (val_array_length p)
    (harray L p)
    (fun r => \[r = length L] \* harray L p).

(** The second specification for [val_array_length] operates only on the
    header of the array. This small-footprint specification is useful to
    read the length of an array whose cells are described by separated
    segments, that is, after [hcells_concat_eq] has been exploited. *)

Parameter triple_array_length_header : forall k p,
  triple (val_array_length p)
    (hheader k p)
    (fun r => \[r = (k:int)] \* hheader k p).

#[global] Hint Resolve triple_array_get triple_array_set triple_array_length : triple.

(* ================================================================= *)
(** ** Representation of Individual Records Fields *)

(** A record can be represented just like an array, with the field names
    corresponding to offsets in that array.

    We let [field] denote the type of field names, an alias for [nat]. *)

Definition field : Type := nat.

(** For example, consider a mutable list cell allocated at location [p].
    It is represented in memory as:

    - a header at location [p], storing the number of fields, that is,
      the value [2];
    - a cell at location [p+1], storing the contents of the head field,
    - a cell at location [p+2], storing the contents of the tail field.

    Concretely, the record can be represented by the heap predicate:
    [(hheader 2 p) \* ((p+1) ~~> x) \* ((p+2) ~~> q)]. *)

(** To avoid exposing pointer arithmetic to the end-user, we introduce
    the "record field" notation [p`.k ~~> v] to denote [(p+1+k) ~~> v].

    For example, with the definition of the field offsets [head := 0]
    and [tail := 1], the same record as before can be represented as:
    [(hheader 2 p) \* (p`.head ~~> x) \* (p`.tail ~~> q)]. *)

Definition hfield (p:loc) (k:field) (v:val) : hprop :=
  (p+1+k)%nat ~~> v.

Notation "p `. k '~~>' v" := (hfield p k v)
  (at level 32, k at level 0, no associativity,
   format "p `. k  '~~>'  v").

(* ================================================================= *)
(** ** Representation of Records *)

(** Describing, e.g., a list cell record in the form
    [(hheader 2 p) \* (p`.head ~~> x) \* (p`.tail ~~> q)]
    in particularly verbose and cumbersome to manipulate.

    To improve the situation, we next introduce generic representation
    predicate for records that allows to describe the same list cell
    much more concisely, as [p ~~~>`{ head := x; tail := q }].

    It what follows, we show how to implement this notation by introducing
    the heap predicates [hfields] and [hrecords]. We then represent the
    specifications of record operations with respect to those predicates. *)

(** A record field is described as the pair of a field and a value
    stored in this field. *)

Definition hrecord_field : Type := (field * val).

(** A record consists of a list of fields. *)

Definition hrecord_fields : Type := list hrecord_field.

(** We let the meta-variable [kvs] denote such lists. *)

Implicit Types kvs : hrecord_fields.

(** A list cell with head field [x] and tail field [q] is represented
    by the list [(head,x)::(tail,q)::nil]. To support the syntax
    [`{ head := x; tail := q }], we introduce the following notation. *)

Notation "`{ k1 := v1 }" :=
  ((k1,(v1:val))::nil)
  (at level 0, k1 at level 0, only parsing).

Notation "`{ k1 := v1 ; k2 := v2 }" :=
  ((k1,(v1:val))::(k2,(v2:val))::nil)
  (at level 0, k1, k2 at level 0, only parsing).

Notation "`{ k1 := v1 ; k2 := v2 ; k3 := v3 }" :=
  ((k1,(v1:val))::(k2,(v2:val))::(k3,(v3:val))::nil)
  (at level 0, k1, k2, k3 at level 0, only parsing).

Notation "`{ k1 := v1 }" :=
  ((k1,v1)::nil)
  (at level 0, k1 at level 0, only printing).

Notation "`{ k1 := v1 ; k2 := v2 }" :=
  ((k1,v1)::(k2,v2)::nil)
  (at level 0, k1, k2 at level 0, only printing).

Notation "`{ k1 := v1 ; k2 := v2 ; k3 := v3 }" :=
  ((k1,v1)::(k2,v2)::(k3,v3)::nil)
  (at level 0, k1, k2, k3 at level 0, only printing).

Open Scope val_scope.

(** The heap predicate [hfields kvs p] asserts that, at location [p],
    one finds the representation of the fields described by the list [kvs].

    The predicate [hfields kvs p] is defined recursively on the list [kvs].
    If [kvs] is empty, the predicate describes the empty heap predicate.
    Otherwise, it describes a first field, at offset [k] and with contents
    [v], as the predicate [p`.k ~~> v], and it describes the remaining
    fields recursively. *)

Fixpoint hfields (kvs:hrecord_fields) (p:loc) : hprop :=
  match kvs with
  | nil => \[]
  | (k,v)::kvs' => (p`.k ~~> v) \* (hfields kvs' p)
  end.

(** The heap predicate [hrecord kvs p] describes a record: it covers
    not just all the fields of the record, but also the header.

    The cells are described by [hfields kvs p], and the header is
    described by [hheader z p], where [nb] should be such that the
    keys in the list [kvs] are between [0] inclusive and [nb] exclusive.

    A permissive definition of [hrecord kvs p] would allow the fields
    from the list [kvs] to be permuted arbitrarily. Yet, to avoid
    complications related to permutations, we make in this course the
    simplifying assumptions that fields are always listed in the order
    of their associated offsets.

    The auxiliary predicate [maps_all_fields z kvs] asserts that the
    keys from the association list [kvs] correspond exactly to the sequence
    made of the first [nb] natural numbers, that is, [0; 1; ...; nb-1]. *)

Definition maps_all_fields (nb:nat) (kvs:hrecord_fields) : Prop :=
  LibList.map fst kvs = nat_seq 0 nb.

(** The predicate [hrecord kvs p] exploits [maps_all_fields z kvs]
    to relate the value [nb] stored in the header with the association
    list [kvs] that describes the contents of the fields. *)

Definition hrecord (kvs:hrecord_fields) (p:loc) : hprop :=
  \exists z, hheader z p \* hfields kvs p \* \[maps_all_fields z kvs].

(** The heap predicate [hrecord kvs p] captures in particular the
    invariant that the location [p] is not null. *)

Lemma hrecord_not_null : forall p kvs,
  hrecord kvs p ==> hrecord kvs p \* \[p <> null].
Proof using.
  intros. unfold hrecord. xpull. intros z M.
  xchanges* hheader_not_null.
Qed.

(** We introduce the notation [p ~~~> kvs] for [hrecord kvs p],
    allowing to write, e.g., [p ~~~>`{ head := x; tail := q }]. *)

Notation "p '~~~>' kvs" := (hrecord kvs p)
  (at level 32).

(* ================================================================= *)
(** ** Example with Mutable Linked Lists *)

(** Recall the definition of the representation predicate [MList],
    which was introduced in [Basic]. *)

Definition head : field := 0%nat.
Definition tail : field := 1%nat.

Fixpoint MList (L:list val) (p:loc) : hprop :=
  match L with
  | nil => \[p = null]
  | x::L' => \exists q, (p ~~~>`{ head := x; tail := q}) \* (MList L' q)
  end.

(** Recall the statement of the lemma [MList_if], which reformulates
    the definition of [MList] with a case analysis on [p = null].

    Observe the use of the lemma [hrecrod_not_null] to exploit the
    fact that a record cannot be allocated at the [null] location. *)

Lemma MList_if : forall (p:loc) (L:list val),
      (MList L p)
  ==> (If p = null
        then \[L = nil]
        else \exists x q L', \[L = x::L']
             \* (p ~~~> `{ head := x ; tail := q }) \* (MList L' q)).
Proof using.
  intros. destruct L as [|x L']; simpl.
  { xpull. intros M. case_if. xsimpl*. }
  { xpull. intros q. xchange hrecord_not_null. intros N.
    case_if. xsimpl*. }
Qed.

Global Opaque MList.

(* ================================================================= *)
(** ** Reading in Record Fields *)

Declare Scope trm_scope_ext.

(** The read operation is described by an expression of the form
    [val_get_field k p], where [k] denotes a field name, and where [p]
    denotes the location of a record. Technically, [val_get_field k]
    is a value, and this value is applied to the pointer [p]. Hence,
    [val_get_field] has type [field -> val]. *)

Parameter val_get_field : field -> val.

(** The read operation [val_get_field k p] is abbreviated as [p`.k]. *)

Notation "t1 '`.' k" :=
  (val_get_field k t1)
  (in custom trm at level 56, k at level 0, format "t1 '`.' k" )
  : trm_scope_ext.

(** The operation [val_get_field k p] can be specified at three levels.

    First, its small-footprint specification operates at the level of
    a single field, described by [p`.k ~~> v]. The specification is
    very similar to that of [val_get]. The return value is exactly [v]. *)

Parameter triple_get_field : forall p k v,
  triple (val_get_field k p)
    (p`.k ~~> v)
    (fun r => \[r = v] \* (p`.k ~~> v)).

(** Second, this operation can be specified with respect to a list of
    fields, described in the form [hfields kvs p]. To that end, we introduce
    a function called [hfields_lookup] for extracting the value [v]
    associated with a field [k] in a list of record fields [kvs].

    The operation [hfields_lookup k kvs] returns a result of type [option val],
    because we cannot presume that the field [k] occurs in [kvs], even though
    it is always the case in practice. *)

Fixpoint hfields_lookup (k:field) (kvs:hrecord_fields) : option val :=
  match kvs with
  | nil => None
  | (ki,vi)::kvs' => if Nat.eq_dec k ki
                       then Some vi
                       else hfields_lookup k kvs'
  end.

(** Under the assumption that [hfields_lookup k kvs] returns [Some v],
    the read operation [val_get_field k p] is specified to return [v].
    The corresponding specification appears below. *)

Parameter triple_get_field_hfields : forall kvs p k v,
  hfields_lookup k kvs = Some v ->
  triple (val_get_field k p)
    (hfields kvs p)
    (fun r => \[r = v] \* hfields kvs p).

(** Third and last, the read operation can be specified with respect
    to the predicate [hrecord kvs p], describing the full record, including
    its header. The specification is similar to the previous one. *)

Parameter triple_get_field_hrecord : forall kvs p k v,
  hfields_lookup k kvs = Some v ->
  triple (val_get_field k p)
    (hrecord kvs p)
    (fun r => \[r = v] \* hrecord kvs p).

(* ================================================================= *)
(** ** Writing in Record Fields *)

(** The write operation is described by an expression of the form
    [val_set_field k p v], where [k] denotes a field name, and where [p]
    denotes the location of a record, and [v] is the new value for the field. *)

Parameter val_set_field : field -> val.

(** The write operation [val_get_field k p v] is abbreviated as
    [Set p`.k ':= v]. *)

Notation "t1 '`.' k ':=' t2" :=
  (val_set_field k t1 t2)
  (in custom trm at level 56, k at level 0, format "t1 '`.' k  ':=' t2")
  : trm_scope_ext.

(** Like for the read operation, the write operation can be specified at three
    levels. First, at the level of an individual field. *)

Parameter triple_set_field : forall v p k v',
  triple (val_set_field k p v)
    (p`.k ~~> v')
    (fun _ => p`.k ~~> v).

(** Then, at the level of [hfields] and [hrecord]. To that end, we
    introduce an auxiliary function called [hrecord_update] for computing
    the updated list of fields following an write operation.
    Concretely, [hrecord_update k w kvs] replaces the contents of the field
    named [k] with the value [w]. It returns some description [kvs'] of the
    record fields, provided the update operation succeeded, i.e., provided that
    the field [k] on which the update is to be performed actually occurs in the
    list [kvs]. *)

Fixpoint hfields_update (k:field) (v:val) (kvs:hrecord_fields)
                        : option hrecord_fields :=
  match kvs with
  | nil => None
  | (ki,vi)::kvs' => if Nat.eq_dec k ki
                       then Some ((k,v)::kvs')
                       else match hfields_update k v kvs' with
                            | None => None
                            | Some LR => Some ((ki,vi)::LR)
                            end
  end.

(** The specification in terms of [hfields] is as follows. *)

Parameter triple_set_field_hfields : forall kvs kvs' k p v,
  hfields_update k v kvs = Some kvs' ->
  triple (val_set_field k p v)
    (hfields kvs p)
    (fun _ => hfields kvs' p).

(** The specification in terms of [hrecord] is similar. *)

Parameter triple_set_field_hrecord : forall kvs kvs' k p v,
  hfields_update k v kvs = Some kvs' ->
  triple (val_set_field k p v)
    (hrecord kvs p)
    (fun _ => hrecord kvs' p).

(* ================================================================= *)
(** ** Allocation of Records *)

(** Because records are internally described like arrays, records may
    be allocated and deallocated using the operations [val_alloc] and
    [val_dealloc], just like for arrays. That said, it is useful to
    express derived specifications for these two operations stated in
    terms of representation predicate [hrecord], which describes a
    full record in terms of the list of its fields. *)

(** For allocation, one needs to provide, at some point, the fields names
    for the record being allocated. These fields names may be described
    by a list of field names of type [list field].

    This list, written [ks], should be equivalent to a list of
    consecutive natural numbers [0 :: 1 :: ... :: n-1], where [n]
    denotes the number of fields. The interest of introducing the list
    [ks] is to provide readable names in place of numbers.

    The operation [val_alloc_hrecord ks] is implemented by invoking
    [val_alloc] on the length of [ks]. *)

Definition val_alloc_hrecord (ks:list field) : trm :=
  val_alloc (length ks).

(** The specification of [val_alloc_hrecord ks] involves an empty
    precondition and a postcondition of the form [hrecord kvs p],
    where the list [kvs] maps the fields names from [ks] to the
    value [val_uninit]. The premise expressed in terms of [nat_seq]
    ensures that the list [ks] contains consecutive offsets starting
    from zero.

    In the statement below, [LibListExec.length] is a variant of
    [LibList.length] that computes in Coq (using [simpl] or [reflexivity]).
    Likewise for [LibListExec.map], which is equivalent to [LibList.map]. *)

Parameter triple_alloc_hrecord : forall ks,
  ks = nat_seq 0 (LibListExec.length ks) ->
  triple (val_alloc_hrecord ks)
    \[]
    (funloc p => hrecord (LibListExec.map (fun k => (k,val_uninit)) ks) p).

#[global] Hint Resolve triple_alloc_hrecord : triple.

(** For example, the allocation of a list cell is specified as follows. *)

Lemma triple_alloc_mcons :
  triple (val_alloc_hrecord (head::tail::nil))
    \[]
    (funloc p => p ~~~> `{ head := val_uninit ; tail := val_uninit }).
Proof using. applys* triple_alloc_hrecord. Qed.

(* ================================================================= *)
(** ** Deallocation of Records *)

(** Deallocation of a record, written [val_dealloc_hrecord p], is
    implemented as [val_dealloc p]. *)

Definition val_dealloc_hrecord : val :=
  val_dealloc.

(** The specification of this operation simply requires as precondition
    the full record description, in the form [hrecord kvs p], and yields
    the empty postcondition. *)

Parameter triple_dealloc_hrecord : forall kvs p,
  triple (val_dealloc_hrecord p)
    (hrecord kvs p)
    (fun _ => \[]).

#[global] Hint Resolve triple_dealloc_hrecord : triple.

(** To improve readability, we introduce the notation [Delete p]
    for record deallocation. *)

Notation "'delete'" :=
  (trm_val val_dealloc_hrecord)
  (in custom trm at level 0) : trm_scope_ext.

(** For example, the following corollary to [triple_dealloc_hrecord] may be
    used to reason about the deallocation of a list cell. *)

Lemma triple_dealloc_mcons : forall p x q,
  triple (val_dealloc_hrecord p)
    (p ~~~> `{ head := x ; tail := q })
    (fun _ => \[]).
Proof using. intros. applys* triple_dealloc_hrecord. Qed.

(* ================================================================= *)
(** ** Combined Record Allocation and Initialization *)

(** It is often useful to allocate a record and immediately initialize
    its fields. To that end, we introduce the operation [val_new_hrecord],
    which applies to a list of fields and to values for these fields.

    This operation can be defined in an arity-generic way, yet, to avoid
    technicalities, we only present its specialization for arity 2. *)

Module RecordInit.
Import ProgramSyntax.
Open Scope trm_scope_ext.

(** In the definition below, the expression in braces
    [val_alloc_hrecord (k1::k2::nil)] refers to a Coq term,
    embedded in the syntax of program terms. *)

Definition val_new_hrecord_2 (k1:field) (k2:field) : val :=
  <{ fun 'x1 'x2 =>
       let 'p = {val_alloc_hrecord (k1::k2::nil)} in
       'p`.k1 := 'x1;
       'p`.k2 := 'x2;
       'p }>.

(** To improve readability, we introduce notation to allow writing, e.g.,
    [`{ head := x; tail := q }] for the allocation and initialization
    of a list cell. *)

Notation "`{ k1 := v1 ; k2 := v2 }" :=
  (val_new_hrecord_2 k1 k2 v1 v2)
  (in custom trm at level 65,
   k1, k2 at level 0,
   v1, v2 at level 65) : trm_scope_ext.

(** This operation is specified as follows. *)

Lemma triple_new_hrecord_2 : forall k1 k2 v1 v2,
  k1 = 0%nat ->
  k2 = 1%nat ->
  triple <{ `{ k1 := v1; k2 := v2 } }>
    \[]
    (funloc p => p ~~~> `{ k1 := v1 ; k2 := v2 }).
Proof using.
  introv -> ->. xwp. xapp triple_alloc_hrecord. { auto. } intros p. simpl.
  xapp triple_set_field_hrecord. { reflexivity. }
  xapp triple_set_field_hrecord. { reflexivity. }
  xval. xsimpl*.
Qed.

(** For example, the operation [mcons x q] allocates a list cell with
    head value [x] and tail pointer [q]. *)

Definition mcons : val :=
  val_new_hrecord_2 head tail.

Lemma triple_mcons : forall (x q:val),
  triple (mcons x q)
    \[]
    (funloc p => p ~~~> `{ head := x ; tail := q }).
Proof using. intros. applys* triple_new_hrecord_2. Qed.

End RecordInit.

(* ################################################################# *)
(** * More Details *)

(* ================================================================= *)
(** ** Extending [xapp] to Support Record Access Operations *)

(** The tactic [xapp] can be refined to automatically invoke the
    lemmas [triple_get_field_hrecord] and [triple_set_field_hrecord],
    which involve preconditions of the form
    [hfields_lookup k kvs = Some v] and
    [hfields_update k v kvs = Some ks'], respectively.

    The auxiliary lemmas reformulate the specification triples in
    weakest-precondition form. The premise takes the form
    [H ==> \exists kvs, (hrecord kvs p) \* match ... with Some .. => ..].

    This presentation enables using [xsimpl] to extract the description
    of the record, named [kvs], before evaluating the [lookup] or
    [update] function for producing the suitable postcondition. *)

Lemma xapp_get_field_lemma : forall H k p Q,
  H ==> \exists kvs, (hrecord kvs p) \*
     match hfields_lookup k kvs with
     | None => \[False]
     | Some v => ((fun r => \[r = v] \* hrecord kvs p) \--* protect Q) end ->
  H ==> wp (val_get_field k p) Q.
Proof using.
  introv N. xchange N. intros kvs. cases (hfields_lookup k kvs).
  { rewrite wp_equiv. applys* triple_conseq_frame triple_get_field_hrecord.
    xsimpl. intros r ->. xchange (qwand_specialize v). rewrite* hwand_hpure_l. }
  { xpull. }
Qed.

Lemma xapp_set_field_lemma : forall H k p v Q,
  H ==> \exists kvs, (hrecord kvs p) \*
     match hfields_update k v kvs with
     | None => \[False]
     | Some kvs' => ((fun _ => hrecord kvs' p) \--* protect Q) end ->
  H ==> wp (val_set_field k p v) Q.
Proof using.
  introv N. xchange N. intros kvs. cases (hfields_update k v kvs).
  { rewrite wp_equiv. applys* triple_conseq_frame triple_set_field_hrecord.
    xsimpl. intros r. xchange (qwand_specialize r). }
  { xpull. }
Qed.

Ltac xapp_nosubst_for_records tt ::=
  first [ applys xapp_set_field_lemma; xsimpl; simpl; xapp_simpl
        | applys xapp_get_field_lemma; xsimpl; simpl; xapp_simpl ].

(* ================================================================= *)
(** ** Deallocation Function for Lists *)

(** Recall that our Separation Logic set up enforces that all allocated
    data eventually gets properly deallocated. In what follows, we present
    a function for recursively deallocating an entire mutable list. *)

Module ListDealloc.
Import ProgramSyntax RecordInit.
Open Scope trm_scope_ext.

(** The operation [mfree_list] deallocates all the cells in a given list.
    It is implemented as a recursive function that invokes [mfree_cell]
    on every cell that it traverses.

OCaml:

    let rec mfree_list p =
      if p != null then begin
        let q = p.tail in
        delete p;
        mfree_list q
      end
*)

Definition mfree_list : val :=
  <{ fix 'f 'p =>
       let 'b = ('p <> null) in
       if 'b then
         let 'q = 'p`.tail in
         delete 'p;
         'f 'q
       end }>.

(** The precondition of [mfree_list p] requires a full list [MList L p].
    The postcondition is empty: the entire list is destroyed. *)

(** **** Exercise: 3 stars, standard, especially useful (Triple_mfree_list)

    Verify the function [mfree_list].
    Hint: the overall pattern of the proof follows that used for the
    function [triple_mcopy], from chapter [Repr]. *)

Lemma triple_mfree_list : forall L p,
  triple (mfree_list p)
    (MList L p)
    (fun _ => \[]).
Proof using. (* FILL IN HERE *) Admitted.

(** [] *)

End ListDealloc.


(* ################################################################# *)
(** * Optional Material *)

(** The aim of this bonus section is to show how to establish
    the specifications presented in this chapter.

    To that end, we consider an extended language, featuring the
    operations [val_alloc] and [val_dealloc], which operates on
    blocks of cells. *)

Module Realization.

(* ================================================================= *)
(** ** Refined Source Language *)

(** We assume that every allocated block features a "header cell",
    represented explicitly in the memory state.

    To describe this header cell, we introduce a special value,
    written [val_header k], where [k] denotes the length of the block
    that follows the header. *)

Parameter val_header : nat -> val.

(** Note that values of the form [val_header k] should never be
    introduced by source terms. They are only introduced in heaps
    by the evaluation of [val_alloc], and they should never leak
    in program terms. *)

(** The operation [val_alloc k] is specified as shown below. Starting from
    a state [sa], it produces a state [sb \u sa] (i.e., the union of [sb]
    and [sa]), where [sb] consists of consecutive of [k+1] consecutive
    cells. The head cell stores the special value [val_header k], while
    the [k] following cells store the special value [val_uninit], describing
    uninitialized cells. *)

Parameter eval_alloc : forall k n sa sb p,
  sb = Fmap.conseq (val_header k :: LibList.make k val_uninit) p ->
  n = nat_to_Z k ->
  p <> null ->
  Fmap.disjoint sa sb ->
  eval sa (val_alloc (val_int n)) (sb \u sa) (val_loc p).

(** The operation [val_dealloc p] is specified as shown below. Assume
    a state of the form [sb \u sa], where [sb] consists of consecutive of
    [k+1] consecutive cells. Assume the first of these cells to store the
    special value [val_header k]. Then, the deallocation operation removes
    the block described by [sb], and leaves the state [sa]. *)

Parameter eval_dealloc : forall k vs sa sb p,
  sb = Fmap.conseq (val_header k :: vs) p ->
  k = LibList.length vs ->
  Fmap.disjoint sa sb ->
  eval (sb \u sa) (val_dealloc (val_loc p)) sa val_unit.

(** Rather than extending the language with primitive operations
    for reading and writing in array cells and record fields,
    we simply include a pointer arithmetic operation, named
    [val_ptr_add], and use it to encode all other access operations. *)

Parameter val_ptr_add : prim.

(** The operation [val_ptr p n] applies to a pointer [p] and an integer [n],
    and returns the address [p+n]. *)

Parameter eval_ptr_add : forall p1 p2 n s,
  (p2:int) = p1 + n ->
  eval s (val_ptr_add (val_loc p1) (val_int n)) s (val_loc p2).

(** Note that the specification above allows the integer [n] to be negative,
    as long as [p+n] is nonnegative. That said, thereafter we only apply
    [eval_ptr_add] to nonnegative arguments. *)

(** We also introduce the primitive operation [val_length p], which returns
    the number stored in the header block at address [p]. This operation is
    useful to implement the function [val_array_length], which reads the
    length of an array. *)

Parameter val_length : prim.

Parameter eval_length : forall s p k,
  Fmap.indom s p ->
  (val_header k) = Fmap.read s p ->
  eval s (val_length (val_loc p)) s (val_int k).

(* ================================================================= *)
(** ** Realization of [hheader] *)

(** The heap predicate [hheader k p] describes a cell at location
    whose contents is the special value [val_header k], and with
    the invariant that [p] is not null.

    [hheader k p] is defined as [p ~~> (val_header k) \* \[p <> null]]. *)

Parameter hheader_def :
  hheader = (fun (k:nat) (p:loc) => p ~~> (val_header k) \* \[p <> null]).

(** Like other heap predicates, the definition of [hheader] is associated
    with an introduction and an elimination lemma. *)

Lemma hheader_intro : forall p k,
  p <> null ->
  (hheader k p) (Fmap.single p (val_header k)).
Proof using.
  introv N. rewrite hheader_def. rewrite hstar_hpure_r.
  split*. applys hsingle_intro.
Qed.

Lemma hheader_inv: forall h p k,
  (hheader k p) h ->
  h = Fmap.single p (val_header k) /\ p <> null.
Proof using.
  introv E. rewrite hheader_def in E. rewrite hstar_hpure_r in E.
  split*.
Qed.

(** The heap predicate [hheader k p] captures the invariant [p <> null]. *)

Lemma hheader_not_null : forall p k,
  hheader k p ==> hheader k p \* \[p <> null].
Proof using. intros. rewrite hheader_def. xsimpl*. Qed.

(** The definition of [hheader] is meant to show that one can prove all
    the specifications axiomatized so far. Note, however, that this
    definition should not be revealed to the end user. In other words,
    it should be made "strongly opaque". (Technically, this could be
    achieved by means of a functor in Coq.)

    Otherwise, the user could exploit the [val_set] operation to update
    the contents of a header field, replacing [p ~~> (val_header k)]
    with [p ~~> v] for another value [v], thereby compromising the
    invariants of the memory model. *)

(* ================================================================= *)
(** ** Introduction and Elimination Lemmas for [hcells] and [harray] *)

(** The heap predicates [hcells] and [harray] have their introduction
    and elimination lemmas stated as follows. These lemmas are useful
    for establishing the specifications of the allocation and of the
    deallocation operations. *)

Lemma hcells_intro : forall L p,
  (hcells L p) (Fmap.conseq L p).
Proof using.
  intros L. induction L as [|L']; intros; rew_listx.
  { applys hempty_intro. }
  { simpl. applys hstar_intro.
    { applys* hsingle_intro. }
    { applys IHL. }
    { applys Fmap.disjoint_single_conseq. left. math. } }
Qed.

Lemma hcells_inv : forall p L h,
  hcells L p h ->
  h = Fmap.conseq L p.
Proof using.
  introv N. gen p h. induction L as [|x L'];
   intros; rew_listx; simpls.
  { applys hempty_inv N. }
  { lets (h1&h2&N1&N2&N3&->): hstar_inv N. fequal.
    { applys hsingle_inv N1. }
    { applys IHL' N2. } }
Qed.

Lemma harray_intro : forall k p L,
  k = length L ->
  p <> null ->
  (harray L p) (Fmap.conseq (val_header k :: L) p).
Proof using.
  introv E n. unfold harray. rew_listx. applys hstar_intro.
  { subst k. applys* hheader_intro. }
  { applys hcells_intro. }
  { applys disjoint_single_conseq. left. math. }
Qed.

Lemma harray_inv : forall p L h,
  (harray L p) h ->
  h = (Fmap.conseq (val_header (length L) :: L) p) /\ p <> null.
Proof using.
  introv N. unfolds harray. rew_listx.
  lets (h1&h2&N1&N2&N3&->): hstar_inv (rm N).
  lets (N4&Np): hheader_inv (rm N1).
  lets N2': hcells_inv (rm N2). subst*.
Qed.

(* ================================================================= *)
(** ** Proving the Specification of Allocation and Deallocation *)

(** Following the usual pattern, we first establish a reasoning rule
    for allocation at the level of Hoare logic. *)

Lemma hoare_alloc_nat : forall H k,
  hoare (val_alloc k)
    H
    (funloc p => harray (LibList.make k val_uninit) p \* H).
Proof using.
  intros. intros h Hh. sets L: (LibList.make k val_uninit).
  sets L': (val_header k :: L).
  forwards~ (p&Dp&Np): (Fmap.conseq_fresh null h L').
  exists ((Fmap.conseq L' p) \u h) (val_loc p). split.
  { applys~ (@eval_alloc k). }
  { applys hexists_intro p. rewrite hstar_hpure_l. split*.
    { applys* hstar_intro. applys* harray_intro.
      subst L. rew_listx*. } }
Qed.

(** We then derive the Separation Logic reasoning rule. *)

Lemma triple_alloc_nat : forall k,
  triple (val_alloc k)
    \[]
    (funloc p => harray (LibList.make k val_uninit) p).
Proof using.
  intros. intros H'. applys hoare_conseq.
  { applys hoare_alloc_nat H'. } { xsimpl. } { xsimpl*. }
Qed.

(** The two corollaries to [triple_alloc_nat] follow. The first one
    applies to an integer argument, as opposed to a natural number. *)

Lemma triple_alloc : forall n,
  n >= 0 ->
  triple (val_alloc n)
    \[]
    (funloc p => harray (LibList.make (abs n) val_uninit) p).
Proof using.
  introv N. rewrite <- (@abs_nonneg n) at 1; [|auto].
  xapp triple_alloc_nat. xsimpl*.
Qed.

(** The second corollary weakens the postcondition by not specifying
    the contents of the allocated cells. *)

Lemma triple_alloc_array : forall n,
  n >= 0 ->
  triple (val_alloc n)
    \[]
    (funloc p => \exists L, \[n = length L] \* harray L p).
Proof using.
  introv N. xapp triple_alloc. { auto. }
  { xpull. intros p. xsimpl*. { rewrite length_make. rewrite* abs_nonneg. } }
Qed.

(** We also establish the specification of deallocation, first w.r.t.
    Hoare triples, then w.r.t. Separation Logic triples. *)

Lemma hoare_dealloc : forall H L p,
  hoare (val_dealloc p)
    (harray L p \* H)
    (fun _ => H).
Proof using.
  intros. intros h Hh. destruct Hh as (h1&h2&N1&N2&N3&N4). subst h.
  exists h2 val_unit. split; [|auto].
  applys* eval_dealloc L. applys harray_inv N1.
Qed.

Lemma triple_dealloc : forall L p,
  triple (val_dealloc p)
    (harray L p)
    (fun _ => \[]).
Proof using.
  intros. intros H'. applys hoare_conseq.
  { applys hoare_dealloc H'. } { xsimpl. } { xsimpl. }
Qed.

(* ================================================================= *)
(** ** Splitting Lemmas for [hcells] *)

(** The description of the cells of an array can be split in pieces,
    allowing to describe only portions of the array. *)

Lemma hcells_nil_eq : forall p,
  hcells nil p = \[].
Proof using. auto. Qed.

Lemma hcells_cons_eq : forall p x L,
  hcells (x::L) p = (p ~~> x) \* hcells L (p+1)%nat.
Proof using. intros. simpl. xsimpl*. Qed.

Lemma hcells_one_eq : forall p x L,
  hcells (x::nil) p = (p ~~> x).
Proof using. intros. rewrite hcells_cons_eq, hcells_nil_eq. xsimpl. Qed.

Lemma hcells_concat_eq : forall p L1 L2,
  hcells (L1++L2) p = (hcells L1 p \* hcells L2 (length L1 + p)%nat).
Proof using.
  intros. gen p. induction L1; intros; rew_list; simpl.
  { xsimpl. }
  { rewrite IHL1. math_rewrite (length L1 + (p + 1) = S (length L1 + p))%nat.
    xsimpl. }
Qed.

(** In order to reason about the read or write operation on a specific
    cell, we need to isolate this cell from the other cells of the array.
    Then, after the operation, we need to fold back to the view on the
    entire array.

    The isolation process is captured in a general way by the following
    "focus lemma". It reads as follows. Assume [hcells L p] to initially
    describe a segment of an array. Then, the [k]-th cell from this segment
    can be isolated as a predicate [(p+k) ~~> v], where [v] denotes the
    [k]-th item of [L], that is [LibList.nth k L].

    What remains of the heap can be described using the magic wand operator
    as [((p+k) ~~> v) \-* (hcells L p)], which captures the idea that when
    providing back the cell at location [p+k], one regains the ownership of
    the original segment. *)

(** The following statement describes a focus lemma. *)

Parameter hcells_focus_read : forall k p v L,
  k < length L ->
  v = LibList.nth k L ->
  hcells L p ==>
       ((p+k)%nat ~~> v)
    \* ((p+k)%nat ~~> v \-* hcells L p).

(** The above lemma is, however, limited to read operations. Indeed, it imposes
    the cell [(p+k) ~~> v] to be merged back into the array segment, without
    modification to the original contents [v].

    The lemma can be generalized into a form that takes into account the
    possibility of folding back the array segment with a modified contents
    for the cell at [p+k], described by [(p+k) ~~> w], for any value [w].
    The updated segment gets described as [update k w L]. *)

Lemma hcells_focus : forall k p L,
  k < length L ->
  hcells L p ==>
       ((p+k)%nat ~~> LibList.nth k L)
    \* (\forall w, ((p+k)%nat ~~> w) \-* hcells (LibList.update k w L) p).
Proof using.
  introv E. gen k p. induction L as [|x L']; rew_list; intros.
  { false. math. }
  { simpl. rewrite nth_cons_case. case_if.
    { subst. math_rewrite (p + 0 = p)%nat. xsimpl. intros w.
      rewrite update_zero. rewrite hcells_cons_eq. xsimpl. }
    { forwards R: IHL' (k-1)%nat (p+1)%nat. { math. }
      math_rewrite ((p+1)+(k-1) = p+k)%nat in R. xchange (rm R).
      xsimpl. intros w. xchange (hforall_specialize w).
      rewrite update_cons_pos; [|math]. rewrite hcells_cons_eq. xsimpl. } }
Qed.

(** The above focus lemma immediately extends to a full array described
    in the form [harray L p]. *)

Lemma harray_focus : forall k p L,
  k < length L ->
  harray L p ==>
       ((p+1+k)%nat ~~> LibList.nth k L)
    \* (\forall w, ((p+1+k)%nat ~~> w) \-* harray (LibList.update k w L) p).
Proof using.
  introv E. unfolds harray. xchanges (>> hcells_focus E). intros w.
  xchange (hforall_specialize w). xsimpl. rewrite* length_update.
Qed.

(* ================================================================= *)
(** ** Specification of Pointer Arithmetic *)

(** The operation [val_ptr_add p n] adds an integer [n] to the
    address [p]. This operation is used for encoding array and
    record operations by accessing cells at specific offsets.

    The specification of [val_ptr_add] directly reformulates the
    evaluation rule. It is established following the usual pattern
    for primitive operations. *)

Lemma hoare_ptr_add : forall p n H,
  p + n >= 0 ->
  hoare (val_ptr_add p n)
    H
    (fun r => \[r = val_loc (abs (p + n))] \* H).
Proof using.
  introv N. intros s K0. exists s (val_loc (abs (p + n))). split.
  { applys eval_ptr_add. rewrite abs_nonneg; math. }
  { rewrite* hstar_hpure_l. }
Qed.

Lemma triple_ptr_add : forall p n,
  p + n >= 0 ->
  triple (val_ptr_add p n)
    \[]
    (fun r => \[r = val_loc (abs (p + n))]).
Proof using.
  introv N. unfold triple. intros H'.
  applys* hoare_conseq hoare_ptr_add; xsimpl*.
Qed.

(** The following lemma specializes the specification for the case
    where the argument [n] is equal to a natural number [k]. This
    reformulation avoids the [abs] function, and is more practical for
    the encodings that we consider further in the subsequent sections. *)

Lemma triple_ptr_add_nat : forall p k,
  triple (val_ptr_add p k)
    \[]
    (fun r => \[r = val_loc (p+k)%nat]).
Proof using.
  intros. applys triple_conseq triple_ptr_add. { math. } { xsimpl. }
  { xsimpl. intros. subst. fequals.
    applys eq_nat_of_eq_int. rewrite abs_nonneg; math. }
Qed.

(* ================================================================= *)
(** ** Specification of the [length] Operation to Read the Header *)

(** To establish [triple_length], we follow the same proof pattern
    as for [triple_get]. *)

Lemma eval_length_sep : forall s s2 p k,
  s = Fmap.union (Fmap.single p (val_header k)) s2 ->
  eval s (val_length (val_loc p)) s (val_int k).
Proof using.
  introv ->. forwards Dv: Fmap.indom_single p (val_header k).
  applys eval_length.
  { applys~ Fmap.indom_union_l. }
  { rewrite~ Fmap.read_union_l. rewrite~ Fmap.read_single. }
Qed.

Lemma hoare_length : forall H k p,
  hoare (val_length p)
    ((hheader k p) \* H)
    (fun r => \[r = val_int k] \* (hheader k p) \* H).
Proof using.
  intros. intros s K0. exists s (val_int k). split.
  { destruct K0 as (s1&s2&P1&P2&D&U). lets (E1&N): hheader_inv P1.
    subst s1. applys eval_length_sep U. }
  { rewrite~ hstar_hpure_l. }
Qed.

Lemma triple_length : forall k p,
  triple (val_length p)
    (hheader k p)
    (fun r => \[r = val_int k] \* hheader k p).
Proof using.
  intros. unfold triple. intros H'. applys hoare_conseq hoare_length; xsimpl~.
Qed.

#[global] Hint Resolve triple_length : triple.

(* ================================================================= *)
(** ** Encoding of Array Operations using Pointer Arithmetic *)

(** An access to the [i]-th cell of an array at location [p] can be encoded
    as an access to the cell at location [p+i+1]. *)

Module Export ArrayAccessDef.
Import ProgramSyntax.
Open Scope wp_scope.

(** Let's first state and prove two auxiliary arithmetic lemmas that
    are needed in the proofs below. *)

Lemma abs_lt_inbound : forall i k,
  0 <= i < nat_to_Z k ->
  (abs i < k).
Proof using.
  introv N. apply lt_nat_of_lt_int. rewrite abs_nonneg; math.
Qed.

Lemma succ_int_plus_abs : forall p i,
  i >= 0 ->
  ((p + 1 + abs i) = abs (nat_to_Z p + (i + 1)))%nat.
Proof using.
  introv N. rewrite abs_nat_plus_nonneg; [|math].
  math_rewrite (i+1 = 1 + i).
  rewrite <- succ_abs_eq_abs_one_plus; math.
Qed.

(** The length operation on an array, written [val_array_length p],
    is encoded as [val_length p], where [val_length] is the
    primitive operation for reading the contents of a header. *)

Definition val_array_length : val := val_length.

Lemma triple_array_length_header : forall k p,
  triple (val_array_length p)
    (hheader k p)
    (fun r => \[r = k] \* hheader k p).
Proof using. intros. applys triple_length. Qed.

Lemma triple_array_length : forall L p,
  triple (val_array_length p)
    (harray L p)
    (fun r => \[r = length L] \* harray L p).
Proof using.
  intros. unfold harray. applys triple_conseq_frame triple_length.
  { xsimpl. } { xsimpl. auto. }
Qed.

(** The get operation on an array, written [val_array_get p i],
    is encoded as [val_get (p+i+1)]. *)

Definition val_array_get : val :=
  <{ fun 'p 'i =>
       let 'j = 'i + 1 in
       let 'n = val_ptr_add 'p 'j in
       val_get 'n }>.

Lemma triple_array_get : forall p i v L,
  0 <= i < length L ->
  LibList.nth (abs i) L = v ->
  triple (val_array_get p i)
    (harray L p)
    (fun r => \[r = v] \* harray L p).
Proof using.
  introv N E. xwp. xapp. xapp triple_ptr_add. { math. }
  xchange (@harray_focus (abs i) p L).
  { rew_listx. applys* abs_lt_inbound. }
  sets w: (LibList.nth (abs i) L). rewrite succ_int_plus_abs; [|math].
  xapp triple_get. xchange (hforall_specialize w). subst w.
  rewrite update_nth_same. rewrite <- E. xsimpl*.
  { rew_listx. applys* abs_lt_inbound. }
Qed.

(** The set operation on an array, written [val_array_set p i v],
    is encoded as [val_set (p+i+1) v]. *)

Definition val_array_set : val :=
  <{ fun 'p 'i 'v =>
       let 'j = 'i + 1 in
       let 'n = val_ptr_add 'p 'j in
       val_set 'n 'v }>.

Lemma triple_array_set : forall p i v L,
  0 <= i < length L ->
  triple (val_array_set p i v)
    (harray L p)
    (fun _ => harray (LibList.update (abs i) v L) p).
Proof using.
  introv R. xwp. xpull. xapp. xapp triple_ptr_add. { math. }
  xchange (@harray_focus (abs i) p L). { applys* abs_lt_inbound. }
  rewrite succ_int_plus_abs; [|math].
  xapp triple_set. auto. xchange (hforall_specialize v).
Qed.

End ArrayAccessDef.

(* ================================================================= *)
(** ** Encoding of Record Operations using Pointer Arithmetic *)

(** An access to the [k]-th field of a record at location [p] can be
    encoded as an access to the cell at location [p+k+1]. *)

Module Export FieldAccessDef.
Import ProgramSyntax.

(** The get operation on a field, written [p`.k],
    is encoded as [val_get (p+k+1)]. *)

Definition val_get_field (k:field) : val :=
  <{ fun 'p =>
       let 'q = val_ptr_add 'p {nat_to_Z (k+1)} in
       val_get 'q }>.

Notation "t1 '`.' f" :=
  (val_get_field f t1)
  (in custom trm at level 56, f at level 0, format "t1 '`.' f" ).

Lemma triple_get_field : forall p k v,
  triple ((val_get_field k) p)
    (p`.k ~~> v)
    (fun r => \[r = v] \* (p`.k ~~> v)).
Proof using.
  xwp. xapp triple_ptr_add_nat. unfold hfield.
  math_rewrite (p+1+k = p+(k+1))%nat.
  xapp triple_get. xsimpl*.
Qed.

(** The set operation on a field, written [Set p`.k := v],
    is encoded as [val_set (p+k+1) v]. *)

Definition val_set_field (k:field) : val :=
  <{ fun 'p 'v =>
       let 'q = val_ptr_add 'p {nat_to_Z (k+1)} in
       val_set 'q 'v }>.

Lemma triple_set_field : forall v1 p k v2,
  triple ((val_set_field k) p v2)
    (p`.k ~~> v1)
    (fun _ => p`.k ~~> v2).
Proof using.
  intros. xwp. xapp triple_ptr_add_nat. unfold hfield.
  math_rewrite (p+1+k = p+(k+1))%nat.
  xapp triple_set. xsimpl*.
Qed.

Notation "t1 '`.' f ':=' t2" :=
  (val_set_field f t1 t2)
  (in custom trm at level 56, f at level 0, format "t1 '`.' f  ':='  t2").

End FieldAccessDef.

(* ================================================================= *)
(** ** Specification of Record Operations w.r.t. [hfields] and [hrecord] *)

(** The specifications [triple_get_field] and [triple_set_field]
    established above correspond to small-footprint specifications,
    with preconditions mentioning a single field. Corollaries to these
    specifications can be established with preconditions mentioning a
    list of fields (predicate [hfields]), or a full record (predicate
    [hrecord]). *)

(** Get operation on a list of fields *)

Lemma triple_get_field_hfields : forall kvs p k v,
  hfields_lookup k kvs = Some v ->
  triple (val_get_field k p)
    (hfields kvs p)
    (fun r => \[r = v] \* hfields kvs p).
Proof using.
  intros L. induction L as [| [ki vi] L']; simpl; introv E.
  { inverts E. }
  { case_if.
    { inverts E. subst ki. applys triple_conseq_frame.
      { applys triple_get_field. } { xsimpl. } { xsimpl*. } }
    { applys triple_conseq_frame.
      { applys IHL' E. }
      { xsimpl. }
      { xsimpl*. } } }
Qed.

(** Get operation on a record *)

Lemma triple_get_field_hrecord : forall kvs p k v,
  hfields_lookup k kvs = Some v ->
  triple (val_get_field k p)
    (p ~~~> kvs)
    (fun r => \[r = v] \* p ~~~> kvs).
Proof using.
  introv M. unfold hrecord. xtriple. xpull. intros z Hz.
  xapp (>> triple_get_field_hfields M). xsimpl*.
Qed.

(** Set operation on a list of fields *)

Lemma triple_set_field_hfields : forall kvs kvs' k p v,
  hfields_update k v kvs = Some kvs' ->
  triple (val_set_field k p v)
    (hfields kvs p)
    (fun _ => hfields kvs' p).
Proof using.
  intros kvs. induction kvs as [| [ki vi] kvs']; simpl; introv E.
  { inverts E. }
  { case_if.
    { inverts E. subst ki. applys triple_conseq_frame.
      { applys triple_set_field. } { xsimpl. } { xsimpl*. } }
    { cases (hfields_update k v kvs') as C2; tryfalse. inverts E.
      applys triple_conseq_frame. { applys IHkvs' C2. }
      { xsimpl. } { simpl. xsimpl*. } } }
Qed.

(** Auxiliary lemma about [hfields_update], showing that the update
    operation preserves the names of the fields. *)

Lemma hfields_update_preserves_fields : forall kvs kvs' k v,
  hfields_update k v kvs = Some kvs' ->
  LibList.map fst kvs' = LibList.map fst kvs.
Proof using.
  intros kvs. induction kvs as [|[ki vi] kvs1]; simpl; introv E.
  { introv _ H. inverts H. }
  { case_if.
    { inverts E. rew_listx*. subst. fequals. }
    { cases (hfields_update k v kvs1).
      { inverts E. rew_listx. fequals*. }
      { inverts E. } } }
Qed.

Lemma hfields_update_preserves_maps_all_fields : forall kvs kvs' z k v,
  hfields_update k v kvs = Some kvs' ->
  maps_all_fields z kvs = maps_all_fields z kvs'.
Proof using.
  introv M. unfold maps_all_fields. extens.
  rewrites* (>> hfields_update_preserves_fields M).
Qed.

(** Set operation on a record *)

Lemma triple_set_field_hrecord : forall kvs kvs' k p v,
  hfields_update k v kvs = Some kvs' ->
  triple (val_set_field k p v)
    (p ~~~> kvs)
    (fun _ => p ~~~> kvs').
Proof using.
  introv M. unfold hrecord. xtriple. xpull. intros z Hz.
  xapp (>> triple_set_field_hfields M). xsimpl.
  rewrites* <- (>> hfields_update_preserves_maps_all_fields z M).
Qed.

(* ================================================================= *)
(** ** Specification of Record Allocation and Deallocation *)

(** Recall that record allocation, written [val_alloc_hrecord ks],
    is encoded as [val_alloc (length ks)], and that record deallocation,
    written [val_dealloc_hrecord p], is encoded as [val_dealloc p].

    The operations [val_alloc] and [val_dealloc] have already been
    specified, via lemmas [triple_alloc] and [triple_dealloc].

    In this section, we show that the specifications for [val_alloc_hrecord]
    and [val_dealloc_hrecord] can be derived from those.

    The proofs are not completely trivial because we need to convert
    between the view of a list of consecutive cells, as captured by
    the predicate [hcells], and the view of a list of fields, as captured
    by the predicate [hfields].

    To that end, the lemma [hfields_eq_hcells] asserts the equality
    between [hfields kvs p] and [hcells L (p+1)] under a suitable relation
    between the list of values [L] and the description of the fields [kvs]:
    the values from the association list [kvs] must correspond to the list [L],
    and the keys from the association list [kvs] must correspond to the
    [length L] first natural numbers.

    The proof is carried out by induction, on the following statement. *)

Lemma hfields_eq_hcells_ind : forall L p kvs o,
  LibList.map fst kvs = nat_seq o (length L) ->
  L = LibList.map snd kvs ->
  hfields kvs p = hcells L (p+1+o)%nat.
Proof using.
  intros L. induction L as [|v L']; introv M E; rew_listx in *;
   destruct kvs as [|[k v'] kvs']; tryfalse; rew_listx in *.
  { auto. }
  { simpls. inverts M as M'. inverts E as E'. rew_listx in *.
    unfold hfield. fequals.
    math_rewrite (p+1+o+1=p+1+(o+1))%nat. applys* IHL'.
    math_rewrite* (o+1=S o)%nat. }
Qed.

(** The statement of the lemma [hfields_eq_hcells] involves the predicate
    [maps_all_fields], which appears in the definition of [hrecord]. *)

Lemma hfields_eq_hcells : forall z L p kvs,
  maps_all_fields z kvs ->
  z = length L ->
  L = LibList.map snd kvs ->
  hfields kvs p = hcells L (p+1)%nat.
Proof using.
  introv M HL E. subst z. rewrites (>> hfields_eq_hcells_ind M E).
  fequals. unfold loc. math.
Qed.

(** The following lemma converts from the [harray] view to the [hrecord]
    view, for an array of uninitialized values. *)

Lemma harray_uninit_himpl_hrecord : forall p z,
  harray (LibList.make z val_uninit) p ==>
  hrecord (LibList.map (fun k => (k,val_uninit)) (nat_seq 0 z)) p.
Proof using.
  intros. unfolds hrecord, harray. rew_listx.
  sets kvs: ((LibList.map (fun k => (k,val_uninit)) (nat_seq 0 z))).
  asserts (M1&M2): (LibList.map fst kvs = nat_seq 0 z
                 /\ LibList.map snd kvs = LibList.make z val_uninit).
  { subst kvs. generalize 0%nat as o.
    induction z as [|z']; intros; simpl; rew_listx; simpl.
    { auto. }
    { forwards* (N1&N2): IHz' (S o). split; fequals*. } }
  xsimpl z.
  { applys M1. }
  { rewrites* <- (>> hfields_eq_hcells M1). rew_listx*. }
Qed.

(** Exploiting the above lemma, we derive the specification of record
    allocation. *)

Lemma triple_alloc_hrecord : forall ks,
  ks = nat_seq 0 (LibListExec.length ks) ->
  triple (val_alloc_hrecord ks)
    \[]
    (funloc p => hrecord (LibListExec.map (fun k => (k,val_uninit)) ks) p).
Proof using.
  introv E. xapp triple_alloc_nat. intros p.
  xsimpl p. { auto. } rewrite E. rewrite length_nat_seq.
  rewrite LibListExec.map_eq. xchange harray_uninit_himpl_hrecord.
Qed.

(** The following lemma converts in the other direction, from the [hrecord]
    view to the [harray] view.*)

Lemma hrecord_himpl_harray : forall p kvs,
  hrecord kvs p ==> harray (LibList.map snd kvs) p.
Proof using.
  intros. unfolds hrecord, harray. xpull. intros z M.
  asserts Hz: (z = length kvs).
  { lets E: length_nat_seq 0%nat z. rewrite <- M in E. rew_listx* in *. }
  xchange* (>> hfields_eq_hcells p M). { rew_listx*. }
  xsimpl. rew_listx. rewrite* Hz.
Qed.

(** Exploiting the above lemma, we derive the specification of record
    deallocation. *)

Lemma triple_dealloc_hrecord : forall kvs p,
  triple (val_dealloc p)
    (hrecord kvs p)
    (fun _ => \[]).
Proof using.
  intros. xtriple. xchange hrecord_himpl_harray.
  xapp triple_dealloc. xsimpl.
Qed.

End Realization.

(* 2023-10-18 23:05 *)
