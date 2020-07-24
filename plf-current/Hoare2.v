(** * Hoare2: Hoare Logic, Part II *)

Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Strings.String.
From PLF Require Import Maps.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import omega.Omega.
From PLF Require Import Hoare.
From PLF Require Import Imp.

(* ################################################################# *)
(** * Decorated Programs *)

(** The beauty of Hoare Logic is that it is _compositional_: the
    structure of proofs exactly follows the structure of programs.

    This suggests that we can record the essential ideas of a
    proof (informally, and leaving out some low-level calculational
    details) by "decorating" a program with appropriate assertions on
    each of its commands.

    Such a _decorated program_ carries within it an argument for its
    own correctness. *)

(** For example, consider the program: 

    X ::= m;;
    Z ::= p;
    WHILE ~(X = 0) DO
      Z ::= Z - 1;;
      X ::= X - 1
    END

   (Note the _parameters_ [m] and [p], which stand for
   fixed-but-arbitrary numbers.  Formally, they are simply Coq
   variables of type [nat].)
*)
(** Here is one possible specification for this program:

      {{ True }}
    X ::= m;;
    Z ::= p;
    WHILE ~(X = 0) DO
      Z ::= Z - 1;;
      X ::= X - 1
    END
      {{ Z = p - m }}
*)
(** Here is a decorated version of the program, embodying a
    proof of this specification: 

      {{ True }} ->>
      {{ m = m }}
    X ::= m;;
      {{ X = m }} ->>
      {{ X = m /\ p = p }}
    Z ::= p;
      {{ X = m /\ Z = p }} ->>
      {{ Z - X = p - m }}
    WHILE ~(X = 0) DO
        {{ Z - X = p - m /\ X <> 0 }} ->>
        {{ (Z - 1) - (X - 1) = p - m }}
      Z ::= Z - 1;;
        {{ Z - (X - 1) = p - m }}
      X ::= X - 1
        {{ Z - X = p - m }}
    END
      {{ Z - X = p - m /\ ~ (X <> 0) }} ->> 
      {{ Z = p - m }}
*)

(** Concretely, a decorated program consists of the program text
    interleaved with assertions (either a single assertion or possibly
    two assertions separated by an implication). *)

(** To check that a decorated program represents a valid proof, we
    check that each individual command is _locally consistent_ with
    its nearby assertions in the following sense: *)

(** - [SKIP] is locally consistent if its precondition and
      postcondition are the same:

          {{ P }} SKIP {{ P }}
*)

(** - The sequential composition of [c1] and [c2] is locally
      consistent (with respect to assertions [P] and [R]) if [c1] is
      locally consistent (with respect to [P] and [Q]) and [c2] is
      locally consistent (with respect to [Q] and [R]):

          {{ P }} c1;; {{ Q }} c2 {{ R }}
*)

(** - An assignment is locally consistent if its precondition is the
      appropriate substitution of its postcondition:

          {{ P [X |-> a] }}
          X ::= a
          {{ P }}
*)

(** - A conditional is locally consistent (with respect to assertions
      [P] and [Q]) if the assertions at the top of its "then" and
      "else" branches are exactly [P /\ b] and [P /\ ~b] and if its
      "then" branch is locally consistent (with respect to [P /\ b]
      and [Q]) and its "else" branch is locally consistent (with
      respect to [P /\ ~b] and [Q]):

          {{ P }}
          TEST b THEN
            {{ P /\ b }}
            c1
            {{ Q }}
          ELSE
            {{ P /\ ~b }}
            c2
            {{ Q }}
          FI
          {{ Q }}
*)

(** - A while loop with precondition [P] is locally consistent if its
      postcondition is [P /\ ~b], if the pre- and postconditions of
      its body are exactly [P /\ b] and [P], and if its body is
      locally consistent:

          {{ P }}
          WHILE b DO
            {{ P /\ b }}
            c1
            {{ P }}
          END
          {{ P /\ ~b }}
*)

(** - A pair of assertions separated by [->>] is locally consistent if
      the first implies the second:

          {{ P }} ->>
          {{ P' }}

      This corresponds to the application of [hoare_consequence], and it
      is the _only_ place in a decorated program where checking whether
      decorations are correct is not fully mechanical and syntactic,
      but rather may involve logical and/or arithmetic reasoning. *)

(** These local consistency conditions essentially describe a
    procedure for _verifying_ the correctness of a given proof. This
    verification involves checking that every single command is
    locally consistent with the accompanying assertions.

    If we are instead interested in _finding_ a proof for a given
    specification, we need to discover the right assertions. This can
    be done in an almost mechanical way, with the exception of finding
    loop invariants. In the remainder of this section we explain in
    detail how to construct decorations for several short programs,
    all of which are loop-free or have simple loop invariants. We
    defer a full discussion of finding loop invariants to the next
    section. *)

(* ================================================================= *)
(** ** Example: Swapping Using Addition and Subtraction *)

(** Here is a program that swaps the values of two variables using
    addition and subtraction (instead of by assigning to a temporary
    variable).

       X ::= X + Y;;
       Y ::= X - Y;;
       X ::= X - Y

    We can prove (informally) using decorations that this program is 
    correct -- i.e., it always swaps the values of variables [X] and [Y].

    (1)     {{ X = m /\ Y = n }} ->>
    (2)     {{ (X + Y) - ((X + Y) - Y) = n /\ (X + Y) - Y = m }}
           X ::= X + Y;;
    (3)     {{ X - (X - Y) = n /\ X - Y = m }}
           Y ::= X - Y;;
    (4)     {{ X - Y = n /\ Y = m }}
           X ::= X - Y
    (5)     {{ X = n /\ Y = m }}

    These decorations can be constructed as follows:
      - We begin with the undecorated program (the unnumbered lines).
      - We add the specification -- i.e., the outer precondition (1)
        and postcondition (5). In the precondition, we use parameters
        [m] and [n] to remember the initial values of variables [X]
        and [Y] so that we can refer to them in the postcondition (5).
      - We work backwards, mechanically, starting from (5) and
        proceeding until we get to (2). At each step, we obtain the
        precondition of the assignment from its postcondition by
        substituting the assigned variable with the right-hand-side of
        the assignment. For instance, we obtain (4) by substituting
        [X] with [X - Y] in (5), and we obtain (3) by substituting [Y]
        with [X - Y] in (4).
      - Finally, we verify that (1) logically implies (2) -- i.e.,
        that the step from (1) to (2) is a valid use of the law of
        consequence. For this we substitute [X] by [m] and [Y] by [n]
        and calculate as follows:

            (m + n) - ((m + n) - n) = n /\ (m + n) - n = m
            (m + n) - m = n /\ m = m
            n = n /\ m = m

    Note that, since we are working with natural numbers rather than
    fixed-width machine integers, we don't need to worry about the
    possibility of arithmetic overflow anywhere in this argument.
    This makes life quite a bit simpler! *)

(* ================================================================= *)
(** ** Example: Simple Conditionals *)

(** Here is a simple decorated program using conditionals:

      (1)     {{True}}
            TEST X <= Y THEN
      (2)       {{True /\ X <= Y}} ->>
      (3)       {{(Y - X) + X = Y \/ (Y - X) + Y = X}}
              Z ::= Y - X
      (4)       {{Z + X = Y \/ Z + Y = X}}
            ELSE
      (5)       {{True /\ ~(X <= Y) }} ->>
      (6)       {{(X - Y) + X = Y \/ (X - Y) + Y = X}}
              Z ::= X - Y
      (7)       {{Z + X = Y \/ Z + Y = X}}
            FI
      (8)     {{Z + X = Y \/ Z + Y = X}}

These decorations were constructed as follows:
  - We start with the outer precondition (1) and postcondition (8).
  - We follow the format dictated by the [hoare_if] rule and copy the
    postcondition (8) to (4) and (7). We conjoin the precondition (1)
    with the guard of the conditional to obtain (2). We conjoin (1)
    with the negated guard of the conditional to obtain (5).
  - In order to use the assignment rule and obtain (3), we substitute
    [Z] by [Y - X] in (4). To obtain (6) we substitute [Z] by [X - Y]
    in (7).
  - Finally, we verify that (2) implies (3) and (5) implies (6). Both
    of these implications crucially depend on the ordering of [X] and
    [Y] obtained from the guard. For instance, knowing that [X <= Y]
    ensures that subtracting [X] from [Y] and then adding back [X]
    produces [Y], as required by the first disjunct of (3). Similarly,
    knowing that [~ (X <= Y)] ensures that subtracting [Y] from [X]
    and then adding back [Y] produces [X], as needed by the second
    disjunct of (6). Note that [n - m + m = n] does _not_ hold for
    arbitrary natural numbers [n] and [m] (for example, [3 - 5 + 5 =
    5]). *)

(** **** Exercise: 2 stars, standard (if_minus_plus_reloaded) 

    Fill in valid decorations for the following program:

       {{ True }}
      TEST X <= Y THEN
          {{                         }} ->>
          {{                         }}
        Z ::= Y - X
          {{                         }}
      ELSE
          {{                         }} ->>
          {{                         }}
        Y ::= X + Z
          {{                         }}
      FI
        {{ Y = X + Z }}
*)

(* Do not modify the following line: *)
Definition manual_grade_for_decorations_in_if_minus_plus_reloaded : option (nat*string) := None.
(** [] *)

(* ================================================================= *)
(** ** Example: Reduce to Zero *)

(** Here is a [WHILE] loop that is so simple it needs no
    invariant (i.e., the invariant [True] will do the job).

        (1)      {{ True }}
               WHILE ~(X = 0) DO
        (2)        {{ True /\ X <> 0 }} ->>
        (3)        {{ True }}
                 X ::= X - 1
        (4)        {{ True }}
               END
        (5)      {{ True /\ ~(X <> 0) }} ->>
        (6)      {{ X = 0 }}

The decorations can be constructed as follows:
  - Start with the outer precondition (1) and postcondition (6).
  - Following the format dictated by the [hoare_while] rule, we copy
    (1) to (4). We conjoin (1) with the guard to obtain (2). The guard
    is a Boolean expression [~(X = 0)], which for simplicity we
    express in assertion (2) as [X <> 0]. We also conjoin (1) with the
    negation of the guard to obtain (5). Note that, because the outer
    postcondition (6) does not syntactically match (5), we need a
    trivial use of the consequence rule from (5) to (6).
  - Assertion (3) is the same as (4), because [X] does not appear in
    [4], so the substitution in the assignment rule is trivial.
  - Finally, the implication between (2) and (3) is also trivial. *)

(** From an informal proof in the form of a decorated program, it is
    easy to read off a formal proof using the Coq versions of the
    Hoare rules.  Note that we do _not_ unfold the definition of
    [hoare_triple] anywhere in this proof -- the idea is to use the
    Hoare rules as a self-contained logic for reasoning about
    programs. *)

Definition reduce_to_zero' : com :=
  WHILE ~(X = 0) DO
    X ::= X - 1
  END.

Theorem reduce_to_zero_correct' :
  {{True}}
  reduce_to_zero'
  {{X = 0}}.
Proof.
  unfold reduce_to_zero'.
  (* First we need to transform the postcondition so
     that hoare_while will apply. *)
  eapply hoare_consequence_post.
  apply hoare_while.
  - (* Loop body preserves invariant *)
    (* Need to massage precondition before [hoare_asgn] applies *)
    eapply hoare_consequence_pre. apply hoare_asgn.
    (* Proving trivial implication (2) ->> (3) *)
    intros st [HT Hbp]. unfold assn_sub. constructor.
  - (* Invariant and negated guard imply postcondition *)
    intros st [Inv GuardFalse].
    unfold bassn in GuardFalse. simpl in GuardFalse.
    rewrite not_true_iff_false in GuardFalse.
    rewrite negb_false_iff in GuardFalse.
    apply eqb_eq in GuardFalse.
    apply GuardFalse. Qed.

(* ================================================================= *)
(** ** Example: Division *)

(** The following Imp program calculates the integer quotient and
    remainder of two numbers [m] and [n] that are arbitrary constants
    in the program.

       X ::= m;;
       Y ::= 0;;
       WHILE n <= X DO
         X ::= X - n;;
         Y ::= Y + 1
       END;

    In we replace [m] and [n] by concrete numbers and execute the
    program, it will terminate with the variable [X] set to the
    remainder when [m] is divided by [n] and [Y] set to the
    quotient. *)

(** In order to give a specification to this program we need to
    remember that dividing [m] by [n] produces a remainder [X] and a
    quotient [Y] such that [n * Y + X = m /\ X < n].

    It turns out that we get lucky with this program and don't have to
    think very hard about the loop invariant: the invariant is just
    the first conjunct [n * Y + X = m], and we can use this to
    decorate the program.

      (1)    {{ True }} ->>
      (2)    {{ n * 0 + m = m }}
           X ::= m;;
      (3)    {{ n * 0 + X = m }}
           Y ::= 0;;
      (4)    {{ n * Y + X = m }}
           WHILE n <= X DO
      (5)      {{ n * Y + X = m /\ n <= X }} ->>
      (6)      {{ n * (Y + 1) + (X - n) = m }}
             X ::= X - n;;
      (7)      {{ n * (Y + 1) + X = m }}
             Y ::= Y + 1
      (8)      {{ n * Y + X = m }}
           END
      (9)    {{ n * Y + X = m /\ ~ (n <= X) }} ->>
     (10)    {{ n * Y + X = m /\ X < n }}

    Assertions (4), (5), (8), and (9) are derived mechanically from
    the invariant and the loop's guard.  Assertions (8), (7), and (6)
    are derived using the assignment rule going backwards from (8)
    to (6).  Assertions (4), (3), and (2) are again backwards
    applications of the assignment rule.

    Now that we've decorated the program it only remains to check that
    the uses of the consequence rule are correct -- i.e., that (1)
    implies (2), that (5) implies (6), and that (9) implies (10). This
    is indeed the case, so we have a valid decorated program. *)

(* ################################################################# *)
(** * Finding Loop Invariants *)

(** Once the outermost precondition and postcondition are
    chosen, the only creative part in verifying programs using Hoare
    Logic is finding the right loop invariants.  The reason this is
    difficult is the same as the reason that inductive mathematical
    proofs are: strengthening the loop invariant (or the induction
    hypothesis) means that you have a stronger assumption to work with
    when trying to establish the postcondition of the loop body (or
    complete the induction step of the proof), but it also means that
    the loop body's postcondition (or the statement being proved
    inductively) is stronger and thus harder to prove!

    This section explains how to approach the challenge of finding loop
    invariants through a series of examples and exercises. *)

(* ================================================================= *)
(** ** Example: Slow Subtraction *)

(** The following program subtracts the value of [X] from the value of
    [Y] by repeatedly decrementing both [X] and [Y].  We want to verify its
    correctness with respect to the pre- and postconditions shown:

             {{ X = m /\ Y = n }}
           WHILE ~(X = 0) DO
             Y ::= Y - 1;;
             X ::= X - 1
           END
             {{ Y = n - m }}
*)

(** To verify this program, we need to find an invariant [Inv] for the
    loop.  As a first step we can leave [Inv] as an unknown and build a
    _skeleton_ for the proof by applying the rules for local
    consistency (working from the end of the program to the beginning,
    as usual, and without any thinking at all yet). 

    This leads to the following skeleton:

        (1)      {{ X = m /\ Y = n }}  ->>             (a)
        (2)      {{ Inv }}
               WHILE ~(X = 0) DO
        (3)        {{ Inv /\ X <> 0 }}  ->>              (c)
        (4)        {{ Inv [X |-> X-1] [Y |-> Y-1] }}
                 Y ::= Y - 1;;
        (5)        {{ Inv [X |-> X-1] }}
                 X ::= X - 1
        (6)        {{ Inv }}
               END
        (7)      {{ Inv /\ ~ (X <> 0) }}  ->>            (b)
        (8)      {{ Y = n - m }}

    By examining this skeleton, we can see that any valid [Inv] will
    have to respect three conditions:
    - (a) it must be _weak_ enough to be implied by the loop's
      precondition, i.e., (1) must imply (2);
    - (b) it must be _strong_ enough to imply the program's postcondition,
      i.e., (7) must imply (8);
    - (c) it must be _preserved_ by each iteration of the loop (given 
      that the loop guard evaluates to true), i.e., (3) must imply (4). *)

(** These conditions are actually independent of the particular
    program and specification we are considering. Indeed, every loop
    invariant has to satisfy them. One way to find an invariant that
    simultaneously satisfies these three conditions is by using an
    iterative process: start with a "candidate" invariant (e.g., a
    guess or a heuristic choice) and check the three conditions above;
    if any of the checks fails, try to use the information that we get
    from the failure to produce another -- hopefully better -- candidate
    invariant, and repeat.

    For instance, in the reduce-to-zero example above, we saw that,
    for a very simple loop, choosing [True] as an invariant did the
    job.  So let's try instantiating [Inv] with [True] in the skeleton
    above and see what we get...

        (1)      {{ X = m /\ Y = n }} ->>       (a - OK)
        (2)      {{ True }}
               WHILE ~(X = 0) DO
        (3)        {{ True /\ X <> 0 }}  ->>    (c - OK)
        (4)        {{ True }}
                 Y ::= Y - 1;;
        (5)        {{ True }}
                 X ::= X - 1
        (6)        {{ True }}
               END
        (7)      {{ True /\ ~(X <> 0) }}  ->>       (b - WRONG!)
        (8)      {{ Y = n - m }}

    While conditions (a) and (c) are trivially satisfied, condition
    (b) is wrong, i.e., it is not the case that [True /\ X = 0] (7)
    implies [Y = n - m] (8).  In fact, the two assertions are
    completely unrelated, so it is very easy to find a counterexample
    to the implication (say, [Y = X = m = 0] and [n = 1]).

    If we want (b) to hold, we need to strengthen the invariant so
    that it implies the postcondition (8).  One simple way to do
    this is to let the invariant _be_ the postcondition.  So let's
    return to our skeleton, instantiate [Inv] with [Y = n - m], and
    check conditions (a) to (c) again.

    (1)      {{ X = m /\ Y = n }}  ->>          (a - WRONG!)
    (2)      {{ Y = n - m }}
           WHILE ~(X = 0) DO
    (3)        {{ Y = n - m /\ X <> 0 }}  ->>   (c - WRONG!)
    (4)        {{ Y - 1 = n - m }}
             Y ::= Y - 1;;
    (5)        {{ Y = n - m }}
             X ::= X - 1
    (6)        {{ Y = n - m }}
           END
    (7)      {{ Y = n - m /\ ~(X <> 0) }}  ->>      (b - OK)
    (8)      {{ Y = n - m }}

    This time, condition (b) holds trivially, but (a) and (c) are
    broken. Condition (a) requires that (1) [X = m /\ Y = n]
    implies (2) [Y = n - m].  If we substitute [Y] by [n] we have to
    show that [n = n - m] for arbitrary [m] and [n], which is not
    the case (for instance, when [m = n = 1]).  Condition (c) requires
    that [n - m - 1 = n - m], which fails, for instance, for [n = 1]
    and [m = 0]. So, although [Y = n - m] holds at the end of the loop,
    it does not hold from the start, and it doesn't hold on each
    iteration; it is not a correct invariant.

    This failure is not very surprising: the variable [Y] changes
    during the loop, while [m] and [n] are constant, so the assertion
    we chose didn't have much chance of being an invariant!

    To do better, we need to generalize (8) to some statement that is
    equivalent to (8) when [X] is [0], since this will be the case
    when the loop terminates, and that "fills the gap" in some
    appropriate way when [X] is nonzero.  Looking at how the loop
    works, we can observe that [X] and [Y] are decremented together
    until [X] reaches [0].  So, if [X = 2] and [Y = 5] initially,
    after one iteration of the loop we obtain [X = 1] and [Y = 4];
    after two iterations [X = 0] and [Y = 3]; and then the loop stops.
    Notice that the difference between [Y] and [X] stays constant
    between iterations: initially, [Y = n] and [X = m], and the
    difference is always [n - m].  So let's try instantiating [Inv] in
    the skeleton above with [Y - X = n - m].

    (1)      {{ X = m /\ Y = n }}  ->>               (a - OK)
    (2)      {{ Y - X = n - m }}
           WHILE ~(X = 0) DO
    (3)        {{ Y - X = n - m /\ X <> 0 }}  ->>    (c - OK)
    (4)        {{ (Y - 1) - (X - 1) = n - m }}
             Y ::= Y - 1;;
    (5)        {{ Y - (X - 1) = n - m }}
             X ::= X - 1
    (6)        {{ Y - X = n - m }}
           END
    (7)      {{ Y - X = n - m /\ ~(X <> 0) }}  ->>       (b - OK)
    (8)      {{ Y = n - m }}

    Success!  Conditions (a), (b) and (c) all hold now.  (To
    verify (c), we need to check that, under the assumption that [X <>
    0], we have [Y - X = (Y - 1) - (X - 1)]; this holds for all
    natural numbers [X] and [Y].) *)

(* ================================================================= *)
(** ** Exercise: Slow Assignment *)

(** **** Exercise: 2 stars, standard (slow_assignment) 

    A roundabout way of assigning a number currently stored in [X] to
    the variable [Y] is to start [Y] at [0], then decrement [X] until
    it hits [0], incrementing [Y] at each step. Here is a program that
    implements this idea:

        {{ X = m }}
      Y ::= 0;;
      WHILE ~(X = 0) DO
        X ::= X - 1;;
        Y ::= Y + 1
      END
        {{ Y = m }}

    Write an informal decorated program showing that this procedure
    is correct. *)

(* FILL IN HERE *)

(* Do not modify the following line: *)
Definition manual_grade_for_decorations_in_slow_assignment : option (nat*string) := None.
(** [] *)

(* ================================================================= *)
(** ** Exercise: Slow Addition *)

(** **** Exercise: 3 stars, standard, optional (add_slowly_decoration) 

    The following program adds the variable X into the variable Z
    by repeatedly decrementing X and incrementing Z.

      WHILE ~(X = 0) DO
         Z ::= Z + 1;;
         X ::= X - 1
      END

    Following the pattern of the [subtract_slowly] example above, pick
    a precondition and postcondition that give an appropriate
    specification of [add_slowly]; then (informally) decorate the
    program accordingly. *)

(* FILL IN HERE

    [] *)

(* ================================================================= *)
(** ** Example: Parity *)

(** Here is a cute little program for computing the parity of the
    value initially stored in [X] (due to Daniel Cristofani).

         {{ X = m }}
       WHILE 2 <= X DO
         X ::= X - 2
       END
         {{ X = parity m }}

    The mathematical [parity] function used in the specification is
    defined in Coq as follows: *)

Fixpoint parity x :=
  match x with
  | 0 => 0
  | 1 => 1
  | S (S x') => parity x'
  end.

(** The postcondition does not hold at the beginning of the loop,
    since [m = parity m] does not hold for an arbitrary [m], so we
    cannot use that as an invariant.  To find an invariant that works,
    let's think a bit about what this loop does.  On each iteration it
    decrements [X] by [2], which preserves the parity of [X].  So the
    parity of [X] does not change, i.e., it is invariant.  The initial
    value of [X] is [m], so the parity of [X] is always equal to the
    parity of [m]. Using [parity X = parity m] as an invariant we
    obtain the following decorated program:

        {{ X = m }} ->>                               (a - OK)
        {{ parity X = parity m }}
      WHILE 2 <= X DO
          {{ parity X = parity m /\ 2 <= X }}  ->>    (c - OK)
          {{ parity (X-2) = parity m }}
        X ::= X - 2
          {{ parity X = parity m }}
      END
        {{ parity X = parity m /\ ~(2 <= X) }}  ->>       (b - OK)
        {{ X = parity m }}

    With this invariant, conditions (a), (b), and (c) are all
    satisfied. For verifying (b), we observe that, when [X < 2], we
    have [parity X = X] (we can easily see this in the definition of
    [parity]).  For verifying (c), we observe that, when [2 <= X], we
    have [parity X = parity (X-2)]. *)

(** **** Exercise: 3 stars, standard, optional (parity_formal) 

    Translate the above informal decorated program into a formal proof
    in Coq. Your proof should use the Hoare logic rules and should not
    unfold [hoare_triple]. Refer to [reduce_to_zero] for an example.
    You might find the following lemmas to be useful: *)

Lemma parity_ge_2 : forall x,
  2 <= x ->
  parity (x - 2) = parity x.
Proof.
  induction x; intro. reflexivity.
  destruct x. inversion H. inversion H1.
  simpl. rewrite <- minus_n_O. reflexivity.
Qed.

Lemma parity_lt_2 : forall x,
  ~ 2 <= x ->
  parity x = x.
Proof.
  intros. induction x. reflexivity. destruct x. reflexivity.
    exfalso. apply H. omega.
Qed.

Theorem parity_correct : forall (m:nat),
  {{ X = m }}
  WHILE 2 <= X DO
    X ::= X - 2
  END
  {{  X = parity m }}.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ================================================================= *)
(** ** Example: Finding Square Roots *)

(** The following program computes the (integer) square root of [X]
    by naive iteration:

      {{ X=m }}
    Z ::= 0;;
    WHILE (Z+1)*(Z+1) <= X DO
      Z ::= Z+1
    END
      {{ Z*Z<=m /\ m<(Z+1)*(Z+1) }}
*)

(** As above, we can try to use the postcondition as a candidate
    invariant, obtaining the following decorated program:

    (1)  {{ X=m }}  ->>           (a - second conjunct of (2) WRONG!)
    (2)  {{ 0*0 <= m /\ m<(0+1)*(0+1) }}
       Z ::= 0;;
    (3)  {{ Z*Z <= m /\ m<(Z+1)*(Z+1) }}
       WHILE (Z+1)*(Z+1) <= X DO
    (4)    {{ Z*Z<=m /\ (Z+1)*(Z+1)<=X }}  ->>             (c - WRONG!)
    (5)    {{ (Z+1)*(Z+1)<=m /\ m<((Z+1)+1)*((Z+1)+1) }}
         Z ::= Z+1
    (6)    {{ Z*Z<=m /\ m<(Z+1)*(Z+1) }}
       END
    (7)  {{ Z*Z<=m /\ m<(Z+1)*(Z+1) /\ ~((Z+1)*(Z+1)<=X) }}  ->> (b - OK)
    (8)  {{ Z*Z<=m /\ m<(Z+1)*(Z+1) }}

    This didn't work very well: conditions (a) and (c) both failed.
    Looking at condition (c), we see that the second conjunct of (4)
    is almost the same as the first conjunct of (5), except that (4)
    mentions [X] while (5) mentions [m]. But note that [X] is never
    assigned in this program, so we should always have [X=m]; we
    didn't propagate this information from (1) into the loop 
    invariant, but we could!

    Also, we don't need the second conjunct of (8), since we can 
    obtain it from the negation of the guard -- the third conjunct 
    in (7) -- again under the assumption that [X=m].  This allows 
    us to simplify a bit.

    So we now try [X=m /\ Z*Z <= m] as the loop invariant:

      {{ X=m }}  ->>                                      (a - OK)
      {{ X=m /\ 0*0 <= m }}
    Z ::= 0;
      {{ X=m /\ Z*Z <= m }}
    WHILE (Z+1)*(Z+1) <= X DO
        {{ X=m /\ Z*Z<=m /\ (Z+1)*(Z+1)<=X }}  ->>        (c - OK)
        {{ X=m /\ (Z+1)*(Z+1)<=m }}
      Z ::= Z + 1
        {{ X=m /\ Z*Z<=m }}
    END
      {{ X=m /\ Z*Z<=m /\ ~((Z+1)*(Z+1)<=X) }}  ->>           (b - OK)
      {{ Z*Z<=m /\ m<(Z+1)*(Z+1) }}

    This works, since conditions (a), (b), and (c) are now all
    trivially satisfied.

    Very often, if a variable is used in a loop in a read-only
    fashion (i.e., it is referred to by the program or by the
    specification and it is not changed by the loop), it is necessary
    to add the fact that it doesn't change to the loop invariant. *)

(* ================================================================= *)
(** ** Example: Squaring *)

(** Here is a program that squares [X] by repeated addition:

    {{ X = m }}
  Y ::= 0;;
  Z ::= 0;;
  WHILE ~(Y = X)  DO
    Z ::= Z + X;;
    Y ::= Y + 1
  END
    {{ Z = m*m }}
*)

(** The first thing to note is that the loop reads [X] but doesn't
    change its value. As we saw in the previous example, it is a good idea
    in such cases to add [X = m] to the invariant.  The other thing
    that we know is often useful in the invariant is the postcondition,
    so let's add that too, leading to the invariant candidate
    [Z = m * m /\ X = m].

      {{ X = m }} ->>                            (a - WRONG)
      {{ 0 = m*m /\ X = m }}
    Y ::= 0;;
      {{ 0 = m*m /\ X = m }}
    Z ::= 0;;
      {{ Z = m*m /\ X = m }}
    WHILE ~(Y = X) DO
        {{ Z = m*m /\ X = m /\ Y <> X }} ->>     (c - WRONG)
        {{ Z+X = m*m /\ X = m }}
      Z ::= Z + X;;
        {{ Z = m*m /\ X = m }}
      Y ::= Y + 1
        {{ Z = m*m /\ X = m }}
    END
      {{ Z = m*m /\ X = m /\ ~(Y <> X) }} ->>         (b - OK)
      {{ Z = m*m }}

    Conditions (a) and (c) fail because of the [Z = m*m] part.  While
    [Z] starts at [0] and works itself up to [m*m], we can't expect
    [Z] to be [m*m] from the start.  If we look at how [Z] progresses
    in the loop, after the 1st iteration [Z = m], after the 2nd
    iteration [Z = 2*m], and at the end [Z = m*m].  Since the variable
    [Y] tracks how many times we go through the loop, this leads us to
    derive a new invariant candidate: [Z = Y*m /\ X = m].

      {{ X = m }} ->>                               (a - OK)
      {{ 0 = 0*m /\ X = m }}
    Y ::= 0;;
      {{ 0 = Y*m /\ X = m }}
    Z ::= 0;;
      {{ Z = Y*m /\ X = m }}
    WHILE ~(Y = X) DO
        {{ Z = Y*m /\ X = m /\ Y <> X }} ->>        (c - OK)
        {{ Z+X = (Y+1)*m /\ X = m }}
      Z ::= Z + X;
        {{ Z = (Y+1)*m /\ X = m }}
      Y ::= Y + 1
        {{ Z = Y*m /\ X = m }}
    END
      {{ Z = Y*m /\ X = m /\ ~(Y <> X) }} ->>           (b - OK)
      {{ Z = m*m }}

    This new invariant makes the proof go through: all three
    conditions are easy to check.

    It is worth comparing the postcondition [Z = m*m] and the [Z =
    Y*m] conjunct of the invariant. It is often the case that one has
    to replace parameters with variables -- or with expressions 
    involving both variables and parameters, like [m - Y] -- when 
    going from postconditions to invariants. *)

(* ================================================================= *)
(** ** Exercise: Factorial *)

(** **** Exercise: 3 stars, standard (factorial) 

    Recall that [n!] denotes the factorial of [n] (i.e., [n! =
    1*2*...*n]).  Here is an Imp program that calculates the factorial
    of the number initially stored in the variable [X] and puts it in
    the variable [Y]:

    {{ X = m }}
  Y ::= 1 ;;
  WHILE ~(X = 0)
  DO
     Y ::= Y * X ;;
     X ::= X - 1
  END
    {{ Y = m! }}

    Fill in the blanks in following decorated program. For full credit,
    make sure all the arithmetic operations used in the assertions are
    well-defined on natural numbers.

    {{ X = m }} ->>
    {{                                      }}
  Y ::= 1;;
    {{                                      }}
  WHILE ~(X = 0)
  DO   {{                                      }} ->>
       {{                                      }}
     Y ::= Y * X;;
       {{                                      }}
     X ::= X - 1
       {{                                      }}
  END
    {{                                      }} ->>
    {{ Y = m! }}
*)

(* Do not modify the following line: *)
Definition manual_grade_for_decorations_in_factorial : option (nat*string) := None.
(** [] *)

(* ================================================================= *)
(** ** Exercise: Min *)

(** **** Exercise: 3 stars, standard (Min_Hoare)  *)

(** Fill in valid decorations for the following program.
  For the [->>] steps in your annotations, you may rely (silently)
  on the following facts about min

  Lemma lemma1 : forall x y,
    (x<>0 /\ y<>0) -> min x y <> 0.
  Lemma lemma2 : forall x y,
    min (x-1) (y-1) = (min x y) - 1.

  plus standard high-school algebra, as always.

  {{ True }} ->>
  {{                    }}
  X ::= a;;
  {{                       }}
  Y ::= b;;
  {{                       }}
  Z ::= 0;;
  {{                       }}
  WHILE ~(X = 0) && ~(Y = 0) DO
  {{                                     }} ->>
  {{                                }}
  X := X - 1;;
  {{                            }}
  Y := Y - 1;;
  {{                        }}
  Z := Z + 1
  {{                       }}
  END
  {{                            }} ->>
  {{ Z = min a b }}
*)

(* Do not modify the following line: *)
Definition manual_grade_for_decorations_in_Min_Hoare : option (nat*string) := None.
(** [] *)

(** **** Exercise: 3 stars, standard (two_loops) 

    Here is a very inefficient way of adding 3 numbers:

     X ::= 0;;
     Y ::= 0;;
     Z ::= c;;
     WHILE ~(X = a) DO
       X ::= X + 1;;
       Z ::= Z + 1
     END;;
     WHILE ~(Y = b) DO
       Y ::= Y + 1;;
       Z ::= Z + 1
     END

    Show that it does what it should by filling in the blanks in the
    following decorated program.

      {{ True }} ->>
      {{                                        }}
    X ::= 0;;
      {{                                        }}
    Y ::= 0;;
      {{                                        }}
    Z ::= c;;
      {{                                        }}
    WHILE ~(X = a) DO
        {{                                        }} ->>
        {{                                        }}
      X ::= X + 1;;
        {{                                        }}
      Z ::= Z + 1
        {{                                        }}
    END;;
      {{                                        }} ->>
      {{                                        }}
    WHILE ~(Y = b) DO
        {{                                        }} ->>
        {{                                        }}
      Y ::= Y + 1;;
        {{                                        }}
      Z ::= Z + 1
        {{                                        }}
    END
      {{                                        }} ->>
      {{ Z = a + b + c }}
*)

(* Do not modify the following line: *)
Definition manual_grade_for_decorations_in_two_loops : option (nat*string) := None.
(** [] *)

(* ================================================================= *)
(** ** Exercise: Power Series *)

(** **** Exercise: 4 stars, standard, optional (dpow2_down) 

    Here is a program that computes the series:
    [1 + 2 + 2^2 + ... + 2^m = 2^(m+1) - 1]

    X ::= 0;;
    Y ::= 1;;
    Z ::= 1;;
    WHILE ~(X = m) DO
      Z ::= 2 * Z;;
      Y ::= Y + Z;;
      X ::= X + 1
    END

    Write a decorated program for this. *)

(* FILL IN HERE

    [] *)

(* ################################################################# *)
(** * Weakest Preconditions (Optional) *)

(** Some Hoare triples are more interesting than others.
    For example,

      {{ False }}  X ::= Y + 1  {{ X <= 5 }}

    is _not_ very interesting: although it is perfectly valid, it
    tells us nothing useful.  Since the precondition isn't satisfied
    by any state, it doesn't describe any situations where we can use
    the command [X ::= Y + 1] to achieve the postcondition [X <= 5].

    By contrast,

      {{ Y <= 4 /\ Z = 0 }}  X ::= Y + 1 {{ X <= 5 }}

    is useful: it tells us that, if we can somehow create a situation
    in which we know that [Y <= 4 /\ Z = 0], then running this command
    will produce a state satisfying the postcondition.  However, this
    triple is still not as useful as it could be, because the [Z = 0]
    clause in the precondition actually has nothing to do with the
    postcondition [X <= 5].  The _most_ useful triple (for this
    command and postcondition) is this one:

      {{ Y <= 4 }}  X ::= Y + 1  {{ X <= 5 }}

    In other words, [Y <= 4] is the _weakest_ valid precondition of
    the command [X ::= Y + 1] for the postcondition [X <= 5]. *)

(** In general, we say that "[P] is the weakest precondition of
    command [c] for postcondition [Q]" if [{{P}} c {{Q}}] and if,
    whenever [P'] is an assertion such that [{{P'}} c {{Q}}], it is
    the case that [P' st] implies [P st] for all states [st].  *)

Definition is_wp P c Q :=
  {{P}} c {{Q}} /\
  forall P', {{P'}} c {{Q}} -> (P' ->> P).

(** That is, [P] is the weakest precondition of [c] for [Q]
    if (a) [P] _is_ a precondition for [Q] and [c], and (b) [P] is the
    _weakest_ (easiest to satisfy) assertion that guarantees that
    [Q] will hold after executing [c]. *)

(** **** Exercise: 1 star, standard, optional (wp) 

    What are the weakest preconditions of the following commands
   for the following postconditions?

  1) {{ ? }}  SKIP  {{ X = 5 }}

  2) {{ ? }}  X ::= Y + Z {{ X = 5 }}

  3) {{ ? }}  X ::= Y  {{ X = Y }}

  4) {{ ? }}
     TEST X = 0 THEN Y ::= Z + 1 ELSE Y ::= W + 2 FI
     {{ Y = 5 }}

  5) {{ ? }}
     X ::= 5
     {{ X = 0 }}

  6) {{ ? }}
     WHILE true DO X ::= 0 END
     {{ X = 0 }}
*)
(* FILL IN HERE

    [] *)

(** **** Exercise: 3 stars, advanced, optional (is_wp_formal) 

    Prove formally, using the definition of [hoare_triple], that [Y <= 4]
   is indeed the weakest precondition of [X ::= Y + 1] with respect to
   postcondition [X <= 5]. *)

Theorem is_wp_example :
  is_wp (Y <= 4)
    (X ::= Y + 1) (X <= 5).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, advanced, optional (hoare_asgn_weakest) 

    Show that the precondition in the rule [hoare_asgn] is in fact the
    weakest precondition. *)

Theorem hoare_asgn_weakest : forall Q X a,
  is_wp (Q [X |-> a]) (X ::= a) Q.
Proof.
(* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, advanced, optional (hoare_havoc_weakest) 

    Show that your [havoc_pre] rule from the [himp_hoare] exercise
    in the [Hoare] chapter returns the weakest precondition. *)
Module Himp2.
Import Himp.

Lemma hoare_havoc_weakest : forall (P Q : Assertion) (X : string),
  {{ P }} HAVOC X {{ Q }} ->
  P ->> havoc_pre X Q.
Proof.
(* FILL IN HERE *) Admitted.
End Himp2.
(** [] *)

(* ################################################################# *)
(** * Formal Decorated Programs (Advanced) *)

(** Our informal conventions for decorated programs amount to a
    way of displaying Hoare triples, in which commands are annotated
    with enough embedded assertions that checking the validity of a
    triple is reduced to simple logical and algebraic calculations
    showing that some assertions imply others.  In this section, we
    show that this informal presentation style can actually be made
    completely formal and indeed that checking the validity of
    decorated programs can mostly be automated.  *)

(* ================================================================= *)
(** ** Syntax *)

(** The first thing we need to do is to formalize a variant of the
    syntax of commands with embedded assertions.  We call the new
    commands _decorated commands_, or [dcom]s.

    The choice of exactly where to put assertions in the definition of
    [dcom] is a bit subtle.  The simplest thing to do would be to
    annotate every [dcom] with a precondition and postcondition.  But
    this would result in very verbose programs with a lot of repeated
    annotations: for example, a program like [SKIP;SKIP] would have to
    be annotated as

        {{P}} ({{P}} SKIP {{P}}) ;; ({{P}} SKIP {{P}}) {{P}},

    with pre- and post-conditions on each [SKIP], plus identical pre-
    and post-conditions on the semicolon!

    We don't want both preconditions and postconditions on each
    command, because a sequence of two commands would contain
    redundant decorations--the postcondition of the first likely being
    the same as the precondition of the second.

    Instead, we decorate commands as follows:

       - The _post_-condition expected by each [dcom] [d] is embedded
         in [d].

       - The _pre_-condition is supplied by the context. *)

Inductive dcom : Type :=
  | DCSkip :  Assertion -> dcom
  | DCSeq : dcom -> dcom -> dcom
  | DCAsgn : string -> aexp ->  Assertion -> dcom
  | DCIf : bexp ->  Assertion -> dcom ->  Assertion -> dcom
           -> Assertion-> dcom
  | DCWhile : bexp -> Assertion -> dcom -> Assertion -> dcom
  | DCPre : Assertion -> dcom -> dcom
  | DCPost : dcom -> Assertion -> dcom.

(** [DCPre] is used to provide the weakened precondition from
    the rule of consequence. To provide the initial precondition
    at the very top of the program, we use [Decorated]: *)    

Inductive decorated : Type :=
  | Decorated : Assertion -> dcom -> decorated.

(** To avoid clashing with the existing [Notation] definitions for
    ordinary [com]mands, we introduce these notations in a special
    scope called [dcom_scope], and we [Open] this scope for the
    remainder of the file. *)

Delimit Scope default with default.

Notation "'SKIP' {{ P }}"
      := (DCSkip P)
      (at level 10) : dcom_scope.
Notation "l '::=' a {{ P }}"
      := (DCAsgn l a P)
      (at level 60, a at next level) : dcom_scope.
Notation "'WHILE' b 'DO' {{ Pbody }} d 'END' {{ Ppost }}"
      := (DCWhile b Pbody d Ppost)
      (at level 80, right associativity) : dcom_scope.
Notation "'TEST' b 'THEN' {{ P }} d 'ELSE' {{ P' }} d' 'FI' {{ Q }}"
      := (DCIf b P d P' d' Q)
      (at level 80, right associativity)  : dcom_scope.
Notation "'->>' {{ P }} d"
      := (DCPre P d)
      (at level 90, right associativity)  : dcom_scope.
Notation "d '->>' {{ P }}"
      := (DCPost d P)
      (at level 80, right associativity)  : dcom_scope.
Notation " d ;; d' "
      := (DCSeq d d')
      (at level 80, right associativity)  : dcom_scope.
Notation "{{ P }} d"
      := (Decorated P d)
      (at level 90)  : dcom_scope.

Delimit Scope dcom_scope with dcom.
Open Scope dcom_scope.

Example dec0 :=
  SKIP {{ True }}.
Example dec1 :=
  WHILE true DO {{ True }} SKIP {{ True }} END
  {{ True }}.
(* Set Printing All. *)

Example dec_while : decorated :=
  {{ True }} 
  WHILE ~(X = 0)
  DO
    {{ True /\ (X <> 0) }}
    X ::= X - 1
    {{ True }}
  END
  {{ True /\  X = 0}} ->>
  {{ X = 0 }}.

(** It is easy to go from a [dcom] to a [com] by erasing all
    annotations. *)

Fixpoint extract (d : dcom) : com :=
  match d with
  | DCSkip _           => SKIP
  | DCSeq d1 d2        => (extract d1 ;; extract d2)
  | DCAsgn X a _       => X ::= a
  | DCIf b _ d1 _ d2 _ => TEST b THEN extract d1 ELSE extract d2 FI
  | DCWhile b _ d _    => WHILE b DO extract d END
  | DCPre _ d          => extract d
  | DCPost d _         => extract d
  end.

Definition extract_dec (dec : decorated) : com :=
  match dec with
  | Decorated P d => extract d
  end.

Print dec_while.
(*
dec_while = 
{{fun _ : state => True}} (WHILE ~ X = 0
                           DO {{fun st : state => True /\ st X <> 0}} 
                           X ::= X - 1 {{fun _ : state => True}}
                           END {{fun st : state => True /\ st X = 0}}) ->>
                          {{fun st : state => st X = 0}}
     : decorated
*)

Compute (extract_dec dec_while).
(*
     = (WHILE ~ "X"%string = 0 DO "X" ::= "X"%string - 1 END)%imp
     : com
*)

(** It is straightforward to extract the precondition and
    postcondition from a decorated program. *)

Fixpoint post (d : dcom) : Assertion :=
  match d with
  | DCSkip P                => P
  | DCSeq d1 d2             => post d2
  | DCAsgn X a Q            => Q
  | DCIf  _ _ d1 _ d2 Q     => Q
  | DCWhile b Pbody c Ppost => Ppost
  | DCPre _ d               => post d
  | DCPost c Q              => Q
  end.

Definition pre_dec (dec : decorated) : Assertion :=
  match dec with
  | Decorated P d => P
  end.

Definition post_dec (dec : decorated) : Assertion :=
  match dec with
  | Decorated P d => post d
  end.

Print dec_while.
(* 
dec_while = 
{{fun _ : state => True}} (WHILE ~ X = 0
                           DO {{fun st : state => True /\ st X <> 0}} 
                           X ::= X - 1 {{fun _ : state => True}}
                           END {{fun st : state => True /\ st X = 0}}) ->>
                          {{fun st : state => st X = 0}}
     : decorated
*)

Compute pre_dec dec_while.
(*
     = fun _ : state => True
     : Assertion
*)

Compute post_dec dec_while.
(*
     = fun x : state => x "X"%string = 0
     : Assertion
*)

(** We can express what it means for a decorated program to be
    correct as follows: *)

Definition dec_correct (dec : decorated) :=
  {{pre_dec dec}} (extract_dec dec) {{post_dec dec}}.

Example dec_while_triple_correct :
  dec_correct dec_while
 = {{ fun st => True }}
   (WHILE ~(X = 0) DO X ::= X - 1 END)%imp
   {{ fun st => st X = 0 }}.
Proof. reflexivity. Qed.

(** To check whether this Hoare triple is _valid_, we need a way to
    extract the "proof obligations" from a decorated program. These
    obligations are often called _verification conditions_, because
    they are the facts that must be verified to see that the
    decorations are logically consistent and thus constitute a proof
    of correctness. *)

(* ================================================================= *)
(** ** Extracting Verification Conditions *)

(** The function [verification_conditions] takes a [dcom] [d] together
    with a precondition [P] and returns a _proposition_ that, if it
    can be proved, implies that the triple [{{P}} (extract d) {{post d}}]
    is valid. *)

(** It does this by walking over [d] and generating a big
    conjunction including all the "local checks" that we listed when
    we described the informal rules for decorated programs.  (Strictly
    speaking, we need to massage the informal rules a little bit to
    add some uses of the rule of consequence, but the correspondence
    should be clear.) *)

Fixpoint verification_conditions (P : Assertion) (d : dcom) : Prop :=
  match d with
  | DCSkip Q =>
      (P ->> Q)
  | DCSeq d1 d2 =>
      verification_conditions P d1
      /\ verification_conditions (post d1) d2
  | DCAsgn X a Q =>
      (P ->> Q [X |-> a])
  | DCIf b P1 d1 P2 d2 Q =>
      ((P /\ b) ->> P1)%assertion
      /\ ((P /\ ~ b) ->> P2)%assertion
      /\ (post d1 ->> Q) /\ (post d2 ->> Q)
      /\ verification_conditions P1 d1
      /\ verification_conditions P2 d2
  | DCWhile b Pbody d Ppost =>
      (* post d is the loop invariant and the initial
         precondition *)
      (P ->> post d)
      /\ ((post d  /\ b) ->> Pbody)%assertion
      /\ ((post d  /\ ~ b) ->> Ppost)%assertion
      /\ verification_conditions Pbody d
  | DCPre P' d =>
      (P ->> P') /\ verification_conditions P' d
  | DCPost d Q =>
      verification_conditions P d /\ (post d ->> Q)
  end.

(** And now the key theorem, stating that [verification_conditions]
    does its job correctly.  Not surprisingly, we need to use each of
    the Hoare Logic rules at some point in the proof. *)

Theorem verification_correct : forall d P,
  verification_conditions P d -> {{P}} (extract d) {{post d}}.
Proof.
  induction d; intros P H; simpl in *.
  - (* Skip *)
    eapply hoare_consequence_pre.
      apply hoare_skip.
      assumption.
  - (* Seq *)
    destruct H as [H1 H2].
    eapply hoare_seq.
      apply IHd2. apply H2.
      apply IHd1. apply H1.
  - (* Asgn *)
    eapply hoare_consequence_pre.
      apply hoare_asgn.
      assumption.
  - (* If *)
    destruct H as [HPre1 [HPre2 [Hd1 [Hd2 [HThen HElse]]]]].
    apply IHd1 in HThen. clear IHd1.
    apply IHd2 in HElse. clear IHd2.
    apply hoare_if.
      + eapply hoare_consequence_post with (Q':=post d1); eauto.
         eapply hoare_consequence_pre; eauto.
      + eapply hoare_consequence_post with (Q':=post d2); eauto.
         eapply hoare_consequence_pre; eauto.
  - (* While *)
    destruct H as [Hpre [Hbody1 [Hpost1  Hd]]].
    eapply hoare_consequence_pre; eauto.
    eapply hoare_consequence_post; eauto.
    apply hoare_while.
    eapply hoare_consequence_pre; eauto.
  - (* Pre *)
    destruct H as [HP Hd].
    eapply hoare_consequence_pre. apply IHd. apply Hd. assumption.
  - (* Post *)
    destruct H as [Hd HQ].
    eapply hoare_consequence_post. apply IHd. apply Hd. assumption.
Qed.

(** Now that all the pieces are in place, we can verify an entire program. *)

Definition verification_conditions_dec (dec : decorated) : Prop :=
  match dec with
  | Decorated P d => verification_conditions P d
  end.

Corollary verification_correct_dec : forall dec,
  verification_conditions_dec dec -> dec_correct dec.
Proof.
  intros [P d]. apply verification_correct.
Qed.

(** The propositions generated by [verification_conditions] are fairly
    big, and they contain many conjuncts that are essentially trivial. *)

Eval simpl in (verification_conditions_dec dec_while).
(**

   ===>
    (((fun _ : state => True) ->> (fun _ : state => True)) /\
     ((fun st : state => True /\ bassn (~(X = 0)) st) ->>
      (fun st : state => True /\ st X <> 0)) /\
     ((fun st : state => True /\ ~ bassn (~(X = 0)) st) ->>
      (fun st : state => True /\ st X = 0)) /\
      (fun st : state => True /\ st X <> 0) ->>
      (fun _ : state => True) [X |-> X - 1]) /\
      (fun st : state => True /\ st X = 0) ->> 
      (fun st : state => st X = 0)   
*)

(* ================================================================= *)
(** ** Automation *)

(** In principle, we could work with such propositions using just the
    tactics we have so far, but we can make things much smoother with
    a bit of automation.  We first define a custom [verify] tactic
    that uses [split] repeatedly to turn all the conjunctions into
    separate subgoals and then uses [omega] and [eauto] (described in
    chapter [Auto] in _Logical Foundations_) to deal with as many
    of them as possible. *)

Tactic Notation "verify" :=
  apply verification_correct;
  repeat split;
  simpl; unfold assert_implies;
  unfold ap in *; unfold ap2 in *; unfold bassn in *; unfold beval in *; unfold aeval in *;
  unfold assn_sub; intros;
  repeat (simpl in *;
          rewrite t_update_eq ||
          (try rewrite t_update_neq; [| (intro X; inversion X; fail)]));
  simpl in *; 
  repeat match goal with [H : _ /\ _ |- _] => destruct H end;
  repeat rewrite not_true_iff_false in *;
  repeat rewrite not_false_iff_true in *;
  repeat rewrite negb_true_iff in *;
  repeat rewrite negb_false_iff in *;
  repeat rewrite eqb_eq in *;
  repeat rewrite eqb_neq in *;
  repeat rewrite leb_iff in *;
  repeat rewrite leb_iff_conv in *;
  try subst;
  simpl in *;
  repeat
    match goal with
      [st : state |- _] =>
        match goal with
        | [H : st _ = _ |- _] => rewrite -> H in *; clear H
        | [H : _ = st _ |- _] => rewrite <- H in *; clear H
        end
    end;
  try eauto; try omega.

(** What's left after [verify] does its thing is "just the interesting
    parts" of checking that the decorations are correct. For very
    simple examples, [verify] sometimes even immediately solves the
    goal (provided that the annotations are correct!). *)

Theorem dec_while_correct :
  dec_correct dec_while.
Proof. verify. Qed.

(* ================================================================= *)
(** ** Examples *)

(** In this section, we use the automation developed above to verify
    formal decorated programs corresponding to most of the informal
    ones we have seen. *)

(* ----------------------------------------------------------------- *)
(** *** Slow Subtraction *)

Example subtract_slowly_dec (m : nat) (p : nat) : decorated :=
    {{ X = m /\  Z = p }} ->>
    {{ Z - X = p - m }}
  WHILE ~(X = 0)
  DO   {{ Z - X = p - m /\ X  <>  0 }} ->>
       {{ (Z - 1) - (X - 1) = p - m }}
     Z ::= Z - 1
       {{ Z - (X - 1) = p - m }} ;;
     X ::= X - 1
       {{ Z - X = p - m }}
  END
    {{ Z - X = p - m /\ X = 0 }} ->>
    {{ Z = p - m }}.

Theorem subtract_slowly_dec_correct : forall m p,
  dec_correct (subtract_slowly_dec m p).
Proof. intros m p. verify. (* this grinds for a bit! *) Qed.

(* ----------------------------------------------------------------- *)
(** *** Swapping Using Addition and Subtraction *)

Definition swap : com :=
  X ::= X + Y;;
  Y ::= X - Y;;
  X ::= X - Y.

Definition swap_dec (m n:nat) : decorated :=
   {{ X = m /\ Y = n}} ->>
   {{ (X + Y) - ((X + Y) - Y) = n
                /\ (X + Y) - Y = m }}
  X ::= X + Y
   {{ X - (X - Y) = n /\ X - Y = m }};;
  Y ::= X - Y
   {{ X - Y = n /\ Y = m }};;
  X ::= X - Y
   {{ X = n /\ Y = m}}.

Theorem swap_correct : forall m n,
  dec_correct (swap_dec m n).
Proof. intros; verify.   Qed.

(**  MRC hid some proofs here so as not to spoil earlier exercises.
   Consider the pros and cons of this. 
 *)
(* ----------------------------------------------------------------- *)
(** *** Division *)

Definition div_mod_dec (a b : nat) : decorated :=
  {{ True }} ->>
  {{ b * 0 + a = a }}
  X ::= a
  {{ b * 0 + X = a }};;
  Y ::= 0
  {{ b * Y + X = a }};;
  WHILE b <= X DO
    {{ b * Y + X = a /\ b <= X }} ->>
    {{ b * (Y + 1) + (X - b) = a }}
    X ::= X - b
    {{ b * (Y + 1) + X = a }};;
    Y ::= Y + 1
    {{ b * Y + X = a }}
  END
  {{ b * Y + X = a /\ ~(b <= X) }} ->>
  {{ b * Y + X = a /\ (X < b) }}.

Theorem div_mod_dec_correct : forall a b,
  dec_correct (div_mod_dec a b).
Proof. intros a b. verify.
  rewrite mult_plus_distr_l. omega.
Qed.

(* ----------------------------------------------------------------- *)
(** *** Parity *)

Definition find_parity : com :=
  WHILE 2 <= X DO
     X ::= X - 2
  END.

(** There are actually several ways to phrase the loop invariant for
    this program.  Here is one natural one, which leads to a rather
    long proof: *)

Inductive ev : nat -> Prop :=
  | ev_0 : ev O
  | ev_SS : forall n : nat, ev n -> ev (S (S n)).

Definition find_parity_dec (m:nat) : decorated :=
   {{ X = m }} ->>
   {{ X <= m /\ ap ev (m - X) }}
  WHILE 2 <= X DO
     {{ (X <= m /\ ap ev (m - X)) /\ 2 <= X }} ->>
     {{ X - 2 <= m /\ ap ev (m - (X - 2)) }}
     X ::= X - 2
     {{ X <= m /\ ap ev (m - X) }}
  END
   {{ (X <= m /\ ap ev (m - X)) /\ X < 2 }} ->>
   {{  X = 0 <-> ev m }}.

Lemma l1 : forall m n p,
  p <= n ->
  n <= m ->
  m - (n - p) = m - n + p.
Proof. intros. omega. Qed.

Lemma l2 : forall m,
  ev m ->
  ev (m + 2).
Proof. intros. rewrite plus_comm. simpl. constructor. assumption. Qed.

Lemma l3' : forall m,
  ev m ->
  ~ev (S m).
Proof. induction m; intros H1 H2. inversion H2. apply IHm.
       inversion H2; subst; assumption. assumption. Qed.

Lemma l3 : forall m,
  1 <= m ->
  ev m ->
  ev (m - 1) ->
  False.
Proof. intros. apply l2 in H1.
       assert (G : m - 1 + 2 = S m). clear H0 H1. omega.
       rewrite G in H1. apply l3' in H0. apply H0. assumption. Qed.

Theorem find_parity_correct : forall m,
  dec_correct (find_parity_dec m).
Proof.
  intro m. verify;
    (* simplification too aggressive ... reverting a bit *)
    fold (2 <=? (st X)) in *;
    try rewrite leb_iff in *;
    try rewrite leb_iff_conv in *; eauto; try omega.  
  - (* invariant holds initially *)
    rewrite minus_diag. constructor.
  - (* invariant preserved *)
    rewrite l1; try assumption.
    apply l2; assumption.
  - (* invariant strong enough to imply conclusion
         (-> direction) *)
    rewrite <- minus_n_O in H2. assumption.
  - (* invariant strong enough to imply conclusion
         (<- direction) *)
    destruct (st X) as [| [| n]].
    (* by H1 X can only be 0 or 1 *)
    + (* st X = 0 *)
      reflexivity.
    + (* st X = 1 *)
      apply l3 in H; try assumption. inversion H.
    + (* st X = 2 *)
      clear H0 H2. (* omega confused otherwise *)
      omega.
Qed.

(** Here is a more intuitive way of writing the invariant: *)

Definition find_parity_dec' (m:nat) : decorated :=
  {{ X = m }} ->>
  {{ ap ev X <-> ev m }}
 WHILE 2 <= X DO
    {{ (ap ev X <-> ev m) /\ 2 <= X }} ->>
    {{ ap ev (X - 2) <-> ev m }}
    X ::= X - 2
    {{ ap ev X <-> ev m }}
 END
 {{ (ap ev X <-> ev m) /\ ~(2 <= X) }} ->>
 {{  X=0 <-> ev m }}.

Lemma l4 : forall m,
  2 <= m ->
  (ev (m - 2) <-> ev m).
Proof.
  induction m; intros. split; intro; constructor.
  destruct m. inversion H. inversion H1. simpl in *.
  rewrite <- minus_n_O in *. split; intro.
    constructor. assumption.
    inversion H0. assumption.
Qed.

Theorem find_parity_correct' : forall m,
  dec_correct (find_parity_dec' m).
Proof.
  intros m. verify;
    (* simplification too aggressive ... reverting a bit *)
    fold (2 <=? (st X)) in *;
    try rewrite leb_iff in *;
    try rewrite leb_iff_conv in *; intuition; eauto; try omega.
  - (* invariant preserved (part 1) *)
    rewrite l4 in H0; eauto.
  - (* invariant preserved (part 2) *)
    rewrite l4; eauto.
  - (* invariant strong enough to imply conclusion
       (-> direction) *)
    apply H0. constructor.
  - (* invariant strong enough to imply conclusion
       (<- direction) *)
      destruct (st X) as [| [| n]]. (* by H1 X can only be 0 or 1 *)
      + (* st X = 0 *)
        reflexivity.
      + (* st X = 1 *)
        inversion H.
      + (* st X = 2 *)
        clear H0 H H3. (* omega confused otherwise *)
        omega.
Qed.

(* ----------------------------------------------------------------- *)
(** *** Square Roots *)

Definition sqrt_dec (m:nat) : decorated :=
    {{ X = m }} ->>
    {{ X = m /\ 0*0 <= m }}
  Z ::= 0
    {{ X = m /\ Z*Z <= m }};;
  WHILE (Z+1)*(Z+1) <= X DO
      {{ (X = m /\ Z*Z<=m)
                   /\ (Z + 1)*(Z + 1) <= X }} ->>
      {{ X = m /\ (Z+1)*(Z+1)<=m }}
    Z ::= Z + 1
      {{ X = m /\ Z*Z<=m }}
  END
    {{ (X = m /\ Z*Z<=m)
                   /\ ~((Z + 1)*(Z + 1) <= X) }} ->>
    {{ Z*Z<=m /\ m<(Z+1)*(Z+1) }}.

Theorem sqrt_correct : forall m,
  dec_correct (sqrt_dec m).
Proof. intro m. verify. Qed.

(* ----------------------------------------------------------------- *)
(** *** Squaring *)

(** Again, there are several ways of annotating the squaring program.
    The simplest variant we've found, [square_simpler_dec], is given
    last. *)

Definition square_dec (m : nat) : decorated :=
  {{ X = m }}
  Y ::= X
  {{ X = m /\ Y = m }};;
  Z ::= 0
  {{ X = m /\ Y = m /\ Z = 0}} ->>
  {{ Z + X * Y = m * m }};;
  WHILE ~ (Y = 0) DO
    {{ Z + X * Y = m * m /\ Y <> 0 }} ->>
    {{ (Z + X) + X * (Y - 1) = m * m }}
    Z ::= Z + X
    {{ Z + X * (Y - 1) = m * m }};;
    Y ::= Y - 1
    {{ Z + X * Y = m * m }}
  END
  {{ Z + X * Y = m * m /\ Y = 0 }} ->>
  {{ Z = m * m }}.

Theorem square_dec_correct : forall m,
  dec_correct (square_dec m).
Proof.
  intro n. verify.
  - (* invariant preserved *)
    destruct (st Y) as [| y'].
    + exfalso. auto.
    + simpl. rewrite <- minus_n_O.
    assert (G : forall n m, n * S m = n + n * m). {
      clear. intros. induction n. reflexivity. simpl.
      rewrite IHn. omega. }
    rewrite <- H. rewrite G. omega. 
Qed.

Definition square_dec' (n : nat) : decorated :=
  {{ True }}
  X ::= n
  {{ X = n }};;
  Y ::= X
  {{ X = n /\ Y = n }};;
  Z ::= 0
  {{ X = n /\ Y = n /\ Z = 0 }} ->>
  {{ Z = X * (X - Y)
               /\ X = n /\ Y <= X }};;
  WHILE ~(Y = 0) DO
    {{ (Z = X * (X - Y)
                /\ X = n /\ Y <= X)
                /\  Y <> 0 }}
    Z ::= Z + X
    {{ Z = X * (X - (Y - 1))
                 /\ X = n /\ Y <= X }};;
    Y ::= Y - 1
    {{ Z = X * (X - Y)
                 /\ X = n /\ Y <= X }}
  END
  {{ (Z = X * (X - Y)
              /\ X = n /\ Y <= X)
               /\ Y = 0 }} ->>
  {{ Z = n * n }}.

Theorem square_dec'_correct : forall (n:nat),
  dec_correct (square_dec' n).
Proof.
  intro n. verify.
  - (* invariant holds initially *)
    rewrite minus_diag. omega.
  - (* invariant preserved *) subst.
    rewrite mult_minus_distr_l.
    repeat rewrite mult_minus_distr_l. rewrite mult_1_r.
    assert (G : forall n m p,
                  m <= n -> p <= m -> n - (m - p) = n - m + p).
      intros. omega.
    rewrite G. reflexivity. apply mult_le_compat_l. assumption.
    destruct (st Y).
    + exfalso. auto. 
    + clear. rewrite mult_succ_r. rewrite plus_comm. 
      apply le_plus_l.
  - (* invariant + negation of guard imply
       desired postcondition *)
    rewrite <- minus_n_O. reflexivity.
Qed.

Definition square_simpler_dec (m : nat) : decorated :=
  {{ X = m }} ->>
  {{ 0 = 0*m /\ X = m }}
  Y ::= 0
  {{ 0 = Y*m /\ X = m }};;
  Z ::= 0
  {{ Z = Y*m /\ X = m }};;
  WHILE ~(Y = X) DO
    {{ (Z = Y*m /\ X = m)
        /\ Y <> X }} ->>
    {{ Z + X = (Y + 1)*m /\ X = m }}
    Z ::= Z + X
    {{ Z = (Y + 1)*m /\ X = m }};;
    Y ::= Y + 1
    {{ Z = Y*m /\ X = m }}
  END
  {{ (Z = Y*m /\ X = m) /\ Y = X }} ->>
  {{ Z = m*m }}.

Theorem square_simpler_dec_correct : forall m,
  dec_correct (square_simpler_dec m).
Proof.
  intro m. verify.
  rewrite mult_plus_distr_r. omega. 
Qed.

(* ----------------------------------------------------------------- *)
(** *** Power Series *)

Fixpoint pow2 n :=
  match n with
  | 0 => 1
  | S n' => 2 * (pow2 n')
  end.

Definition dpow2_down (n : nat) :=
  {{ True }} ->>
  {{ 1 = (pow2 (0 + 1))-1 /\ 1 = pow2 0 }}
  X ::= 0
  {{ 1 = (pow2 (0 + 1))-1 /\ 1 = ap pow2 X }};;
  Y ::= 1
  {{ Y = (ap pow2 (X + 1))-1 /\ 1 = ap pow2 X}};;
  Z ::= 1
  {{ Y = (ap pow2 (X + 1))-1 /\ Z = ap pow2 X }};;
  WHILE ~(X = n) DO
    {{ (Y = (ap pow2 (X + 1))-1 /\ Z = ap pow2 X)
                 /\ X <> n }} ->>
    {{ Y + 2 * Z = (ap pow2 (X + 2))-1
                 /\ 2 * Z = ap pow2 (X + 1) }}
    Z ::= 2 * Z
    {{ Y + Z = (ap pow2 (X + 2))-1
                 /\ Z = ap pow2 (X + 1) }};;
    Y ::= Y + Z
    {{ Y = (ap pow2 (X + 2))-1
                 /\ Z = ap pow2 (X + 1) }};;
    X ::= X + 1
    {{ Y = (ap pow2 (X + 1))-1
                 /\ Z = ap pow2 X }}
  END
  {{ (Y = (ap pow2 (X + 1))-1 /\ Z = ap pow2 X)
               /\ X = n }} ->>
  {{ Y = pow2 (n+1) - 1 }}.

Lemma pow2_plus_1 : forall n,
  pow2 (n+1) = pow2 n + pow2 n.
Proof. induction n; simpl. reflexivity. omega. Qed.

Lemma pow2_le_1 : forall n, pow2 n >= 1.
Proof. induction n. simpl. constructor. simpl. omega. Qed.

Theorem dpow2_down_correct : forall n,
  dec_correct (dpow2_down n).
Proof.
  intro m. verify.
  - (* 1 *)
    rewrite pow2_plus_1. rewrite <- H0. reflexivity.
  - (* 2 *)
    rewrite <- plus_n_O.
    rewrite <- pow2_plus_1. remember (st X) as n.
    replace (pow2 (n + 1) - 1 + pow2 (n + 1))
       with (pow2 (n + 1) + pow2 (n + 1) - 1) by omega.
    rewrite <- pow2_plus_1.
    replace (n + 1 + 1) with (n + 2) by omega.
    reflexivity.
  - (* 3 *)
    rewrite <- plus_n_O. rewrite <- pow2_plus_1.
    reflexivity.
  - (* 4 *)
    replace (st X + 1 + 1) with (st X + 2) by omega.
    reflexivity.
Qed.

(* ================================================================= *)
(** ** Further Exercises *)

(** **** Exercise: 3 stars, advanced (slow_assignment_dec) 

    In the [slow_assignment] exercise above, we saw a roundabout way
    of assigning a number currently stored in [X] to the variable [Y]:
    start [Y] at [0], then decrement [X] until it hits [0],
    incrementing [Y] at each step. Transform the informal decorated
    program your wrote for [slow_assignment] into a formal decorated
    program and prove its correctness. If all goes well, your
    correctness proof will need only [intros] and [verify].

    Hint: most of transformation will involve replacing informal
    assertions with formal assertions.  For example, you would
    replace [{{ X = m /\ Y = 0}}] with [{{ fun st => st X = m /\ st Y = 0 }}].
    Also, semicolons go after the postcondition of an assignment in
    a formal decorated program, as in this example:

    {{ X = m /\ 0 = 0 }}
  Y ::= 0;;
    {{ X = m /\ Y = 0 }}

becomes

    {{ fun st => st X = m /\ 0 = 0 }}
  Y ::= 0
    {{ fun st => st X = m /\ st Y = 0 }} ;;

*)

Example slow_assignment_dec (m : nat) : decorated
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Theorem slow_assignment_dec_correct : forall m,
  dec_correct (slow_assignment_dec m).
Proof. (* FILL IN HERE *) Admitted.

(* Do not modify the following line: *)
Definition manual_grade_for_check_defn_of_slow_assignment_dec : option (nat*string) := None.
(** [] *)

(** **** Exercise: 4 stars, advanced (factorial_dec)  

    The factorial function is defined recursively in the Coq standard
    library in a way that is equivalent to the following:

Fixpoint fact (n : nat) : nat :=
  match n with
  | O => 1
  | S n' => n * (fact n')
  end.
*)

Compute fact 5. (* ==> 120 *)

(** Using your solutions to [factorial] and [slow_assignment_dec] as a
    guide, write a formal decorated program [factorial_dec] that
    implements the factorial function, state a theorem named
    [factorial_dec_correct] that says [factorial_dec] is correct, and
    prove the theorem. If all goes well, [verify] will leave you with
    just two subgoals, each of which requires establishing some
    mathematical property of [fact] rather than proving anything about
    your program.

    Hint: when transforming a loop guard into a formal assertion, make
    sure to express it with [bassn]. *)

(* FILL IN HERE *)

(* Do not modify the following line: *)
Definition manual_grade_for_factorial_dec : option (nat*string) := None.
(** [] *)

(** **** Exercise: 4 stars, advanced, optional (fib_eqn) 

    The Fibonacci function is usually written like this:

      Fixpoint fib n :=
        match n with
        | 0 => 1
        | 1 => 1
        | _ => fib (pred n) + fib (pred (pred n))
        end.

   This doesn't pass Coq's termination checker, but here is a
   slightly clunkier definition that does: *)

Fixpoint fib n :=
  match n with
  | 0 => 1
  | S n' => match n' with
            | 0 => 1
            | S n'' => fib n' + fib n''
            end
  end.

(** Prove that [fib] satisfies the following equation: *)

Lemma fib_eqn : forall n,
  n > 0 ->
  fib n + fib (pred n) = fib (n + 1).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 4 stars, advanced, optional (fib) 

    The following Imp program leaves the value of [fib n] in the
    variable [Y] when it terminates:

    X ::= 1;;
    Y ::= 1;;
    Z ::= 1;;
    WHILE ~(X = n + 1) DO
      T ::= Z;;
      Z ::= Z + Y;;
      Y ::= T;;
      X ::= X + 1
    END

    Fill in the following definition of [dfib] and prove that it
    satisfies this specification:

      {{ True }} dfib {{ Y = fib n }}
*)

Definition T : string := "T".
                      
Definition dfib (n : nat) : decorated
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Theorem dfib_correct : forall n,
  dec_correct (dfib n).
(* FILL IN HERE *) Admitted.
(** [] *)

Close Scope dcom_scope.

(** **** Exercise: 5 stars, advanced, optional (improve_dcom) 

    The formal decorated programs defined in this section are intended
    to look as similar as possible to the informal ones defined earlier
    in the chapter.  If we drop this requirement, we can eliminate
    almost all annotations, just requiring final postconditions and
    loop invariants to be provided explicitly.  Do this -- i.e., define a
    new version of dcom with as few annotations as possible and adapt the
    rest of the formal development leading up to the [verification_correct]
    theorem. *)

(* FILL IN HERE

    [] *)

(** **** Exercise: 4 stars, advanced, optional (implement_dcom) 

    Adapt the parser for Imp presented in chapter [ImpParser]
    of _Logical Foundations_ to parse decorated commands (either ours
    or, even better, the ones you defined in the previous exercise). *)

(* FILL IN HERE

    [] *)


(* 2020-07-24 23:00:10 (UTC+00) *)
