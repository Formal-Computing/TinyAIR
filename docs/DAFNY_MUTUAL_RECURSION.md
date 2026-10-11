# Dafny A/B mutual recursion: lexicographic termination

Reference: https://dafny.org/latest/DafnyRef/DafnyRef#sec-decreases-clause

Dafny's mutually recursive methods:

    method A(x: nat)
      decreases x, 1
    { B(x); }

    method B(x: nat)
      decreases x, 0
    { if x != 0 { A(x-1); } }

TinyAIR supports the corresponding source directly:

    A :: Int -> Int
    requires x >= 0
    decreases x, 1
    ensures result == 0
    A x = B(x)

    B :: Int -> Int
    requires x >= 0
    decreases x, 0
    ensures result == 0
    B x = if x != 0 then A(x-1) else 0

We use Int + requires x>=0 to model Dafny nat; because TinyAIR has
no void/Unit type, the functions return an arbitrary constant 0.
The termination control flow is otherwise equivalent.

## Verification conditions

A(x) -> B(x), for all x>=0:

    (x,0,TOP) < (x,1,TOP)

First coordinates equal. 0 < 1 establishes strict descent.

B(x) -> A(x-1), under x>=0 and x!=0:

    requires_A(x-1): x-1>=0
    (x-1,1,TOP) < (x,0,TOP)

First coordinates strictly decrease. The second coordinate
increases, but lexicographic ordering ignores it.

A and B therefore terminate via a well-founded lexicographic rank
whose effective integer components are bounded below whenever they
decrease.

## Dafny's shorter syntax

Dafny implicitly appends TOP. Hence these are also valid:

    A: decreases x        -> (x,TOP)
    B: decreases x,0      -> (x,0,TOP)

For the call A->B, (x,0,TOP)<(x,TOP) by TOP. For B->A,
(x-1,TOP)<(x,0,TOP) by the first integer component.

## Boolean ranking phase

Also supported:

    A: decreases (x, True)
    B: decreases (x, False)

False < True, and the first component falls on the return call.

## Negative example

With both functions declaring decreases x, the call A(x)->B(x)
does not establish a strict decrease: x is unchanged. That version
is intentionally rejected, although the program itself terminates.

## Running the examples

    python -m tinyair examples/dafny_mutual_rank.air --emit-smt2 smt-out
    python -m tinyair examples/dafny_mutual_top.air --emit-smt2 smt-out
    python -m tinyair examples/dafny_mutual_bool.air --emit-smt2 smt-out
    python -m tinyair examples/dafny_mutual_naive.air --emit-smt2 smt-out
    python -m unittest discover -s tests -v

Each case exports separately numbered verification conditions for A
and B to smt-out. The correct cases must pass every condition,
while the naive version fails A's strict-decrease condition.
