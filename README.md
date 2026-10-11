# TinyAIR — pure functional language with Z3 verification

A small Python implementation for Automated and Interactive Reasoning.
Programs have a Haskell-inspired syntax, type-checked expressions,
pre/postconditions, self-recursion, and mutual recursion. Z3 checks
verification conditions (VCs) symbolically over unbounded integers.

## Run

Open PowerShell in this project folder:

    python -m pip install --user -e .
    python -m unittest discover -s tests -v

Verify a single function:

    python -m tinyair examples/max3.air
    python -m tinyair examples/factorial.air

Verify several mutually recursive functions:

    python -m tinyair examples/dafny_mutual_rank.air
    python -m tinyair examples/dafny_mutual_top.air
    python -m tinyair examples/dafny_mutual_bool.air

Export SMT-LIB VCs (one file per condition):

    python -m tinyair examples/dafny_mutual_rank.air --emit-smt2 smt-out

The exported .smt2 files contain negated VCs. Running Z3 against one
returns unsat when the original VC is proved, sat for a counterexample,
or unknown when it cannot determine validity.

## Dafny-style tuple decreases (v0.4)

Lexicographic termination metrics are written as expression lists:

    A :: Int -> Int
    requires x >= 0
    decreases x, 1
    ensures result == 0
    A x = B(x)

    B :: Int -> Int
    requires x >= 0
    decreases x, 0
    ensures result == 0
    B x = if x != 0 then A(x - 1) else 0

The ranking tuples strictly decrease:

- A(x) -> B(x): (x, 0) < (x, 1)
- B(x) -> A(x - 1): (x - 1, 1) < (x, 0)

Parenthesized forms such as decreases (x, True) also work. Clauses
may be split across multiple decreases lines and are concatenated.
A conceptual TOP element is appended, so these differing lengths work:

    A: decreases x
    B: decreases x, 0

The verifier supports Int and Bool rank components, first-difference
ordering, and nonnegative integer caller components for well-founded
integer descent. Old one-component decreases n remains compatible.
The check is proof-based, not bounded recursion unfolding.

## Code layout

- src/tinyair/syntax.py : abstract syntax tree
- src/tinyair/parser.py : parser and decreases-expression lists
- src/tinyair/rank.py : lexicographic ordering + implicit TOP
- src/tinyair/verification.py : one-function symbolic verifier
- src/tinyair/module_verification.py : call graph + mutual recursion VCs
- src/tinyair/cli.py : command line + .smt2 export
- docs/LANGUAGE.md : full TinyAIR subset specification
- docs/DAFNY_MUTUAL_RECURSION.md : worked Dafny example
- examples/ : verified and intentionally incorrect programs
- tests/ : regression tests

## Known limits

TinyAIR implements a subset, not the entire Dafny language. For
decreases, it supports Int/Bool tuples and implicit TOP suffix, but
does not infer a missing decreases clause, implement Dafny's implicit
call-graph prefixes, or handle sets, sequences, reference values, or
other Dafny types as ranking components. Entry nonnegativity of the
first integer component is checked conservatively. All recursive
call preconditions and decreases conditions must be verified.

## Red-black tree insertion and symbolic VCs

The persistent red-black integer set is in src/tinyair/red_black_tree.py.
The Z3 bounded exhaustive symbolic shape verification is in
src/tinyair/red_black_vc.py.

    python -m unittest discover -s tests -v
    python -m tinyair.red_black_vc --max-nodes 4 --emit-smt2 smt-out/rbt

See docs/RED_BLACK_TREE.md for verification scope. This generates
symbolic .smt2 VCs for BST ordering, red-red exclusion, equal black
height, black root, and inserted-key set preservation. The results
are bounded by tree node count, NOT a general induction proof.

## Actual red-black tree example in TinyAIR

The executable custom-language file is **examples/red_black_tree.air**.
It declares a recursive Tree constructor and implements rotLL/rotLR/
rotRL/rotRR, balance, ins, blacken, insert, and contains using TinyAIR
function definitions. The source itself is parsed and symbolically
evaluated; this is not the separate Python insertion implementation.

    python -m tinyair examples/red_black_tree.air --max-nodes 4 --emit-smt2 smt-out/rbt-air

For initial trees containing at most 4 nodes, the .air source produced
128 Z3 verification conditions, all proved. The Tree backend is
experimental and bounded, while the regular Int/Bool verification
system remains unchanged. See docs/RED_BLACK_TREE.md for exact scope,
builtins and limitations.
