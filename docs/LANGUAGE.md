# TinyAIR v0.4 — language and verification semantics

TinyAIR is a pure, first-order, Haskell-inspired functional language
implemented in Python. Verification conditions are checked with Z3.

## Syntax

Each function contains a signature, zero or more requires clauses,
one or more ensures clauses, optional decreases clauses, and a
single-line definition. Multiple functions may appear in one file.

    sum :: Int -> Int -> Int
    requires x >= 0
    requires y >= 0
    decreases x, y
    ensures result >= 0
    sum x y = x + y

Types: Int (unbounded mathematical integer) and Bool.
Expression syntax: variables, literals, parentheses, if/then/else,
immutable let/in, function(arg1, arg2), arithmetic +,-,*,
comparisons <,<=,>,>=, equality ==,!=, boolean !/not,
&&/and, ||/or. Binary operators are left-associative with ordinary
logical/arithmetic precedence. Comments begin with --.

No side effects, mutation, recursion of functions in contracts,
function imports, division, modulo, loops, or higher-order functions.

## Termination measures

A decreases clause is a NONEMPTY TUPLE OF EXPRESSIONS, not a numeric
expression that is decremented by the runtime. All of these are valid:

    decreases n
    decreases n, m
    decreases (n, m)
    decreases n, True
    decreases (n, True)

Multiple declarations are concatenated in textual order:

    decreases n
    decreases m

means the same as:

    decreases n, m

Tuple components currently must be Int or Bool. A single scalar
decreases n is internally a one-element tuple (n,).

## Dafny-style effective ranks and order

Each tuple has an implicit TOP sentinel after its final component.
TOP is greater than any real Int or Bool value. Thus the following
effective ranks are not equal:

    decreases x       -> (x, TOP)
    decreases x, 0    -> (x, 0, TOP)

They satisfy (x,0,TOP) <_lex (x,TOP). The opposite is false.

Two tuples are compared left-to-right. At the first differing
component, the callee's value must be smaller than the caller's.
Later components are ignored, even if they increase.

- Int: a is smaller than b when a < b AND b >= 0.
  The nonnegativity of the caller's *active* integer component is
  part of Dafny's well-founded integer comparison.
- Bool: False is smaller than True.
- Explicit components at the same position must have the same type
  in this implementation. Dafny supports additional sort orderings.
- A real component is less than TOP; TOP is not less than a real
  component.

The implementation also retains a conservative entry VC that the
first integer component is nonnegative on all inputs satisfying
requires. This is stricter than all Dafny use cases (which can permit
a negative entry measure when no call takes place). Later integer
tuple components are NOT required to be globally nonnegative;
well-foundedness is checked at the component that actually decreases.

Dafny also supports additional implicit rank prefixes, guesses for
omitted clauses, and sets/sequences. TinyAIR does not implement those.

## Recursive/mutually recursive VCs

The compiler builds the static call graph. Each recursive SCC must
have a rank for every member. A call on a cyclic edge from f(x) to
g(a) gets these proof obligations, guarded by its execution path:

1. Callee precondition holds.
2. Callee's first integer rank component is nonnegative (or True
   if first component is Bool; conservative compatibility VC).
3. The callee's effective rank is lexicographically smaller
   than the caller's effective rank.

For example:

    A: decreases x, 1
    B: decreases x, 0

The call A(x) -> B(x) checks (x,0,TOP) < (x,1,TOP).
The call B(x) -> A(x-1) checks (x-1,1,TOP) < (x,0,TOP).
Both are valid when x>=0 and B calls A only when x!=0.

The verifier replaces a recursive call result with a fresh symbolic
value and assumes its postconditions on that call's execution path.
It proves the caller's own postconditions using these hypotheses.
All functions and all call VCs must be verified; SAT on any negated
VC means the module is not established correct.

For non-recursive functions with input x, precondition P, body E,
and postcondition Q_i:

    VC_i = P(x) => Q_i(x, E(x))

Noncyclic calls are handled modularly through the callee's contract.

## Execution and SMT-LIB export

    python -m tinyair examples/dafny_mutual_rank.air
    python -m tinyair examples/dafny_mutual_top.air --emit-smt2 smt-out
    python -m unittest discover -s tests -v

One SMT-LIB file per VC. Each asserts the negation of the VC.

- unsat -> PROVED (VC valid)
- sat -> FAILED (counterexample)
- unknown -> not proved

## Limitations

Only Int and Bool rank elements, no implicit Dafny call-graph
prefixes, no inferred decreases, and no advanced Dafny ranking
types. The verifier does not automatically determine whether
requires is satisfiable: contradictory preconditions can make
contract VCs vacuously valid. Adequate postconditions are needed
to claim behavior beyond termination.

## Experimental Tree datatype and source-driven verification

A special-purpose recursive tree datatype is now accepted at the top
of a TinyAIR module:

    data Tree = Empty | Node(Bool, Tree, Int, Tree)

It is a real custom-language AST representation, not a Python snippet
inside a .air file. The example examples/red_black_tree.air implements
balancing, insertion and membership with TinyAIR functions.

The Tree source backend supports constructors Empty/Node, selectors
empty/red/color/left/right/value, and the rank size(t). Special
contract operations valid(t), has(t, x) and preserves(result, t, x)
are available for the red-black invariant specification.

Use:

    python -m tinyair examples/red_black_tree.air --max-nodes 4 --emit-smt2 smt-out/rbt-air

The Tree module is symbolically *executed* from its parsed AST over
all feasible red-black shapes/colorings through the specified bound,
using unbounded symbolic keys. The generated Z3 VCs cover invariants,
set-preserving insertion, membership, and structural recursion.

This extension is deliberately limited: only the shown Tree
datatype declaration is accepted, not arbitrary algebraic datatypes.
No fully general induction mechanism or unbounded RB-tree proof is
claimed. The ordinary Int/Bool module verifier remains the backend for
all previous .air source files. See docs/RED_BLACK_TREE.md.
