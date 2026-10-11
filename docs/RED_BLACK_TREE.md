# Red-black tree: TinyAIR source and Z3 verification

## Actual custom-language example

The runnable TinyAIR program lives at:

    examples/red_black_tree.air

It declares the experimental recursive Tree datatype:

    data Tree = Empty | Node(Bool, Tree, Int, Tree)

The constructor's Boolean color uses True = Red, False = Black.
The implementation contains these TinyAIR functions:

    rotLL, rotLR, rotRL, rotRR
    balance, ins, blacken, insert, contains

The public insertion contract is:

    insert :: Tree -> Int -> Tree
    requires valid(t)
    ensures valid(result)
    ensures has(result, x)
    ensures preserves(result, t, x)
    insert t x = blacken(ins(t, x))

All rotation, branching, recursive insertion and search logic is
written in the .air file, not delegated to Python's insert function.

### Experimental Tree language primitives

    Empty                       empty constructor
    Node(isRed, left, key, right) tree constructor
    empty(tree)                 True iff Empty
    red(tree)                   True iff red Node; False for Empty
    color(tree)                 node color (nonempty tree)
    left(tree)                  left subtree (nonempty tree)
    right(tree)                 right subtree (nonempty tree)
    value(tree)                 node key (nonempty tree)
    size(tree)                  structural node count; Int
    valid(tree)                 RB invariants and BST ordering
    has(tree, key)              set membership
    preserves(new, old, key)    old set + key exactly equals new set

Empty/selectors must be guarded by empty/red checks. The parser
supports exactly this Tree datatype declaration, alongside
ordinary Int/Bool functions; it does not yet implement general ADTs.
The one-line function definition restriction still applies.

## Source-driven symbolic checking

Invoke the existing TinyAIR CLI (NOT the standalone Python checker):

    python -m tinyair examples/red_black_tree.air --max-nodes 4 --emit-smt2 smt-out/rbt-air

The CLI parses the actual .air functions into ASTs. A symbolic evaluator
executes that AST over every valid bounded red-black tree input shape,
coloring, insertion path and search path. Every original tree key and
the inserted/searched key are Z3 unbounded symbolic integers.

Generated VCs enforce:
- original prestate satisfies valid(t)
- insert preserves black root, no red/red, equal black height, BST order
- inserted key belongs to result
- result's set is exactly original set union the new key
- contains implements symbolic membership
- recursion calls to ins/contains decrease size(t)

One independent negated VC is exported for each feasible source path.
The filename is red_black_tree_vc00001.smt2, etc.

For max-nodes=4, the observed source-driven verification has
128 VCs, all PROVED (UNSAT for every negated VC).
This smaller count than the independent checker is expected: invalid
input colorings/shapes and impossible symbolic branch paths are pruned.

THIS IS BOUNDED VERIFICATION. Symbolic integer keys are universal, but
the initial tree shape is bounded to 4 nodes. This does not prove insertion
correct for every tree of arbitrary size. For an unbounded proof we still
need datatype induction and balance-preservation lemmas.

## Independent Python implementation and checker

The original (separate) implementation remains at:
    src/tinyair/red_black_tree.py

Its independent shape enumerator is:
    src/tinyair/red_black_vc.py

Its SMT-LIB files go to:
    smt-out/rbt/

The independent Python checker previously proved 1,172 VCs through 4
nodes, including many vacuous prestate cases. These do not substitute
for verification of the .air source. The new source-driven backend is:
    src/tinyair/tree_language.py

The tests/test_tree_language.py suite directly interprets .air trees,
compares their exact shapes/colors to the Python version for many
insertion permutations, and checks that intentionally corrupting
rotations or search causes the symbolic verifier to find a counterexample.

## Commands

    python -m tinyair examples/red_black_tree.air --max-nodes 4 --emit-smt2 smt-out/rbt-air
    python -m unittest discover -s tests -v

A successful bounded run is evidence for the specified depth, not
a universal statement about all future inputs.
