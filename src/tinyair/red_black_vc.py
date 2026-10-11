"""Z3 bounded exhaustive shape verification for immutable RB-tree insertion.

Enumerate all binary-tree SHAPES and colorings through max_nodes. Each
shape uses unconstrained symbolic integer keys and a symbolic inserted key.
For every valid prestate, Z3 must show preservation of RB invariants,
membership, and exact set contents. This is NOT a full unbounded proof.
"""

import argparse
from dataclasses import dataclass
from functools import lru_cache
from pathlib import Path

import z3


@dataclass(frozen=True)
class SNode:
    red: bool
    left: object
    key: z3.ArithRef
    right: object


@lru_cache(maxsize=None)
def shapes(nodes):
    if nodes == 0:
        return (None,)
    return tuple(
        (left, right)
        for left_count in range(nodes)
        for left in shapes(left_count)
        for right in shapes(nodes - left_count - 1)
    )


def colorings(shape):
    if shape is None:
        yield None
        return
    lshape, rshape = shape
    for left in colorings(lshape):
        for right in colorings(rshape):
            for red in (False, True):
                yield (red, left, right)


def symbolize(shape, keys, counter):
    if shape is None:
        return None
    red, left, right = shape
    # In-order symbolic names are convenient for counterexample inspection.
    l = symbolize(left, keys, counter)
    key = z3.Int(f"k{counter[0]}")
    counter[0] += 1
    keys.append(key)
    r = symbolize(right, keys, counter)
    return SNode(red, l, key, r)


def red(t):
    return t is not None and t.red


def balance(is_red, l, k, r):
    if not is_red:
        if red(l) and red(l.left):
            x = l.left
            return SNode(True, SNode(False, x.left, x.key, x.right), l.key,
                         SNode(False, l.right, k, r))
        if red(l) and red(l.right):
            x = l.right
            return SNode(True, SNode(False, l.left, l.key, x.left), x.key,
                         SNode(False, x.right, k, r))
        if red(r) and red(r.left):
            x = r.left
            return SNode(True, SNode(False, l, k, x.left), x.key,
                         SNode(False, x.right, r.key, r.right))
        if red(r) and red(r.right):
            x = r.right
            return SNode(True, SNode(False, l, k, r.left), r.key,
                         SNode(False, x.left, x.key, x.right))
    return SNode(is_red, l, k, r)


def insert_symbolic(t, k):
    if t is None:
        return SNode(True, None, k, None)
    left = insert_symbolic(t.left, k)
    right = insert_symbolic(t.right, k)
    # use expressions as symbolic ITE trees, not Python if on z3 expressions.
    return if_node(k < t.key, balance(t.red, left, t.key, t.right),
                   if_node(k > t.key, balance(t.red, t.left, t.key, right), t))


@dataclass(frozen=True)
class Choice:
    condition: z3.BoolRef
    yes: object
    no: object


def if_node(cond, a, b):
    return Choice(cond, a, b)


def expand_insert(t, key):
    """Enumerate guards for each possible BST insertion path."""
    if t is None:
        yield z3.BoolVal(True), SNode(True, None, key, None)
        return
    for guard, left in expand_insert(t.left, key):
        yield z3.And(key < t.key, guard), balance(t.red, left, t.key, t.right)
    for guard, right in expand_insert(t.right, key):
        yield z3.And(key > t.key, guard), balance(t.red, t.left, t.key, right)
    yield key == t.key, t


def blacken(t):
    return SNode(False, t.left, t.key, t.right)


def items(t):
    if t is None:
        return []
    return items(t.left) + [t.key] + items(t.right)


def structural(t):
    """Return Z3 validity, black height, min/max constraints."""
    if t is None:
        return z3.BoolVal(True), z3.IntVal(0)
    lv, lh = structural(t.left)
    rv, rh = structural(t.right)
    ordered = []
    for x in items(t.left):
        ordered.append(x < t.key)
    for x in items(t.right):
        ordered.append(t.key < x)
    if t.red:
        ordered.append(z3.BoolVal(not red(t.left) and not red(t.right)))
    return z3.And(lv, rv, lh == rh, *ordered), lh + (0 if t.red else 1)


def set_preserved(before, after, inserted):
    """Equality of finite contents as mathematical sets, including duplicates."""
    old = items(before)
    new = items(after)
    keys = old + new + [inserted]
    return z3.And(*[
        z3.Or(*[candidate == x for x in new])
        ==
        z3.Or(*[candidate == x for x in old + [inserted]])
        for candidate in keys
    ])


def obligations(max_nodes: int):
    for size in range(max_nodes + 1):
        for shape in shapes(size):
            for coloring in colorings(shape):
                keys = []
                tree = symbolize(coloring, keys, [0])
                valid, _ = structural(tree)
                if tree is not None and tree.red:
                    continue
                new_key = z3.Int("inserted")
                for path_index, (path, candidate) in enumerate(expand_insert(tree, new_key)):
                    result = blacken(candidate)
                    valid_after, _ = structural(result)
                    post = z3.And(
                        valid_after,
                        set_preserved(tree, result, new_key),
                        z3.BoolVal(not result.red),
                    )
                    description = (
                        f"RB insertion n={size}, color={coloring}, path={path_index}"
                    )
                    yield description, z3.Implies(z3.And(valid, path), post)


def run(max_nodes: int, output: Path, timeout_ms: int):
    output.mkdir(parents=True, exist_ok=True)
    count = proved = unknown = failures = 0
    for description, vc in obligations(max_nodes):
        count += 1
        solver = z3.Solver()
        solver.set(timeout=timeout_ms)
        solver.add(z3.Not(vc))
        target = output / f"rbt_insert_vc{count:05d}.smt2"
        target.write_text(
            f"; {description}\n; BOUNDED shape/color proof obligation\n"
            + solver.to_smt2(), encoding="utf-8"
        )
        result = solver.check()
        if result == z3.unsat:
            proved += 1
        elif result == z3.unknown:
            unknown += 1
            print("UNKNOWN", description, solver.reason_unknown())
        else:
            failures += 1
            print("FAILED", description, solver.model())
    print(f"Bounded RB insertion: {count} VCs, {proved} PROVED, "
          f"{failures} FAILED, {unknown} UNKNOWN")
    print(f"SMT-LIB: {output}")
    return 0 if count > 0 and failures == 0 and unknown == 0 else 1


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-nodes", type=int, default=3)
    parser.add_argument("--emit-smt2", type=Path, default=Path("smt-out/rbt"))
    parser.add_argument("--timeout", type=int, default=3000)
    args = parser.parse_args()
    if args.max_nodes < 0 or args.max_nodes > 5:
        parser.error("--max-nodes must be 0..5 (exponential enumeration)")
    raise SystemExit(run(args.max_nodes, args.emit_smt2, args.timeout))


if __name__ == "__main__":
    main()
