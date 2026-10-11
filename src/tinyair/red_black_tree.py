"""Immutable functional red-black integer set (Okasaki-style insertion).

Only insertion, membership, and inorder traversal are supported.
Deletion is intentionally not included; it needs an independent proof.
"""

from dataclasses import dataclass
from typing import Iterator, TypeAlias

RED = True
BLACK = False


@dataclass(frozen=True, slots=True)
class Node:
    red: bool
    left: "Tree"
    key: int
    right: "Tree"


Tree: TypeAlias = Node | None


def is_red(t: Tree) -> bool:
    return t is not None and t.red


def balance(red: bool, left: Tree, key: int, right: Tree) -> Node:
    """Repair the four red/red configurations below a BLACK root."""
    if not red:
        if is_red(left) and is_red(left.left):
            # Black (Red (Red a x b) y c) z d
            a = left.left
            return Node(
                RED, Node(BLACK, a.left, a.key, a.right), left.key,
                Node(BLACK, left.right, key, right),
            )
        if is_red(left) and is_red(left.right):
            # Black (Red a x (Red b y c)) z d
            a = left.right
            return Node(
                RED, Node(BLACK, left.left, left.key, a.left), a.key,
                Node(BLACK, a.right, key, right),
            )
        if is_red(right) and is_red(right.left):
            # Black a x (Red (Red b y c) z d)
            a = right.left
            return Node(
                RED, Node(BLACK, left, key, a.left), a.key,
                Node(BLACK, a.right, right.key, right.right),
            )
        if is_red(right) and is_red(right.right):
            # Black a x (Red b y (Red c z d))
            a = right.right
            return Node(
                RED, Node(BLACK, left, key, right.left), right.key,
                Node(BLACK, a.left, a.key, a.right),
            )
    return Node(red, left, key, right)


def _insert(tree: Tree, key: int) -> Node:
    """Recursive insertion; may temporarily violate red-root/red-child rule."""
    if tree is None:
        return Node(RED, None, key, None)
    if key < tree.key:
        return balance(tree.red, _insert(tree.left, key), tree.key, tree.right)
    if key > tree.key:
        return balance(tree.red, tree.left, tree.key, _insert(tree.right, key))
    return tree  # Sets: repeated insertion leaves the same value and ordering.


def insert(tree: Tree, key: int) -> Node:
    """Return a new fully valid red-black tree containing key."""
    candidate = _insert(tree, key)
    if candidate.red:
        return Node(BLACK, candidate.left, candidate.key, candidate.right)
    return candidate


def contains(tree: Tree, key: int) -> bool:
    while tree is not None:
        if key == tree.key:
            return True
        tree = tree.left if key < tree.key else tree.right
    return False


def inorder(tree: Tree) -> Iterator[int]:
    if tree is None:
        return
    yield from inorder(tree.left)
    yield tree.key
    yield from inorder(tree.right)


def black_height(tree: Tree) -> int:
    """Convention: empty leaf has black height 0."""
    if tree is None:
        return 0
    return black_height(tree.left) + (not tree.red)


def check_invariants(tree: Tree) -> None:
    """Runtime checker used in tests (not a substitute for Z3 proofs)."""
    if tree is not None and tree.red:
        raise AssertionError("Root must be black")

    def walk(node: Tree, lower: int | None, upper: int | None) -> int:
        if node is None:
            return 0
        if lower is not None and not lower < node.key:
            raise AssertionError(f"BST lower bound violated at {node.key}")
        if upper is not None and not node.key < upper:
            raise AssertionError(f"BST upper bound violated at {node.key}")
        if node.red and (is_red(node.left) or is_red(node.right)):
            raise AssertionError(f"Red/red violation at {node.key}")
        left_height = walk(node.left, lower, node.key)
        right_height = walk(node.right, node.key, upper)
        if left_height != right_height:
            raise AssertionError(f"Black-height violation at {node.key}")
        return left_height + (not node.red)

    walk(tree, None, None)
