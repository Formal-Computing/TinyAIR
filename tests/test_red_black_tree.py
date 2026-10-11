"""Runtime and bounded-SMT regression tests for immutable red-black insertion."""

import random
import unittest

import z3

from tinyair.red_black_tree import (
    Node, check_invariants, contains, inorder, insert,
)
from tinyair.red_black_vc import obligations


class RedBlackTests(unittest.TestCase):
    def test_all_permutations_up_to_six_keys(self):
        from itertools import permutations
        for count in range(7):
            for permutation in permutations(range(count)):
                tree = None
                for key in permutation:
                    tree = insert(tree, key)
                    check_invariants(tree)
                self.assertEqual(list(inorder(tree)), list(range(count)))

    def test_deterministic_randomized_inserts(self):
        rng = random.Random(7331)
        for trial in range(20):
            values = [rng.randint(-100, 100) for _ in range(80)]
            tree = None
            seen = set()
            for value in values:
                previous = tree
                tree = insert(tree, value)
                seen.add(value)
                check_invariants(tree)
                self.assertEqual(list(inorder(tree)), sorted(seen))
                self.assertTrue(contains(tree, value))
                if previous is not None:
                    check_invariants(previous)
            self.assertFalse(contains(tree, 9999))

    def test_duplicate_is_idempotent(self):
        tree = None
        for value in (10, 5, 15, 5, 15, 10, -3, -3):
            tree = insert(tree, value)
            check_invariants(tree)
        self.assertEqual(list(inorder(tree)), [-3, 5, 10, 15])

    def test_invariant_checker_rejects_violations(self):
        examples = [
            Node(True, None, 1, None),  # nonblack root
            Node(False, Node(True, Node(True, None, 1, None), 2, None), 3, None),
            Node(False, Node(False, None, 4, None), 3, None),
            Node(False, Node(False, None, 1, None), 3, None),
        ]
        for tree in examples:
            with self.assertRaises(AssertionError):
                check_invariants(tree)

    def test_symbolic_vcs_for_small_trees(self):
        count = 0
        for name, vc in obligations(2):
            solver = z3.Solver()
            solver.add(z3.Not(vc))
            self.assertEqual(solver.check(), z3.unsat, name)
            count += 1
        self.assertGreater(count, 0)


if __name__ == "__main__":
    unittest.main()
