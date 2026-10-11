"""The TinyAIR .air tree program is parsed, executed, and symbolically checked.

These tests verify the source controls behavior (fault injection), rather
than silently invoking the independent Python RB insertion algorithm.
"""

from itertools import permutations
from pathlib import Path
import unittest

import z3

from tinyair.errors import LanguageError, ParseError, TypeCheckError
from tinyair.parser import parse_module
from tinyair.red_black_tree import (
    Node, check_invariants, inorder, insert as python_insert,
)
from tinyair.tree_language import (
    SymbolicEvaluator, generate_tree_vcs, verify_tree_module,
)


SOURCE = Path(__file__).resolve().parents[1] / "examples" / "red_black_tree.air"


def concrete(node):
    if node is None:
        return None
    return Node(node.red, concrete(node.left), node.key.as_long(),
                concrete(node.right))


class TreeLanguageTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.source = SOURCE.read_text(encoding="utf-8")
        cls.module = parse_module(cls.source)

    def test_declared_tree_datatype_and_functions(self):
        self.assertEqual(self.module.data_types, ("Tree",))
        names = [f.name for f in self.module.functions]
        self.assertEqual(
            names,
            ["rotLL", "rotLR", "rotRL", "rotRR", "balance",
             "ins", "blacken", "insert", "contains"],
        )

    def test_small_symbolic_source_driven_vcs(self):
        self.assertEqual(
            verify_tree_module(self.module, max_nodes=2, timeout_ms=1000),
            0,
        )

    def test_concrete_interpretation_agrees_with_python(self):
        for permutation in permutations(range(5)):
            symbolic_tree = None
            python_tree = None
            for key in permutation:
                engine = SymbolicEvaluator(self.module, ())
                symbolic_tree = engine.invoke(
                    "insert", [symbolic_tree, z3.IntVal(key)]
                )
                self.assertEqual(engine.guards, [])
                python_tree = python_insert(python_tree, key)
                observed = concrete(symbolic_tree)
                check_invariants(observed)
                self.assertEqual(list(inorder(observed)),
                                 list(inorder(python_tree)))
                # Full tree shape/color equality, not just inorder keys.
                self.assertEqual(observed, python_tree)
                for search in range(-1, 6):
                    engine = SymbolicEvaluator(self.module, ())
                    found = engine.invoke(
                        "contains", [symbolic_tree, z3.IntVal(search)]
                    )
                    self.assertIsInstance(found, bool)
                    self.assertEqual(found, search in set(permutation[:permutation.index(key)+1]))

    def test_corrupted_rotation_causes_z3_counterexample(self):
        original = next(
            line for line in self.source.splitlines()
            if line.startswith("rotLL l k r = ")
        )
        damaged = self.source.replace(
            original,
            "rotLL l k r = Node(True, l, k, r)",
        )
        altered = parse_module(damaged)
        failed = False
        for condition in generate_tree_vcs(altered, 3):
            solver = z3.Solver()
            solver.add(z3.Not(condition.formula))
            if solver.check() == z3.sat:
                failed = True
                break
        self.assertTrue(failed, "Faulty rotation must violate a generated VC")

    def test_wrong_search_function_is_detected(self):
        original = next(
            line for line in self.source.splitlines()
            if line.startswith("contains t x = ")
        )
        altered = parse_module(
            self.source.replace(original, "contains t x = False")
        )
        failure = False
        for condition in generate_tree_vcs(altered, 1):
            solver = z3.Solver()
            solver.add(z3.Not(condition.formula))
            if solver.check() == z3.sat:
                failure = True
                break
        self.assertTrue(failure, "Incorrect contains must fail its contract")

    def test_missing_recursion_measure_is_rejected(self):
        altered = parse_module(
            self.source.replace("decreases size(t)", "")
        )
        with self.assertRaisesRegex(TypeCheckError, "decreases"):
            list(generate_tree_vcs(altered, 1))

    def test_contract_weakening_is_not_silently_accepted(self):
        altered = parse_module(
            self.source.replace(
                "ensures preserves(result, t, x)",
                "ensures True",
            )
        )
        with self.assertRaisesRegex(TypeCheckError, "ensures"):
            list(generate_tree_vcs(altered, 1))

    def test_unsupported_datatype_is_reported(self):
        with self.assertRaises(ParseError):
            parse_module(
                self.source.replace(
                    "data Tree = Empty | Node(Bool, Tree, Int, Tree)",
                    "data Tree = Empty | Node(Int, Tree, Int, Tree)",
                )
            )


if __name__ == "__main__":
    unittest.main()
