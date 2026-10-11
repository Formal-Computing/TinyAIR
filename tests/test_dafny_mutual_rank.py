"""Dafny's A(x)->B(x)->A(x-1): a phase-sensitive ranking proof."""

from pathlib import Path
import unittest

import z3

from tinyair.module_verification import (
    generate_module_conditions, verify_module,
)
from tinyair.parser import parse_module
from tinyair.verification import make_solver


EXAMPLES = Path(__file__).resolve().parents[1] / "examples"


def load(name):
    return generate_module_conditions(
        parse_module((EXAMPLES / name).read_text(encoding="utf-8"))
    )


class DafnyMutualRankTests(unittest.TestCase):
    def test_phase_sensitive_ranks_prove_both_functions(self):
        results = verify_module(load("dafny_mutual_rank.air"))
        self.assertEqual(tuple(results), ("A", "B"))
        for result in results.values():
            self.assertEqual([r.status for r in result], ["PROVED"] * 5)

    def test_same_rank_for_both_functions_is_insufficient(self):
        results = verify_module(load("dafny_mutual_naive.air"))
        a_results = results["A"]
        b_results = results["B"]
        failure = next(
            result for result in a_results
            if "strictly decreases" in result.condition.description
        )
        self.assertEqual(failure.status, "FAILED")
        self.assertIsNotNone(failure.counterexample)
        self.assertEqual(
            next(
                r.status for r in b_results
                if "strictly decreases" in r.condition.description
            ),
            "PROVED",
        )

    def test_exported_conditions_are_valid_smtlib(self):
        for function in load("dafny_mutual_rank.air").functions:
            for condition in function.conditions:
                solver = z3.Solver()
                solver.from_string(make_solver(condition).to_smt2())
                self.assertEqual(solver.check(), z3.unsat)

    def test_no_call_at_b_zero(self):
        results = verify_module(load("dafny_mutual_rank.air"))
        self.assertTrue(
            all(r.status == "PROVED" for rs in results.values() for r in rs)
        )


if __name__ == "__main__":
    unittest.main()
