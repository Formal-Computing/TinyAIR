"""Regression tests for modular contracts and mutual recursion."""

from pathlib import Path
import unittest

import z3

from tinyair.errors import ParseError, TypeCheckError
from tinyair.module_verification import (
    generate_module_conditions, verify_module,
)
from tinyair.parser import parse_module
from tinyair.verification import make_solver


EXAMPLES = Path(__file__).resolve().parents[1] / "examples"


def compile_source(source: str):
    return generate_module_conditions(parse_module(source))


def check(source: str):
    return verify_module(compile_source(source))


class ModuleTests(unittest.TestCase):
    def test_parse_two_functions(self):
        module = parse_module((EXAMPLES / "mutual_count.air").read_text())
        self.assertEqual([f.name for f in module.functions], ["evenCount", "oddCount"])
        self.assertEqual([len(f.parameters) for f in module.functions], [1, 1])

    def test_single_function_still_supported_as_module(self):
        results = check((EXAMPLES / "max3.air").read_text())
        self.assertEqual(list(results), ["max3"])
        self.assertEqual([r.status for r in results["max3"]], ["PROVED"] * 4)

    def test_mutual_recursion_with_exact_postconditions(self):
        results = check((EXAMPLES / "mutual_count.air").read_text())
        self.assertEqual(
            [r.status for r in results["evenCount"]], ["PROVED"] * 5
        )
        self.assertEqual(
            [r.status for r in results["oddCount"]], ["PROVED"] * 5
        )

    def test_boolean_mutual_recursion(self):
        results = check((EXAMPLES / "even_odd.air").read_text())
        self.assertEqual(len(results), 2)
        for values in results.values():
            self.assertEqual([r.status for r in values], ["PROVED"] * 7)

    def test_bad_mutual_cycle_rejected(self):
        results = check((EXAMPLES / "bad_mutual_cycle.air").read_text())
        for values in results.values():
            bad = [r for r in values if r.status == "FAILED"]
            self.assertTrue(any("strictly decreases" in r.condition.description for r in bad))
            self.assertTrue(any(r.counterexample is not None for r in bad))

    def test_mutual_cycle_missing_measure(self):
        src = """
        a :: Int -> Int
        requires n >= 0
        decreases n
        ensures result == 0
        a n = if n == 0 then 0 else b(n - 1)

        b :: Int -> Int
        requires n >= 0
        ensures result == 0
        b n = if n == 0 then 0 else a(n - 1)
        """
        with self.assertRaisesRegex(TypeCheckError, "decreases"):
            compile_source(src)

    def test_nested_acyclic_calls_no_measure(self):
        results = check((EXAMPLES / "forward_calls.air").read_text())
        self.assertEqual([r.status for r in results["twice"]], ["PROVED"] * 3)
        self.assertEqual([r.status for r in results["inc"]], ["PROVED"])

    def test_call_precondition_failure(self):
        src = """
        source :: Int -> Int
        requires n >= 0
        ensures result >= 0
        source n = target(n - 1)

        target :: Int -> Int
        requires n >= 0
        ensures result == n
        target n = n
        """
        result = check(src)["source"]
        self.assertEqual(result[0].status, "FAILED")
        self.assertIn("precondition", result[0].condition.description)

    def test_callee_postcondition_must_be_verified_too(self):
        src = """
        caller :: Int -> Int
        ensures result == x
        caller x = broken(x)

        broken :: Int -> Int
        ensures result == x
        broken x = x + 1
        """
        results = check(src)
        self.assertEqual(results["caller"][-1].status, "PROVED")
        self.assertEqual(results["broken"][-1].status, "FAILED")

    def test_acyclic_calls_keep_callee_contracts(self):
        src = """
        caller :: Int -> Bool
        ensures result == (n >= 0)
        caller n = positive(n)

        positive :: Int -> Bool
        ensures result == (n >= 0)
        positive n = n >= 0
        """
        for values in check(src).values():
            self.assertTrue(all(r.status == "PROVED" for r in values))

    def test_three_function_cycle(self):
        src = """
        a :: Int -> Int
        requires n >= 0
        decreases n
        ensures result == n
        a n = if n == 0 then 0 else 1 + b(n - 1)

        b :: Int -> Int
        requires n >= 0
        decreases n
        ensures result == n
        b n = if n == 0 then 0 else 1 + c(n - 1)

        c :: Int -> Int
        requires n >= 0
        decreases n
        ensures result == n
        c n = if n == 0 then 0 else 1 + a(n - 1)
        """
        results = check(src)
        self.assertEqual(len(results), 3)
        self.assertTrue(all(r.status == "PROVED" for values in results.values() for r in values))

    def test_unreachable_bad_edge_is_vacuous(self):
        src = """
        a :: Int -> Int
        requires n >= 0
        decreases n
        ensures result == n
        a n = if True then n else b(n)

        b :: Int -> Int
        requires n >= 0
        decreases n
        ensures result == n
        b n = if True then n else a(n)
        """
        self.assertTrue(all(
            r.status == "PROVED" for values in check(src).values() for r in values
        ))

    def test_duplicate_name_rejected(self):
        with self.assertRaisesRegex(ParseError, "Duplicate"):
            parse_module("""
            f :: Int -> Int
            ensures result == n
            f n = n

            f :: Int -> Int
            ensures result == n + 1
            f n = n + 1
            """)

    def test_undeclared_function_rejected(self):
        with self.assertRaisesRegex(TypeCheckError, "Unknown function"):
            compile_source("""
            f :: Int -> Int
            ensures result == n
            f n = missing(n)
            """)

    def test_wrong_arity_rejected(self):
        with self.assertRaisesRegex(TypeCheckError, "expects 1 arguments"):
            compile_source("""
            f :: Int -> Int
            ensures result == n
            f n = g(n, n)

            g :: Int -> Int
            ensures result == n
            g n = n
            """)

    def test_wrong_argument_sort_rejected(self):
        with self.assertRaisesRegex(TypeCheckError, "expects Int"):
            compile_source("""
            f :: Int -> Int
            ensures result == n
            f n = g(True)

            g :: Int -> Int
            ensures result == n
            g n = n
            """)

    def test_unknown_functions_in_preconditions_rejected(self):
        with self.assertRaisesRegex(TypeCheckError, "Calls are only allowed"):
            compile_source("""
            f :: Int -> Int
            requires g(n) >= 0
            ensures result == n
            f n = n

            g :: Int -> Int
            ensures result == n
            g n = n
            """)

    def test_invalid_contract_in_uncalled_function_rejected(self):
        with self.assertRaises(TypeCheckError):
            compile_source("""
            valid :: Int -> Int
            ensures result == x
            valid x = x

            invalid :: Int -> Int
            ensures result + True == 2
            invalid x = x
            """)

    def test_exported_smtlib_is_valid(self):
        compiled = compile_source(
            (EXAMPLES / "mutual_count.air").read_text()
        )
        for function in compiled.functions:
            for condition in function.conditions:
                solver = z3.Solver()
                solver.from_string(make_solver(condition).to_smt2())
                self.assertEqual(solver.check(), z3.unsat)

    def test_empty_module_rejected(self):
        with self.assertRaises(ParseError):
            parse_module("-- nothing\n")


if __name__ == "__main__":
    unittest.main()
