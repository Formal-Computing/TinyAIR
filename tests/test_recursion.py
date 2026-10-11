"""Recursive total-correctness regression tests (Z3 checks validity, not samples)."""

from pathlib import Path
import unittest

from tinyair.errors import ParseError, TypeCheckError
from tinyair.parser import parse_program
from tinyair.verification import generate_conditions, verify


EXAMPLES = Path(__file__).resolve().parents[1] / "examples"


def check_source(source: str):
    return verify(generate_conditions(parse_program(source)))


class RecursionTests(unittest.TestCase):
    def test_factorial(self):
        results = check_source((EXAMPLES / "factorial.air").read_text())
        self.assertEqual(len(results), 6)
        self.assertTrue(all(x.status == "PROVED" for x in results))

    def test_arithmetic_series_exact_contract(self):
        results = check_source((EXAMPLES / "sum_to.air").read_text())
        self.assertEqual(len(results), 5)
        self.assertTrue(all(x.status == "PROVED" for x in results))

    def test_two_recursive_calls(self):
        results = check_source((EXAMPLES / "fibonacci.air").read_text())
        self.assertEqual(len(results), 8)
        self.assertTrue(all(x.status == "PROVED" for x in results))

    def test_self_call_does_not_terminate(self):
        results = check_source((EXAMPLES / "bad_recursion.air").read_text())
        failures = [r for r in results if r.status == "FAILED"]
        self.assertEqual(len(failures), 1)
        self.assertIn("strictly decreases", failures[0].condition.description)
        self.assertIsNotNone(failures[0].counterexample)

    def test_missing_decreases_not_accepted(self):
        source = """
        f :: Int -> Int
        requires n >= 0
        ensures result >= 0
        f n = if n == 0 then 0 else f(n - 1)
        """
        with self.assertRaisesRegex(TypeCheckError, "decreases"):
            generate_conditions(parse_program(source))

    def test_missing_nonnegative_domain_not_accepted(self):
        source = """
        f :: Int -> Int
        decreases n
        ensures result >= 0
        f n = if n <= 0 then 0 else f(n - 1)
        """
        results = check_source(source)
        self.assertEqual(results[0].status, "FAILED")
        self.assertIn("nonnegative", results[0].condition.description)

    def test_invalid_recursive_call_precondition(self):
        source = """
        f :: Int -> Int
        requires n >= 0
        decreases n
        ensures result >= 0
        f n = if n == 0 then 0 else f(n - 2)
        """
        results = check_source(source)
        failures = [r.condition.description for r in results if r.status == "FAILED"]
        self.assertIn("call 1: precondition", failures)

    def test_invalid_postcondition_not_provable(self):
        source = """
        f :: Int -> Int
        requires n >= 0
        decreases n
        ensures result == 0
        f n = if n == 0 then 1 else f(n - 1)
        """
        results = check_source(source)
        self.assertEqual(results[-1].status, "FAILED")

    def test_unknown_function_not_accepted(self):
        source = """
        f :: Int -> Int
        requires n >= 0
        decreases n
        ensures result >= 0
        f n = other(n)
        """
        with self.assertRaisesRegex(TypeCheckError, "Only calls"):
            generate_conditions(parse_program(source))

    def test_wrong_call_arity_not_accepted(self):
        source = """
        f :: Int -> Int
        requires n >= 0
        decreases n
        ensures result >= 0
        f n = f(n, n)
        """
        with self.assertRaisesRegex(TypeCheckError, "expects 1 arguments"):
            generate_conditions(parse_program(source))

    def test_wrong_call_type_not_accepted(self):
        source = """
        f :: Int -> Int
        requires n >= 0
        decreases n
        ensures result >= 0
        f n = f(True)
        """
        with self.assertRaisesRegex(TypeCheckError, "expects Int"):
            generate_conditions(parse_program(source))

    def test_no_recursive_calls_preserves_old_behavior(self):
        source = """
        f :: Int -> Int
        ensures result == n + 1
        f n = n + 1
        """
        self.assertEqual(
            [result.status for result in check_source(source)], ["PROVED"]
        )

    def test_parenthesized_haskell_like_call_with_whitespace(self):
        source = """
        f :: Int -> Int
        requires n >= 0
        decreases n
        ensures result == n
        f n = if n == 0 then 0 else 1 + f (n - 1)
        """
        self.assertTrue(all(r.status == "PROVED" for r in check_source(source)))

    def test_let_bound_recursive_result(self):
        source = """
        f :: Int -> Int
        requires n >= 0
        decreases n
        ensures result == n
        f n = if n == 0 then 0 else let y = f(n - 1) in 1 + y
        """
        self.assertTrue(all(r.status == "PROVED" for r in check_source(source)))

    def test_unreachable_recursive_call_does_not_require_decrease(self):
        source = """
        f :: Int -> Int
        requires n >= 0
        decreases n
        ensures result == 0
        f n = if True then 0 else f(n)
        """
        self.assertTrue(all(r.status == "PROVED" for r in check_source(source)))

    def test_short_circuit_recursion_uses_conditional_path(self):
        source = """
        allGood :: Int -> Bool
        requires n >= 0
        decreases n
        ensures result == True
        allGood n = n == 0 || allGood(n - 1)
        """
        self.assertTrue(all(r.status == "PROVED" for r in check_source(source)))

    def test_multiple_decreases_clauses_are_concatenated(self):
        function = parse_program("""
            f :: Int -> Int
            decreases n
            decreases n - 1
            ensures result == n
            f n = n
            """)
        self.assertEqual(len(function.decreases), 2)

    def test_calls_in_contracts_rejected(self):
        with self.assertRaisesRegex(TypeCheckError, "Calls are only allowed"):
            generate_conditions(parse_program("""
            f :: Int -> Int
            ensures result == f(n)
            f n = n
            """))


if __name__ == "__main__":
    unittest.main()
