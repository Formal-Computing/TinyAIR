"""Integration tests for the parser, type checks, and Z3 verification."""

import unittest

from tinyair.errors import ParseError, TypeCheckError
from tinyair.parser import parse_program
from tinyair.verification import generate_conditions, verify


def statuses(source: str) -> list[str]:
    return [r.status for r in verify(generate_conditions(parse_program(source)))]


class ParserTests(unittest.TestCase):
    def test_basic_structure(self):
        program = parse_program("""
        max :: Int -> Int -> Int
        requires True
        ensures result >= a && result >= b
        max a b = if a >= b then a else b
        """)
        self.assertEqual(program.name, "max")
        self.assertEqual(program.parameters, ("a", "b"))
        self.assertEqual(program.parameter_types, ("Int", "Int"))

    def test_wrong_parameter_count(self):
        with self.assertRaises(ParseError):
            parse_program("""
            f :: Int -> Int -> Int
            ensures result == x
            f x = x
            """)

    def test_unrecognized_token(self):
        with self.assertRaises(ParseError):
            parse_program("""
            f :: Int -> Int
            ensures result == x @ 3
            f x = x
            """)


class VerificationTests(unittest.TestCase):
    def test_correct_max(self):
        self.assertEqual(statuses("""
        max :: Int -> Int -> Int
        ensures result >= a && result >= b
        ensures result == a || result == b
        max a b = if a >= b then a else b
        """), ["PROVED", "PROVED"])

    def test_incorrect_max_yields_counterexample(self):
        compiled = generate_conditions(parse_program("""
        max :: Int -> Int -> Int
        ensures result >= a && result >= b
        max a b = if a >= b then b else a
        """))
        result = verify(compiled)[0]
        self.assertEqual(result.status, "FAILED")
        self.assertIsNotNone(result.counterexample)

    def test_precondition_matters(self):
        self.assertEqual(statuses("""
        f :: Int -> Int
        requires x >= 0
        ensures result >= 0
        f x = x
        """), ["PROVED"])
        self.assertEqual(statuses("""
        f :: Int -> Int
        ensures result >= 0
        f x = x
        """), ["FAILED"])

    def test_boolean_and_conditional(self):
        self.assertEqual(statuses("""
        choose :: Bool -> Int -> Int -> Int
        ensures result == a || result == b
        choose flag a b = if flag then a else b
        """), ["PROVED"])

    def test_let_binding(self):
        self.assertEqual(statuses("""
        double :: Int -> Int
        ensures result == 2 * x
        double x = let y = x + x in y
        """), ["PROVED"])

    def test_arithmetic_precedence_and_zero_arguments(self):
        self.assertEqual(statuses("""
        seven :: Int
        ensures result == 7
        seven = 1 + 2 * 3
        """), ["PROVED"])

    def test_wrong_return_type(self):
        with self.assertRaises(TypeCheckError):
            generate_conditions(parse_program("""
            f :: Int -> Int
            ensures result == x
            f x = x >= 0
            """))

    def test_wrong_condition_type(self):
        with self.assertRaises(TypeCheckError):
            generate_conditions(parse_program("""
            f :: Int -> Int
            ensures result == 3
            f x = if x then 3 else 4
            """))


if __name__ == "__main__":
    unittest.main()
