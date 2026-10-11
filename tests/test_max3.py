"""Symbolic verification tests for the maximum of three integers."""

from pathlib import Path
import unittest

from tinyair.parser import parse_program
from tinyair.verification import generate_conditions, verify

EXAMPLE = Path(__file__).resolve().parents[1] / "examples" / "max3.air"


class MaxThreeTests(unittest.TestCase):
    def test_max3_proves_all_four_postconditions(self):
        source = EXAMPLE.read_text(encoding="utf-8")
        program = parse_program(source)
        self.assertEqual(program.parameters, ("a", "b", "c"))
        compiled = generate_conditions(program)
        results = verify(compiled)
        self.assertEqual(len(results), 4)
        self.assertEqual([result.status for result in results], ["PROVED"] * 4)

    def test_wrong_max3_produces_counterexample(self):
        source = """
        max3 :: Int -> Int -> Int -> Int
        ensures result >= a && result >= b && result >= c
        max3 a b c = a
        """
        results = verify(generate_conditions(parse_program(source)))
        self.assertEqual(results[0].status, "FAILED")
        self.assertIsNotNone(results[0].counterexample)


if __name__ == "__main__":
    unittest.main()
