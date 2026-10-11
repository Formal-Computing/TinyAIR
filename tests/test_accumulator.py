"""A two-parameter recursion example exercises argument parsing and induction."""

from pathlib import Path
import unittest

from tinyair.parser import parse_program
from tinyair.verification import generate_conditions, verify


class AccumulatorTests(unittest.TestCase):
    def test_tail_recursive_sum_with_two_arguments(self):
        file = (
            Path(__file__).resolve().parents[1] / "examples" / "sum_accumulator.air"
        )
        program = parse_program(file.read_text(encoding="utf-8"))
        self.assertEqual(program.parameters, ("n", "acc"))
        results = verify(generate_conditions(program))
        self.assertEqual(len(results), 5)
        self.assertEqual([r.status for r in results], ["PROVED"] * 5)


if __name__ == "__main__":
    unittest.main()
