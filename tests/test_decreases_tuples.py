"""Regression tests for Dafny-like lexicographic decreases tuples."""

from pathlib import Path
import unittest

import z3

from tinyair.errors import ParseError, TypeCheckError
from tinyair.parser import parse_decreases, parse_module, parse_program
from tinyair.module_verification import generate_module_conditions, verify_module
from tinyair.rank import lexicographic_less
from tinyair.verification import generate_conditions, verify, make_solver


EXAMPLES = Path(__file__).resolve().parents[1] / "examples"


def module_results(file):
    source = (EXAMPLES / file).read_text(encoding="utf-8")
    return verify_module(generate_module_conditions(parse_module(source)))


class TupleRankTests(unittest.TestCase):
    def test_dafny_a_b_integer_phase(self):
        result = module_results("dafny_mutual_rank.air")
        for values in result.values():
            self.assertEqual([x.status for x in values], ["PROVED"] * 5)

    def test_dafny_implicit_top(self):
        result = module_results("dafny_mutual_top.air")
        for values in result.values():
            self.assertEqual([x.status for x in values], ["PROVED"] * 5)

    def test_dafny_boolean_phase_and_parentheses(self):
        result = module_results("dafny_mutual_bool.air")
        for values in result.values():
            self.assertEqual([x.status for x in values], ["PROVED"] * 5)

    def test_two_variable_lexicographic_rank(self):
        result = module_results("lexicographic_two_args.air")
        self.assertEqual(
            [x.status for x in result["countDown"]], ["PROVED"] * 8
        )

    def test_non_decreasing_tuple_fails(self):
        result = module_results("lexicographic_bad_tie.air")["stuck"]
        violations = [
            x for x in result if x.status == "FAILED"
            and "strictly decreases" in x.condition.description
        ]
        self.assertEqual(len(violations), 1)
        self.assertIsNotNone(violations[0].counterexample)

    def test_original_naive_scalar_rank_still_fails(self):
        result = module_results("dafny_mutual_naive.air")["A"]
        self.assertEqual(result[3].status, "FAILED")

    def test_tuple_parser_splits_top_level_only(self):
        self.assertEqual(len(parse_decreases("x, 1")), 2)
        self.assertEqual(len(parse_decreases("(x, 1)")), 2)
        self.assertEqual(len(parse_decreases("x, (y + 1)")), 2)
        self.assertEqual(len(parse_decreases("(x, (y + 1))")), 2)
        self.assertEqual(len(parse_decreases("(x + 1)")), 1)

    def test_multiple_decreases_clauses_concatenated(self):
        program = parse_program("""
        f :: Int -> Int
        decreases x
        decreases 1, True
        ensures result == x
        f x = x
        """)
        self.assertEqual(len(program.decreases), 3)
        self.assertEqual(len(verify(generate_conditions(program))), 2)

    def test_scalar_remains_one_component(self):
        source = (EXAMPLES / "factorial.air").read_text(encoding="utf-8")
        parsed = parse_program(source)
        self.assertEqual(len(parsed.decreases), 1)
        self.assertEqual([r.status for r in verify(generate_conditions(parsed))], ["PROVED"] * 6)

    def test_reject_empty_tuple_elements(self):
        for clause in ("x,", ",x", "x,,1", "()", "(x,)"):
            with self.subTest(clause=clause):
                with self.assertRaises(ParseError):
                    parse_decreases(clause)

    def test_nonnegative_prefix_and_bool_phase(self):
        module = parse_module("""
        p :: Bool -> Int
        decreases b
        ensures result == 0
        p b = if b then p(False) else 0
        """)
        result = verify_module(generate_module_conditions(module))["p"]
        self.assertTrue(all(r.status == "PROVED" for r in result))

    def test_lex_comparator_implicit_top(self):
        x = z3.Int("x")
        caller = (x,)
        callee = (x, z3.IntVal(0))
        formula = lexicographic_less(callee, caller)
        s = z3.Solver()
        s.add(z3.Not(formula))
        self.assertEqual(s.check(), z3.unsat)
        s = z3.Solver()
        s.add(lexicographic_less(caller, callee))
        self.assertEqual(s.check(), z3.unsat)

    def test_lex_comparator_first_component_dominates(self):
        x = z3.Int("x")
        m = z3.Int("m")
        # Later component gets bigger, but first decreases.
        clause = lexicographic_less((x - 1, m + 100), (x, m))
        solver = z3.Solver()
        solver.add(x >= 1, z3.Not(clause))
        self.assertEqual(solver.check(), z3.unsat)

    def test_nonnegative_on_active_integer_comparison(self):
        caller = (z3.IntVal(0), z3.IntVal(-1))
        callee = (z3.IntVal(0), z3.IntVal(-2))
        s = z3.Solver()
        s.add(lexicographic_less(callee, caller))
        self.assertEqual(s.check(), z3.unsat)

    def test_negative_unused_tail_is_permitted(self):
        source = """
        f :: Int -> Int
        requires n >= 0
        decreases n, -100
        ensures result == 0
        f n = if n == 0 then 0 else f(n - 1)
        """
        result = verify(generate_conditions(parse_program(source)))
        self.assertTrue(all(r.status == "PROVED" for r in result))

    def test_reject_incompatible_tuple_component_sorts(self):
        source = """
        a :: Int -> Int
        requires n >= 0
        decreases n, True
        ensures result == 0
        a n = if n == 0 then 0 else b(n - 1)

        b :: Int -> Int
        requires n >= 0
        decreases n, 1
        ensures result == 0
        b n = if n == 0 then 0 else a(n - 1)
        """
        with self.assertRaisesRegex(TypeCheckError, "incompatible decreases"):
            generate_module_conditions(parse_module(source))

    def test_exported_dafny_tuple_vcs(self):
        program = generate_module_conditions(
            parse_module((EXAMPLES / "dafny_mutual_rank.air").read_text(encoding="utf-8"))
        )
        for function in program.functions:
            for condition in function.conditions:
                solver = z3.Solver()
                solver.from_string(make_solver(condition).to_smt2())
                self.assertEqual(solver.check(), z3.unsat)


if __name__ == "__main__":
    unittest.main()
