"""TinyAIR Tree datatype interpreter and bounded symbolic source verification.

The source .air AST, not a Python copy of insertion, drives the evaluation.
All tree shapes/colorings up to a size bound and ALL integer keys are checked
via SMT-LIB. No claim of an unbounded inductive tree proof is made.

This is an intentionally limited experimental backend for Tree:
  data Tree = Empty | Node(Bool, Tree, Int, Tree)
  empty/red/color/left/right/value/size
  valid/has/preserves in contracts
"""

from dataclasses import dataclass
from pathlib import Path

import z3

from .errors import LanguageError, TypeCheckError
from .red_black_vc import (
    SNode, colorings, shapes, symbolize, structural, items, set_preserved,
)
from .syntax import Binary, BoolLiteral, Call, Conditional, IntLiteral, Let, Unary, Variable


class _BranchRequired(Exception):
    """The evaluator reached an unassigned symbolic conditional."""


def _bool(expr):
    if isinstance(expr, bool):
        return z3.BoolVal(expr)
    if isinstance(expr, z3.BoolRef):
        return expr
    raise TypeCheckError("Expected a Bool expression")


def _int(expr):
    if isinstance(expr, bool):
        raise TypeCheckError("Expected Int, got Bool")
    if isinstance(expr, int):
        return z3.IntVal(expr)
    if isinstance(expr, z3.ArithRef) and expr.sort() == z3.IntSort():
        return expr
    raise TypeCheckError("Expected an Int expression")


def _tree(expr):
    if expr is None or isinstance(expr, SNode):
        return expr
    raise TypeCheckError("Expected a Tree")


def _check_arity(name, args, n):
    if len(args) != n:
        raise TypeCheckError(f"{name} expects {n} arguments, got {len(args)}")


def _membership(tree, key):
    return z3.Or(*[entry == key for entry in items(tree)])


def _valid(tree):
    condition, _ = structural(tree)
    root_black = tree is None or not tree.red
    return z3.And(condition, z3.BoolVal(root_black))


class SymbolicEvaluator:
    """Execute the parsed TinyAIR AST with symbolic integer branch splitting."""

    def __init__(self, module, choices):
        self.functions = {f.name: f for f in module.functions}
        self.choices = choices
        self.consumed = 0
        self.guards = []
        self.termination = []
        self.call_stack = []
        self.remaining_calls = 2048

    def branch(self, value) -> bool:
        predicate = z3.simplify(_bool(value))
        if z3.is_true(predicate):
            return True
        if z3.is_false(predicate):
            return False
        if self.consumed >= len(self.choices):
            raise _BranchRequired()
        outcome = self.choices[self.consumed]
        self.consumed += 1
        self.guards.append(predicate if outcome else z3.Not(predicate))
        return outcome

    def builtin(self, name, args):
        if name == "Node":
            _check_arity(name, args, 4)
            color, l, value, r = args
            if not isinstance(color, bool):
                if z3.is_true(color):
                    color = True
                elif z3.is_false(color):
                    color = False
                else:
                    raise TypeCheckError("Symbolic node colors not implemented")
            return SNode(color, _tree(l), _int(value), _tree(r))
        if name in ("empty", "red", "color", "left", "right", "value", "size", "valid"):
            _check_arity(name, args, 1)
            node = _tree(args[0])
            if name == "empty":
                return node is None
            if name == "red":
                return node is not None and node.red
            if name == "size":
                return z3.IntVal(len(items(node)))
            if name == "valid":
                return _valid(node)
            if node is None:
                raise LanguageError(f"{name}(Empty) is undefined")
            return {
                "color": lambda: node.red,
                "left": lambda: node.left,
                "right": lambda: node.right,
                "value": lambda: node.key,
            }[name]()
        if name == "has":
            _check_arity(name, args, 2)
            return _membership(_tree(args[0]), _int(args[1]))
        if name == "preserves":
            _check_arity(name, args, 3)
            new, old, inserted = args
            return set_preserved(_tree(old), _tree(new), _int(inserted))
        return None

    def eval(self, expr, env):
        if isinstance(expr, IntLiteral):
            return z3.IntVal(expr.value)
        if isinstance(expr, BoolLiteral):
            return expr.value
        if isinstance(expr, Variable):
            if expr.name == "Empty":
                return None
            if expr.name not in env:
                raise TypeCheckError(f"Unbound variable {expr.name}")
            return env[expr.name]
        if isinstance(expr, Unary):
            value = self.eval(expr.operand, env)
            if expr.op == "-":
                return -_int(value)
            if expr.op in ("not", "!"):
                return z3.Not(_bool(value))
            raise TypeCheckError(f"Unsupported unary operator {expr.op}")
        if isinstance(expr, Binary):
            op = expr.op
            if op in ("&&", "and"):
                left = self.eval(expr.left, env)
                return self.eval(expr.right, env) if self.branch(left) else False
            if op in ("||", "or"):
                left = self.eval(expr.left, env)
                return True if self.branch(left) else self.eval(expr.right, env)

            left = self.eval(expr.left, env)
            right = self.eval(expr.right, env)
            if op == "+":
                return _int(left) + _int(right)
            if op == "-":
                return _int(left) - _int(right)
            if op == "*":
                return _int(left) * _int(right)
            if op == "<":
                return _int(left) < _int(right)
            if op == "<=":
                return _int(left) <= _int(right)
            if op == ">":
                return _int(left) > _int(right)
            if op == ">=":
                return _int(left) >= _int(right)
            if op in ("==", "!="):
                if isinstance(left, SNode) or isinstance(right, SNode):
                    raise TypeCheckError("Tree equality not implemented")
                relation = left == right
                return relation if op == "==" else z3.Not(_bool(relation))
            raise TypeCheckError(f"Unsupported binary operator {op}")
        if isinstance(expr, Conditional):
            condition = self.eval(expr.condition, env)
            next_expr = expr.when_true if self.branch(condition) else expr.when_false
            return self.eval(next_expr, env)
        if isinstance(expr, Let):
            new_env = dict(env)
            new_env[expr.name] = self.eval(expr.value, env)
            return self.eval(expr.body, new_env)
        if isinstance(expr, Call):
            arguments = [self.eval(arg, env) for arg in expr.arguments]
            if expr.name in {
                "Node", "empty", "red", "color", "left", "right",
                "value", "size", "valid", "has", "preserves",
            }:
                return self.builtin(expr.name, arguments)
            return self.invoke(expr.name, arguments)
        raise TypeCheckError(f"Unknown expression AST: {type(expr).__name__}")

    def invoke(self, name, args):
        if name not in self.functions:
            raise TypeCheckError(f"Undeclared function: {name}")
        function = self.functions[name]
        _check_arity(name, args, len(function.parameters))
        if self.remaining_calls <= 0:
            raise LanguageError("Function evaluation exceeded recursion safety limit")
        self.remaining_calls -= 1
        env = dict(zip(function.parameters, args))

        # This backend type-checks each call dynamically on a symbolic shape,
        # with declared sorts required for all evaluated function arguments.
        for type_name, value in zip(function.parameter_types, args):
            if type_name == "Int":
                _int(value)
            elif type_name == "Bool":
                _bool(value)
            elif type_name == "Tree":
                _tree(value)
            else:
                raise TypeCheckError(f"Unknown type {type_name}")

        for ancestor, ancestor_env in self.call_stack:
            if ancestor.name == name:
                if function.decreases is None:
                    raise TypeCheckError(f"Recursive {name} must declare decreases")
                if len(function.decreases) != 1:
                    raise TypeCheckError("Tree recursion currently requires one Int measure")
                old_rank = self.eval(ancestor.decreases[0], ancestor_env)
                new_rank = self.eval(function.decreases[0], env)
                self.termination.append(z3.And(
                    _int(old_rank) >= 0,
                    _int(new_rank) >= 0,
                    _int(new_rank) < _int(old_rank),
                ))
                break
        self.call_stack.append((function, env))
        try:
            result = self.eval(function.body, env)
        finally:
            self.call_stack.pop()

        if function.return_type == "Int":
            _int(result)
        elif function.return_type == "Bool":
            _bool(result)
        elif function.return_type == "Tree":
            _tree(result)
        return result


@dataclass(frozen=True)
class TreeVC:
    description: str
    formula: z3.BoolRef


def _is_call(expr, name):
    if isinstance(expr, Call):
        return expr.name == name
    return False


def _validate_module(module):
    if module.data_types != ("Tree",):
        raise TypeCheckError("Tree backend requires the Tree datatype declaration")
    functions = {fn.name: fn for fn in module.functions}
    if "insert" not in functions or "contains" not in functions:
        raise TypeCheckError("Tree example needs insert and contains functions")
    insert = functions["insert"]
    contains = functions["contains"]
    if (insert.parameter_types, insert.return_type) != (("Tree", "Int"), "Tree"):
        raise TypeCheckError("insert must have type Tree -> Int -> Tree")
    if (contains.parameter_types, contains.return_type) != (("Tree", "Int"), "Bool"):
        raise TypeCheckError("contains must have type Tree -> Int -> Bool")

    required = {"valid", "has", "preserves"}
    found = {clause.name for clause in insert.ensures if isinstance(clause, Call)}
    if not required.issubset(found):
        raise TypeCheckError("insert must declare ensures valid/has/preserves")
    return functions


def generate_tree_vcs(module, max_nodes=3):
    """Yield VCs compiled FROM TinyAIR source for all bounded tree structures."""
    _validate_module(module)
    for node_count in range(max_nodes + 1):
        for shape in shapes(node_count):
            for coloring in colorings(shape):
                tree = symbolize(coloring, [], [0])
                # Invalid prestate shapes contribute no useful verification VCs.
                prestate = _valid(tree)
                feasible = z3.Solver()
                feasible.add(prestate)
                if feasible.check() != z3.sat:
                    continue
                search = z3.Int("query")

                for func_name in ("insert", "contains"):
                    function = {fn.name: fn for fn in module.functions}[func_name]
                    pending = [()]
                    path_number = 0
                    while pending:
                        choices = pending.pop()
                        evaluator = SymbolicEvaluator(module, choices)
                        try:
                            outcome = evaluator.invoke(func_name, [tree, search])
                            if evaluator.consumed != len(choices):
                                raise LanguageError("Unexpected surplus branch decisions")
                            guard = z3.And(prestate, *evaluator.guards)
                            feasible_path = z3.Solver()
                            feasible_path.add(guard)
                            if feasible_path.check() != z3.sat:
                                continue
                            env = {**dict(zip(function.parameters, [tree, search])),
                                   "result": outcome}
                            requires = z3.And(*[
                                _bool(evaluator.eval(clause, env))
                                for clause in function.requires
                            ])
                            postconditions = [
                                _bool(evaluator.eval(clause, env))
                                for clause in function.ensures
                            ]
                            post = z3.And(*postconditions, *evaluator.termination)
                            vc = z3.Implies(z3.And(guard, requires), post)
                            path_number += 1
                            yield TreeVC(
                                f"{func_name} n={node_count} colors={coloring} "
                                f"path={path_number} source=red_black_tree.air",
                                vc,
                            )
                        except _BranchRequired:
                            pending.append(choices + (False,))
                            pending.append(choices + (True,))


def verify_tree_module(module, *, max_nodes=3, output=None, timeout_ms=3000):
    """Export source-driven negated VCs and classify every Z3 check."""
    _validate_module(module)
    if max_nodes < 0 or max_nodes > 5:
        raise ValueError("max_nodes must be between 0 and 5")
    if output is not None:
        output = Path(output)
        output.mkdir(parents=True, exist_ok=True)

    totals = {"PROVED": 0, "FAILED": 0, "UNKNOWN": 0}
    count = 0
    for count, condition in enumerate(generate_tree_vcs(module, max_nodes), start=1):
        solver = z3.Solver()
        solver.set(timeout=timeout_ms)
        solver.add(z3.Not(condition.formula))
        if output is not None:
            destination = output / f"red_black_tree_vc{count:05}.smt2"
            destination.write_text(
                f"; {condition.description}\n"
                "; Source-driven, finite tree shape bound; NOT an unbounded proof\n"
                + solver.to_smt2(), encoding="utf-8",
            )
        status = solver.check()
        if status == z3.unsat:
            totals["PROVED"] += 1
        elif status == z3.sat:
            totals["FAILED"] += 1
            print(f"FAILED {condition.description}: {solver.model()}")
        else:
            totals["UNKNOWN"] += 1
            print(f"UNKNOWN {condition.description}: {solver.reason_unknown()}")

    print(f"TinyAIR Tree source: {count} bounded VCs, "
          f"{totals['PROVED']} PROVED, {totals['FAILED']} FAILED, "
          f"{totals['UNKNOWN']} UNKNOWN; max prestate nodes={max_nodes}")
    if output is not None:
        print(f"SMT-LIB output: {output}")
    if count == 0:
        raise LanguageError("Tree verifier generated no VCs")
    return 0 if totals["FAILED"] == 0 and totals["UNKNOWN"] == 0 else 1
