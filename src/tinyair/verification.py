"""Sound contract-based verification of pure functions, including self-recursion.

Recursive calls are abstracted by fresh results. Only results of smaller,
precondition-satisfying calls may use the induction hypothesis (ensures).
All generated VCs must be proved for a program to be considered verified.
"""

from dataclasses import dataclass

import z3

from .errors import TypeCheckError
from .rank import compile_rank, lexicographic_less, rank_nonnegative
from .syntax import (
    Binary, BoolLiteral, Call, Conditional, Function, IntLiteral,
    Let, Unary, Variable,
)


def _sort_name(term: z3.ExprRef) -> str:
    return str(term.sort())


def _require_sort(term: z3.ExprRef, expected: str, context: str) -> None:
    if _sort_name(term) != expected:
        raise TypeCheckError(
            f"{context} expects {expected}, received {_sort_name(term)}"
        )


def compile_expr(expr, environment: dict[str, z3.ExprRef], *,
                 on_call=None, path=None) -> z3.ExprRef:
    """Symbolically evaluate one expression; path tracks conditional execution."""
    if path is None:
        path = z3.BoolVal(True)

    def visit(child, guard=path):
        return compile_expr(child, environment, on_call=on_call, path=guard)

    if isinstance(expr, IntLiteral):
        return z3.IntVal(expr.value)
    if isinstance(expr, BoolLiteral):
        return z3.BoolVal(expr.value)
    if isinstance(expr, Variable):
        if expr.name not in environment:
            raise TypeCheckError(f"Unknown variable {expr.name!r}")
        return environment[expr.name]

    if isinstance(expr, Let):
        bound = visit(expr.value)
        new_environment = {**environment, expr.name: bound}
        return compile_expr(expr.body, new_environment, on_call=on_call, path=path)

    if isinstance(expr, Unary):
        value = visit(expr.operand)
        if expr.op == "-":
            _require_sort(value, "Int", "Unary -")
            return -value
        _require_sort(value, "Bool", f"Unary {expr.op}")
        return z3.Not(value)

    if isinstance(expr, Binary):
        left = visit(expr.left)
        op = expr.op

        if op in ("&&", "and", "||", "or"):
            _require_sort(left, "Bool", op)
            # Termination obligations on the RHS only apply if it is evaluated.
            right_guard = z3.And(
                path, left if op in ("&&", "and") else z3.Not(left)
            )
            right = visit(expr.right, right_guard)
            _require_sort(right, "Bool", op)
            return z3.And(left, right) if op in ("&&", "and") else z3.Or(left, right)

        right = visit(expr.right)
        if op in ("+", "-", "*", "<", "<=", ">", ">="):
            _require_sort(left, "Int", op)
            _require_sort(right, "Int", op)
            return {
                "+": lambda: left + right,
                "-": lambda: left - right,
                "*": lambda: left * right,
                "<": lambda: left < right,
                "<=": lambda: left <= right,
                ">": lambda: left > right,
                ">=": lambda: left >= right,
            }[op]()

        if op in ("==", "!="):
            if left.sort() != right.sort():
                raise TypeCheckError("Equality requires operands of the same type")
            return left == right if op == "==" else left != right

        raise TypeCheckError(f"Unsupported operator {op!r}")

    if isinstance(expr, Conditional):
        condition = visit(expr.condition)
        _require_sort(condition, "Bool", "if condition")
        yes = visit(expr.when_true, z3.And(path, condition))
        no = visit(expr.when_false, z3.And(path, z3.Not(condition)))
        if yes.sort() != no.sort():
            raise TypeCheckError("Both branches of if must have the same type")
        return z3.If(condition, yes, no)

    if isinstance(expr, Call):
        if on_call is None:
            raise TypeCheckError("Calls are only allowed inside the function body")
        # Recursive argument expressions are processed before the outer call.
        args = tuple(visit(arg) for arg in expr.arguments)
        return on_call(expr.name, args, path)

    raise TypeCheckError(f"Unsupported expression: {type(expr).__name__}")


@dataclass(frozen=True)
class VerificationCondition:
    number: int
    formula: z3.BoolRef
    description: str = "postcondition"


@dataclass(frozen=True)
class VerificationResult:
    condition: VerificationCondition
    status: str
    counterexample: dict[str, str] | None = None
    reason: str | None = None


@dataclass(frozen=True)
class CompiledProgram:
    function: Function
    symbols: dict[str, z3.ExprRef]
    conditions: tuple[VerificationCondition, ...]


def generate_conditions(function: Function) -> CompiledProgram:
    """Create total-correctness VCs with a well-founded induction hypothesis."""
    symbols = {
        name: z3.Int(name) if type_name == "Int" else z3.Bool(name)
        for name, type_name in zip(function.parameters, function.parameter_types)
    }

    preconditions = [compile_expr(expr, symbols) for expr in function.requires]
    for clause in preconditions:
        _require_sort(clause, "Bool", "requires clause")
    pre = z3.And(*preconditions)

    measure = None
    conditions: list[tuple[str, z3.BoolRef]] = []
    if function.decreases is not None:
        measure = compile_rank(function.decreases, symbols, compile_expr)
        conditions.append((
            "decreases is nonnegative", z3.Implies(pre, rank_nonnegative(measure))
        ))

    assumptions: list[z3.BoolRef] = []
    call_index = 0

    def on_call(name: str, args: tuple[z3.ExprRef, ...], path: z3.BoolRef):
        nonlocal call_index
        if name != function.name:
            raise TypeCheckError(
                f"Only calls to the current function {function.name!r} are supported"
            )
        if len(args) != len(function.parameters):
            raise TypeCheckError(
                f"{name} expects {len(function.parameters)} arguments, got {len(args)}"
            )
        for value, type_name in zip(args, function.parameter_types):
            _require_sort(value, type_name, f"{name} argument")
        if measure is None:
            raise TypeCheckError(
                f"Recursive function {name!r} requires a 'decreases' clause"
            )

        call_index += 1
        call_env = dict(zip(function.parameters, args))
        invocation = z3.And(pre, *assumptions, path)
        callee_preconditions = [
            compile_expr(clause, call_env) for clause in function.requires
        ]
        callee_pre = z3.And(*callee_preconditions)
        callee_measure = compile_rank(function.decreases, call_env, compile_expr)
        conditions.append((
            f"call {call_index}: precondition",
            z3.Implies(invocation, callee_pre),
        ))
        conditions.append((
            f"call {call_index}: decreases nonnegative",
            z3.Implies(invocation, rank_nonnegative(callee_measure)),
        ))
        conditions.append((
            f"call {call_index}: strictly decreases",
            z3.Implies(invocation, lexicographic_less(callee_measure, measure)),
        ))

        if function.return_type == "Int":
            result = z3.FreshInt(f"{name}_recursive_result_")
        else:
            result = z3.FreshBool(f"{name}_recursive_result_")

        # Induction hypothesis: on a well-founded, valid recursive call,
        # the result satisfies every postcondition of this same function.
        for clause in function.ensures:
            post = compile_expr(clause, {**call_env, "result": result})
            _require_sort(post, "Bool", "recursive ensures clause")
            assumptions.append(z3.Implies(path, post))
        return result

    body = compile_expr(function.body, symbols, on_call=on_call)
    _require_sort(body, function.return_type, "Function body")

    premise = z3.And(pre, *assumptions)
    for index, guarantee in enumerate(function.ensures, start=1):
        post = compile_expr(guarantee, {**symbols, "result": body})
        _require_sort(post, "Bool", f"ensures clause {index}")
        conditions.append((
            f"postcondition {index}",
            z3.Implies(premise, post),
        ))

    vcs = tuple(
        VerificationCondition(i, formula, description)
        for i, (description, formula) in enumerate(conditions, 1)
    )
    return CompiledProgram(function, symbols, vcs)


def make_solver(condition: VerificationCondition, timeout_ms: int = 5000) -> z3.Solver:
    solver = z3.Solver()
    if timeout_ms > 0:
        solver.set(timeout=timeout_ms)
    solver.add(z3.Not(condition.formula))
    return solver


def verify(program: CompiledProgram, timeout_ms: int = 5000) -> list[VerificationResult]:
    """Only UNSAT of every negated VC establishes total correctness."""
    results = []
    for condition in program.conditions:
        solver = make_solver(condition, timeout_ms)
        status = solver.check()
        if status == z3.unsat:
            results.append(VerificationResult(condition, "PROVED"))
        elif status == z3.sat:
            model = solver.model()
            example = {
                name: str(model.eval(symbol, model_completion=True))
                for name, symbol in program.symbols.items()
            }
            results.append(VerificationResult(condition, "FAILED", example))
        else:
            results.append(VerificationResult(
                condition, "UNKNOWN", reason=solver.reason_unknown()
            ))
    return results
