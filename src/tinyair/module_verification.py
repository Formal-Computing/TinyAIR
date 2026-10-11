"""Modular contract verification with well-founded mutual recursion.

The call graph partitions functions into recursive components. Calls inside
one component must strictly decrease a shared natural-number rank; calls
outside the component rely on their independently verified contracts.
Every function and every call obligation must be proved before accepting
a module. No finite-depth recursive unfolding is used.
"""

from dataclasses import dataclass

import z3

from .errors import TypeCheckError
from .rank import compile_rank, lexicographic_less, rank_nonnegative
from .syntax import (
    Binary, Call, Conditional, Function, Let, Module, Unary,
)
from .verification import (
    CompiledProgram, VerificationCondition, _require_sort,
    compile_expr, verify,
)


def called_functions(expr) -> set[str]:
    """All statically referenced functions (including nested calls)."""
    if isinstance(expr, Call):
        result = {expr.name}
        for arg in expr.arguments:
            result.update(called_functions(arg))
        return result
    if isinstance(expr, Unary):
        return called_functions(expr.operand)
    if isinstance(expr, Binary):
        return called_functions(expr.left) | called_functions(expr.right)
    if isinstance(expr, Conditional):
        return (
            called_functions(expr.condition)
            | called_functions(expr.when_true)
            | called_functions(expr.when_false)
        )
    if isinstance(expr, Let):
        return called_functions(expr.value) | called_functions(expr.body)
    return set()


@dataclass(frozen=True)
class CompiledModule:
    functions: tuple[CompiledProgram, ...]


def generate_module_conditions(module: Module) -> CompiledModule:
    """Generate VCs for all functions, including mutually recursive cycles."""
    definitions = {function.name: function for function in module.functions}
    if len(definitions) != len(module.functions):
        raise TypeCheckError("Duplicate function definitions")
    if not module.functions:
        raise TypeCheckError("Empty module")

    graph = {
        name: called_functions(function.body)
        for name, function in definitions.items()
    }
    for caller, callees in graph.items():
        for callee in callees:
            if callee not in definitions:
                raise TypeCheckError(
                    f"Unknown function {callee!r}, called from {caller!r}"
                )

    def reach(name: str) -> set[str]:
        found: set[str] = set()
        pending = list(graph[name])
        while pending:
            next_name = pending.pop()
            if next_name in found:
                continue
            found.add(next_name)
            pending.extend(graph[next_name])
        return found

    reachable = {name: reach(name) for name in definitions}
    # Every path inside a recursive SCC has to strictly reduce its rank.
    recursive = {name for name in definitions if name in reachable[name]}
    for name in recursive:
        if definitions[name].decreases is None:
            raise TypeCheckError(
                f"Recursive function {name!r} requires a 'decreases' clause"
            )

    compiled = []
    for function in module.functions:
        caller = function.name
        symbols = {
            name: z3.Int(name) if type_name == "Int" else z3.Bool(name)
            for name, type_name in zip(
                function.parameters, function.parameter_types
            )
        }
        preconditions = [
            compile_expr(expr, symbols) for expr in function.requires
        ]
        for condition in preconditions:
            _require_sort(condition, "Bool", "requires clause")
        pre = z3.And(*preconditions)

        # Validate contracts even when the function is never called.
        post_symbol = (
            z3.Int("result") if function.return_type == "Int"
            else z3.Bool("result")
        )
        for clause in function.ensures:
            _require_sort(
                compile_expr(clause, {**symbols, "result": post_symbol}),
                "Bool", f"{caller} ensures clause"
            )

        measure = None
        obligations: list[tuple[str, z3.BoolRef]] = []
        if function.decreases is not None:
            measure = compile_rank(function.decreases, symbols, compile_expr)
            obligations.append((
                "decreases is nonnegative",
                z3.Implies(pre, rank_nonnegative(measure))
            ))

        assumptions: list[z3.BoolRef] = []
        call_number = 0

        def on_call(callee_name: str, args: tuple[z3.ExprRef, ...],
                    path: z3.BoolRef) -> z3.ExprRef:
            nonlocal call_number
            callee = definitions[callee_name]
            if len(args) != len(callee.parameters):
                raise TypeCheckError(
                    f"{callee_name} expects {len(callee.parameters)} "
                    f"arguments, got {len(args)}"
                )
            for arg, type_name in zip(args, callee.parameter_types):
                _require_sort(arg, type_name, f"{callee_name} argument")

            call_number += 1
            callee_env = dict(zip(callee.parameters, args))
            premise = z3.And(pre, *assumptions, path)
            callee_pre = z3.And(*(
                compile_expr(clause, callee_env)
                for clause in callee.requires
            ))
            obligations.append((
                f"call {call_number} -> {callee_name}: precondition",
                z3.Implies(premise, callee_pre),
            ))

            # callee -> ... -> caller closes a call-graph cycle.
            if caller in reachable[callee_name]:
                if measure is None or callee.decreases is None:
                    raise TypeCheckError(
                        "Every member of a recursive cycle needs 'decreases'"
                    )
                callee_measure = compile_rank(
                    callee.decreases, callee_env, compile_expr
                )
                obligations.append((
                    f"call {call_number} -> {callee_name}: "
                    "decreases nonnegative",
                    z3.Implies(premise, rank_nonnegative(callee_measure)),
                ))
                obligations.append((
                    f"call {call_number} -> {callee_name}: strictly decreases",
                    z3.Implies(premise, lexicographic_less(callee_measure, measure)),
                ))

            result = (
                z3.FreshInt(f"{callee_name}_result_")
                if callee.return_type == "Int"
                else z3.FreshBool(f"{callee_name}_result_")
            )
            # Callee contracts may be used only where the call executes.
            # All their correctness + termination obligations are checked
            # in this same compiled module, not assumed from unchecked code.
            for guarantee in callee.ensures:
                condition = compile_expr(
                    guarantee, {**callee_env, "result": result}
                )
                _require_sort(
                    condition, "Bool", f"{callee_name} ensures clause"
                )
                assumptions.append(z3.Implies(path, condition))
            return result

        body = compile_expr(function.body, symbols, on_call=on_call)
        _require_sort(body, function.return_type, f"{caller} body")
        premise = z3.And(pre, *assumptions)
        for index, guarantee in enumerate(function.ensures, 1):
            post = compile_expr(
                guarantee, {**symbols, "result": body}
            )
            _require_sort(post, "Bool", f"{caller} ensures clause {index}")
            obligations.append((
                f"postcondition {index}", z3.Implies(premise, post)
            ))

        conditions = tuple(
            VerificationCondition(index, formula, description)
            for index, (description, formula)
            in enumerate(obligations, 1)
        )
        compiled.append(CompiledProgram(function, symbols, conditions))
    return CompiledModule(tuple(compiled))


def verify_module(module: CompiledModule, timeout_ms: int = 5000):
    """Return per-function Z3 results; every VC is needed for success."""
    return {
        compiled.function.name: verify(compiled, timeout_ms=timeout_ms)
        for compiled in module.functions
    }
