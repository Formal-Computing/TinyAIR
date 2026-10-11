"""Dafny-inspired well-founded lexicographic decreases tuple ordering.

Rank components supported by TinyAIR: Int and Bool. An implicit top (TOP)
is appended to every rank; TOP is strictly above any concrete component.
Dafny has additional sorts/prefix rules that are outside this subset.
"""

import z3

from .errors import TypeCheckError


def compile_rank(expressions, environment, compile_expr):
    """Type-check a rank and produce a tuple of Z3 expressions."""
    if not expressions:
        raise TypeCheckError("decreases must contain at least one expression")
    terms = tuple(compile_expr(expr, environment) for expr in expressions)
    for index, term in enumerate(terms, 1):
        if term.sort() not in (z3.IntSort(), z3.BoolSort()):
            raise TypeCheckError(
                f"decreases component {index} must be Int or Bool, not {term.sort()}"
            )
    return terms


def rank_nonnegative(rank):
    """Conservative legacy entry check on the first integer component.

    Integer comparison itself uses Dafny's well-founded relation requiring
    the *caller*'s decreasing integer component to be nonnegative. Lower
    tuple components need not be globally nonnegative if earlier ones drop.
    """
    first = rank[0]
    return first >= 0 if first.sort() == z3.IntSort() else z3.BoolVal(True)


def lexicographic_less(callee, caller):
    """Return Z3 formula: (callee, TOP) <_lex (caller, TOP).

    For integers, a well-founded decrease is a < b AND b >= 0; a may be
    negative on a terminating last step. For booleans, False < True.
    At any position, a real callee component is strictly below TOP.
    """
    same_prefix = z3.BoolVal(True)
    disjuncts = []
    for i in range(max(len(callee), len(caller))):
        if i >= len(callee):
            # Callee has TOP while caller has an ordinary component:
            # TOP < ordinary is never true.
            break
        if i >= len(caller):
            # Callee has an ordinary component and caller has TOP.
            disjuncts.append(same_prefix)
            break
        left, right = callee[i], caller[i]
        if left.sort() != right.sort():
            raise TypeCheckError(
                f"incompatible decreases components {i+1}: "
                f"callee {left.sort()}, caller {right.sort()}"
            )
        if left.sort() == z3.IntSort():
            smaller = z3.And(left < right, right >= 0)
        elif left.sort() == z3.BoolSort():
            smaller = z3.And(z3.Not(left), right)
        else:
            raise TypeCheckError(f"unsupported decreases type {left.sort()}")
        disjuncts.append(z3.And(same_prefix, smaller))
        same_prefix = z3.And(same_prefix, left == right)
    return z3.Or(*disjuncts)
