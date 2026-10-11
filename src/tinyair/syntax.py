"""AST for the pure expression-based TinyAIR language."""

from dataclasses import dataclass


@dataclass(frozen=True)
class IntLiteral:
    value: int


@dataclass(frozen=True)
class BoolLiteral:
    value: bool


@dataclass(frozen=True)
class Variable:
    name: str


@dataclass(frozen=True)
class Unary:
    op: str
    operand: "Expr"


@dataclass(frozen=True)
class Binary:
    op: str
    left: "Expr"
    right: "Expr"


@dataclass(frozen=True)
class Conditional:
    condition: "Expr"
    when_true: "Expr"
    when_false: "Expr"


@dataclass(frozen=True)
class Let:
    name: str
    value: "Expr"
    body: "Expr"


@dataclass(frozen=True)
class Call:
    name: str
    arguments: tuple["Expr", ...]


Expr = IntLiteral | BoolLiteral | Variable | Unary | Binary | Conditional | Let | Call


@dataclass(frozen=True)
class Function:
    name: str
    parameters: tuple[str, ...]
    parameter_types: tuple[str, ...]
    return_type: str
    body: Expr
    requires: tuple[Expr, ...]
    ensures: tuple[Expr, ...]
    decreases: tuple[Expr, ...] | None = None


@dataclass(frozen=True)
class Module:
    """Sequence of functions, including mutually recursive definitions."""
    functions: tuple[Function, ...]
    data_types: tuple[str, ...] = ()
