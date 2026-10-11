"""TinyAIR Pratt parser: expressions, contracts, and a single function."""

import re
from dataclasses import dataclass

from .errors import ParseError
from .syntax import (
    Binary, BoolLiteral, Call, Conditional, Function, IntLiteral, Let,
    Unary, Variable,
)

_TOKEN = re.compile(r"\s+|\d+|>=|<=|==|!=|&&|\|\||[A-Za-z_]\w*|[,()+*<>=!-]")
_IDENTIFIER = re.compile(r"[A-Za-z_]\w*\Z")
_SIGNATURE = re.compile(r"([A-Za-z_]\w*)\s*::\s*(.+)\Z")
_DEFINITION = re.compile(
    r"([A-Za-z_]\w*)(?:\s+([A-Za-z_]\w*(?:\s+[A-Za-z_]\w*)*))?\s*=\s*(.+)\Z"
)
_PRECEDENCE = {
    "||": 1, "or": 1,
    "&&": 2, "and": 2,
    "==": 3, "!=": 3,
    "<": 4, "<=": 4, ">": 4, ">=": 4,
    "+": 5, "-": 5, "*": 6,
}
_RESERVED = {
    "if", "then", "else", "let", "in", "True", "False",
    "true", "false", "and", "or", "not", "result",
    "requires", "ensures", "decreases",
}


@dataclass(frozen=True)
class Token:
    text: str
    position: int


def tokenize(expression: str) -> list[Token]:
    tokens = []
    position = 0
    while position < len(expression):
        match = _TOKEN.match(expression, position)
        if match is None:
            raise ParseError(
                f"Unexpected character {expression[position]!r} at column {position + 1}"
            )
        if not match.group().isspace():
            tokens.append(Token(match.group(), position))
        position = match.end()
    tokens.append(Token("<end>", len(expression)))
    return tokens


class ExpressionParser:
    def __init__(self, expression: str):
        self.tokens = tokenize(expression)
        self.index = 0

    def current(self) -> str:
        return self.tokens[self.index].text

    def take(self) -> str:
        token = self.current()
        self.index += 1
        return token

    def expect(self, token: str) -> None:
        if self.current() != token:
            raise ParseError(f"Expected {token!r}, found {self.current()!r}")
        self.take()

    def parse(self):
        result = self.expression()
        if self.current() != "<end>":
            raise ParseError(f"Unexpected token {self.current()!r}")
        return result

    def expression(self, min_precedence: int = 0):
        left = self.prefix()
        while self.current() in _PRECEDENCE:
            op = self.current()
            precedence = _PRECEDENCE[op]
            if precedence < min_precedence:
                break
            self.take()
            right = self.expression(precedence + 1)
            left = Binary(op, left, right)
        return left

    def prefix(self):
        token = self.take()

        if token == "if":
            condition = self.expression()
            self.expect("then")
            when_true = self.expression()
            self.expect("else")
            when_false = self.expression()
            return Conditional(condition, when_true, when_false)

        if token == "let":
            name = self.take()
            if not _IDENTIFIER.fullmatch(name) or name in _RESERVED:
                raise ParseError(f"Invalid let variable {name!r}")
            self.expect("=")
            value = self.expression()
            self.expect("in")
            return Let(name, value, self.expression())

        if token in ("-", "!", "not"):
            return Unary(token, self.expression(7))

        if token == "(":
            inside = self.expression()
            self.expect(")")
            return inside

        if token.isdecimal():
            return IntLiteral(int(token))

        if token in ("True", "true", "False", "false"):
            return BoolLiteral(token in ("True", "true"))

        if _IDENTIFIER.fullmatch(token) and (
            token not in _RESERVED or token == "result"
        ):
            # Both fact(n - 1) and fact (n - 1) are accepted.
            if self.current() == "(":
                self.take()
                arguments = []
                if self.current() != ")":
                    arguments.append(self.expression())
                    while self.current() == ",":
                        self.take()
                        arguments.append(self.expression())
                self.expect(")")
                return Call(token, tuple(arguments))
            return Variable(token)

        raise ParseError(f"Expected expression, found {token!r}")


def parse_expression(text: str):
    return ExpressionParser(text).parse()



def parse_decreases(text: str) -> tuple:
    """Read a Dafny-style expression list, e.g. x, 1 or (x, True).

    A pair of enclosing parentheses is accepted as alternative tuple syntax.
    Commas nested in parentheses do not split components.
    """
    text = text.strip()
    if not text:
        raise ParseError("decreases requires an expression")

    # Optionally remove one set of parentheses enclosing the entire list.
    if text.startswith("(") and text.endswith(")"):
        depth = 0
        enclosing = False
        for i, char in enumerate(text):
            if char == "(":
                depth += 1
            elif char == ")":
                depth -= 1
                if depth < 0:
                    raise ParseError("Unmatched ')' in decreases")
                if depth == 0:
                    enclosing = (i == len(text) - 1)
                    break
        if enclosing:
            text = text[1:-1].strip()

    parts = []
    depth = 0
    start = 0
    for i, char in enumerate(text):
        if char == "(":
            depth += 1
        elif char == ")":
            depth -= 1
            if depth < 0:
                raise ParseError("Unmatched ')' in decreases")
        elif char == "," and depth == 0:
            parts.append(text[start:i].strip())
            start = i + 1
    if depth != 0:
        raise ParseError("Unclosed '(' in decreases")
    parts.append(text[start:].strip())
    if any(not part for part in parts):
        raise ParseError("Empty decreases tuple component")
    return tuple(parse_expression(part) for part in parts)


def parse_program(source: str, allowed_types: tuple[str, ...] = ("Int", "Bool")) -> Function:
    """Parse a single pure function with optional termination measure."""
    lines = [line.split("--", 1)[0].strip() for line in source.splitlines()]
    lines = [line for line in lines if line]
    if not lines:
        raise ParseError("Empty source file")

    signature = _SIGNATURE.fullmatch(lines[0])
    if signature is None:
        raise ParseError("First statement must be 'name :: Int -> ... -> Int'")
    name, signature_text = signature.groups()
    if name in _RESERVED:
        raise ParseError(f"Reserved function name {name!r}")
    types = tuple(part.strip() for part in signature_text.split("->"))
    if not types or any(t not in allowed_types for t in types):
        raise ParseError(f"Unsupported signature type; allowed: {allowed_types}")

    preconditions, postconditions = [], []
    definition = None
    decreases = []
    for line in lines[1:]:
        if line.startswith("requires "):
            preconditions.append(parse_expression(line[len("requires "):]))
        elif line.startswith("ensures "):
            postconditions.append(parse_expression(line[len("ensures "):]))
        elif line.startswith("decreases "):
            decreases.extend(parse_decreases(line[len("decreases "):]))
        else:
            match = _DEFINITION.fullmatch(line)
            if match is None or definition is not None:
                raise ParseError(f"Invalid or duplicate function definition: {line}")
            definition = match

    if definition is None:
        raise ParseError(f"Missing definition for {name}")
    if not postconditions:
        raise ParseError("At least one ensures clause is required")

    defined_name, parameter_text, body_text = definition.groups()
    if defined_name != name:
        raise ParseError(f"Signature is for {name}, definition is for {defined_name}")
    parameters = tuple(parameter_text.split()) if parameter_text else ()
    if len(parameters) != len(types) - 1:
        raise ParseError(
            f"Expected {len(types) - 1} parameters, got {len(parameters)}"
        )
    if len(set(parameters)) != len(parameters):
        raise ParseError("Duplicate parameter name")
    if any(parameter in _RESERVED or parameter == name for parameter in parameters):
        raise ParseError("Reserved/conflicting parameter name")

    return Function(
        name=name,
        parameters=parameters,
        parameter_types=types[:-1],
        return_type=types[-1],
        body=parse_expression(body_text),
        requires=tuple(preconditions),
        ensures=tuple(postconditions),
        decreases=tuple(decreases) if decreases else None,
    )



def parse_module(source: str):
    """Parse multiple top-level signatures, each followed by its own contract/body.

    Functions may be declared in any order; their names are resolved when
    verification conditions are generated.
    """
    from .syntax import Module

    lines = [line.split("--", 1)[0].strip() for line in source.splitlines()]
    lines = [line for line in lines if line]
    if not lines:
        raise ParseError("Empty source file")
    blocks: list[list[str]] = []
    data_types = []
    for line in lines:
        if line.startswith("data "):
            if line != "data Tree = Empty | Node(Bool, Tree, Int, Tree)":
                raise ParseError(
                    "The experimental datatype extension supports exactly: "
                    "data Tree = Empty | Node(Bool, Tree, Int, Tree)"
                )
            if "Tree" in data_types or blocks:
                raise ParseError("Data declarations must be unique and precede functions")
            data_types.append("Tree")
            continue
        if _SIGNATURE.fullmatch(line):
            blocks.append([line])
        elif not blocks:
            raise ParseError("First statement must be a function signature")
        else:
            blocks[-1].append(line)
    if not blocks:
        raise ParseError("At least one function definition is required")
    allowed_types = ("Int", "Bool", *data_types)
    functions = tuple(
        parse_program("\n".join(block), allowed_types=allowed_types)
        for block in blocks
    )
    names = [function.name for function in functions]
    if len(set(names)) != len(names):
        raise ParseError("Duplicate top-level function name")
    return Module(functions, tuple(data_types))
