"""Human-readable diagnostics for TinyAIR source and type errors."""


class LanguageError(Exception):
    """A TinyAIR program is syntactically or semantically invalid."""


class ParseError(LanguageError):
    """Parsing or lexical analysis failed."""


class TypeCheckError(LanguageError):
    """An expression has an invalid type or contains an unknown name."""
