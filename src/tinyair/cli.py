"""Command-line verification and Z3 SMT-LIB export for TinyAIR modules."""

import argparse
from pathlib import Path

import z3

from .errors import LanguageError
from .module_verification import generate_module_conditions, verify_module
from .parser import parse_module
from .rank import compile_rank
from .verification import compile_expr, make_solver


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Prove contracts and termination for TinyAIR function modules."
    )
    parser.add_argument("source", type=Path, help="A .air source file")
    parser.add_argument(
        "--emit-smt2", metavar="DIRECTORY", type=Path,
        help="Export one independent negated VC per SMT-LIB file",
    )
    parser.add_argument(
        "--timeout", type=int, default=5000,
        help="Per-VC Z3 timeout in milliseconds (0 disables timeout)",
    )
    parser.add_argument(
        "--max-nodes", type=int, default=3,
        help="Finite input-tree node bound for experimental Tree datatype (default: 3)",
    )
    args = parser.parse_args(argv)
    if args.timeout < 0:
        parser.error("--timeout must be >= 0")

    try:
        parsed = parse_module(args.source.read_text(encoding="utf-8"))
        if parsed.data_types:
            from .tree_language import verify_tree_module
            return verify_tree_module(
                parsed, max_nodes=args.max_nodes,
                output=args.emit_smt2, timeout_ms=args.timeout,
            )
        module = generate_module_conditions(parsed)
    except (LanguageError, OSError) as error:
        parser.exit(2, f"Error: {error}\n")

    for compiled in module.functions:
        name = compiled.function.name
        print(f"\nFunction: {name}")
        if compiled.function.decreases is not None:
            rank = compile_rank(
                compiled.function.decreases, compiled.symbols, compile_expr
            )
            formatted_rank = ", ".join(str(part) for part in rank)
            # TOP is a notional sentinel in the lexicographic comparator.
            print(f"  Effective decreases: ({formatted_rank}, TOP)")
        for condition in compiled.conditions:
            print(f"\nVC {condition.number} [{condition.description}]:")
            print(f"  {z3.simplify(condition.formula)}")
            if args.emit_smt2 is not None:
                args.emit_smt2.mkdir(parents=True, exist_ok=True)
                prefix = (
                    args.source.stem if len(module.functions) == 1
                    else f"{args.source.stem}_{name}"
                )
                filename = f"{prefix}_vc{condition.number}.smt2"
                destination = args.emit_smt2 / filename
                destination.write_text(
                    make_solver(condition, args.timeout).to_smt2(),
                    encoding="utf-8",
                )
                print(f"  SMT-LIB: {destination}")

    print()
    grouped_results = verify_module(module, timeout_ms=args.timeout)
    all_proved = True
    for name, results in grouped_results.items():
        print(f"Function {name}:")
        for result in results:
            print(
                f"  VC {result.condition.number} "
                f"[{result.condition.description}]: {result.status}"
            )
            if result.status != "PROVED":
                all_proved = False
            if result.counterexample is not None:
                print(f"    Counterexample: {result.counterexample}")
            if result.reason:
                print(f"    Reason: {result.reason}")

    if all_proved:
        print("\nAll module verification conditions proved.")
        return 0
    print("\nAt least one module verification condition was not proved.")
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
