#!/usr/bin/env python3
"""Expand an unscoped Lake lint command to the authoritative project inventory."""

from __future__ import annotations

import sys
from pathlib import Path
from typing import Callable


from scripts.paths import ROOT
GLOBAL_VALUE_OPTIONS = {"-d", "--dir", "-f", "--file", "-K", "--config",
                        "--log-level", "--fail-level"}
LINT_VALUE_OPTIONS = {"--linters", "--lint-only"}


def project_modules() -> list[str]:
    """Use the same active-source boundary as the authoritative proof checker."""
    from scripts.verification import modules
    paths, _ = modules.discover(include_scripts=True)
    return sorted(path.removesuffix(".lean").replace("/", ".") for path in paths)


def expand(args: list[str], discover: Callable[[], list[str]] = project_modules) -> list[str]:
    """Preserve scoped and unrelated commands; fill only lint's empty module list."""
    i = 0
    while i < len(args):
        arg = args[i]
        if arg == "--" or arg in {"--help", "-h", "--version"}:
            return args
        if arg in {"-d", "--dir", "-f", "--file"} or arg.startswith(("--dir=", "--file=")):
            return args  # A different workspace/configuration has its own inventory.
        if arg in GLOBAL_VALUE_OPTIONS:
            i += 2
        elif arg.startswith("-"):
            i += 1
        else:
            break
    if i >= len(args) or args[i] != "lint":
        return args
    i += 1
    while i < len(args) and args[i] != "--":
        arg = args[i]
        if arg in {"--help", "-h"}:
            return args
        if arg in LINT_VALUE_OPTIONS:
            if i + 1 >= len(args):
                return args  # Leave malformed CLI input to Lake's diagnostic.
            i += 2
        elif arg.startswith("-"):
            i += 1
        else:
            return args  # An explicit module list is already scoped.
    modules = discover()
    from scripts.lean_module_data.paths import parse_name
    if not modules or any(not parse_name(module) for module in modules):
        raise ValueError("default lint requires a nonempty valid project module inventory")
    if len(modules) != len(set(modules)):
        raise ValueError("default lint inventory contains duplicate modules")
    return args[:i] + modules + args[i:]


def main() -> int:
    """Emit NUL-delimited arguments so the shell preserves their exact boundaries."""
    try:
        args = expand(sys.argv[1:])
    except ValueError as error:
        print(f"project lint discovery failed: {error}", file=sys.stderr)
        return 1
    for arg in args:
        sys.stdout.buffer.write(arg.encode() + b"\0")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
