#!/usr/bin/env python3
"""Build configured native linter providers in order before project compilation."""

from __future__ import annotations

import subprocess
import sys
import tomllib
from pathlib import Path

from scripts.paths import ROOT
from scripts.linting import lake_args


def build_options(args: list[str]) -> list[str] | None:
    """Select project build/lint commands while preserving their global settings."""
    i = 0
    while i < len(args):
        arg = args[i]
        if arg in {"--", "--help", "-h", "--version", "--no-build"}:
            return None
        if arg in {"-d", "--dir", "-f", "--file"} or arg.startswith(("--dir=", "--file=")):
            return None
        if arg in lake_args.GLOBAL_VALUE_OPTIONS:
            if i + 1 >= len(args):
                return None
            i += 2
        elif arg.startswith("-"):
            i += 1
        else:
            break
    if i == len(args) or args[i] not in {"build", "lint"}:
        return None
    if any(arg in {"--help", "-h"} for arg in args[i + 1:]):
        return None
    return args[:i]


def prepare(lake: str, args: list[str], run=subprocess.run) -> int:
    """Reuse Lake's own dependency traces; stop immediately on a provider failure."""
    cwd = Path.cwd().resolve()
    if cwd != ROOT and ROOT not in cwd.parents:
        return 0
    options = build_options(args)
    if options is None:
        return 0
    config = tomllib.loads((ROOT / "lakefile.toml").read_text())
    for target in config.get("dynlibs", []) + config.get("plugins", []):
        # Separate invocations prevent Lake's asynchronous facet resolution
        # from scheduling multiple writers for a cold shared dependency.
        result = run([lake, *options, "build", target], cwd=ROOT)
        if result.returncode:
            return result.returncode
    return 0


if __name__ == "__main__":
    raise SystemExit(prepare(sys.argv[1], sys.argv[2:]))
