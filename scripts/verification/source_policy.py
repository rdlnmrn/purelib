"""Check constructive source policy on the current active project inventory."""

import argparse
from pathlib import Path
import re
import sys

from scripts.paths import ROOT
from scripts.verification import modules, sources


FORBIDDEN = {"noncomputable", "classical", "native_decide", "sorry", "admit"}
RESOURCE = re.compile(r"\bset_option\s+(maxRecDepth|maxHeartbeats)\b")
COMPLETED_IMPORTS = ("Mathlib.MeasureTheory", "Mathlib.Topology", "Mathlib.SetTheory",
                     "Mathlib.Cardinal", "Mathlib.Analysis")


def violations(source):
    """Report actual source tokens and imports, ignoring prose and string inputs."""
    result = []
    masked = sources.code(source, quoted_input=True)
    for token in sources.lex(masked):
        if token.kind == "ident" and (token.text in FORBIDDEN or token.text.startswith("Classical.")):
            # Quoted names are data, rather than executed proof commands.
            if source[max(0, token.start - 1):token.start] == "`":
                continue
            result.append((source.count("\n", 0, token.start) + 1,
                           "forbidden constructive shortcut: " + token.text))
    for match in RESOURCE.finditer(masked):
        result.append((source.count("\n", 0, match.start()) + 1,
                       "resource override: " + match[1]))
    for name, _ in sources.imports(source):
        if any(name == prefix or name.startswith(prefix + ".") for prefix in COMPLETED_IMPORTS):
            result.append((1, "completed/infinite import route: " + name))
    return result


def check(paths, root=ROOT):
    """Reject empty inventories, unreadable sources and actual policy violations."""
    paths = list(paths)
    if not paths:
        raise ValueError("source policy found an empty source inventory")
    failures = []
    for path in paths:
        source = Path(root) / path
        text = source.read_text(encoding="utf-8")
        failures.extend(f"{path}:{line}: {message}" for line, message in violations(text))
    return failures


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("sources", nargs="*", type=Path, help="explicit source files; otherwise all active sources")
    args = parser.parse_args(argv)
    try:
        paths = [path.resolve() for path in args.sources] if args.sources else modules.discover(include_scripts=True)[0]
        failures = check(paths)
        for failure in failures:
            print(failure, file=sys.stderr)
        if failures:
            return 1
        print(f"Constructive source policy passed for {len(paths)} current sources")
        return 0
    except (OSError, UnicodeError, ValueError) as error:
        print(f"source policy failed: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
