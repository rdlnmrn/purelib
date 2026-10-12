#!/usr/bin/env python3
"""Check authored Lean owners and visibility-tag names in the current source tree.

This lexical check does not establish name resolution or proof-closure safety.
It shares the source editor's lexer and checks source tokens without build
artifacts. Quoted identifier references are checked; comments and strings are not.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

from scripts.module_style import core as style
from scripts.lean_module_data.paths import parse_name

from scripts.paths import ROOT
PROJECT_ROOTS = {"Purelib", "Test", "papers", "formalisations", "scripts"}


def components(name: str) -> tuple[str, ...]:
    """Decode escaped name components without splitting dots inside escapes."""
    parsed = parse_name(name)
    if not parsed:
        raise ValueError(f"unsupported Lean name: {name!r}")
    return tuple(value for tag, value in parsed if tag == 1)


def underscore_owners(parts: tuple[str, ...]) -> tuple[str, ...]:
    """Select literal authored owner components; callers strip genuine root qualifiers."""
    return tuple(part for part in parts if part.startswith("_"))


def inspect_source(path: str, text: str) -> dict:
    """Inventory declaration owners, explicit scopes and tagged references."""
    inventory = style.inventory(text)
    owners, references = [], []
    for declaration in inventory["declarations"]:
        name = declaration["name"]
        if declaration["name_start"] == declaration["name_end"]:
            # Anonymous examples/instances have source-survey keys, not Lean names.
            parent = name.rpartition(".")[0]
            parts = components(parent) if parent else ()
        else:
            parts = components(name)
            if declaration["kind"] not in {"structure", "class", "inductive", "class inductive"}:
                parts = parts[:-1]
        bad = underscore_owners(parts)
        if bad:
            owners.append({"kind": "declaration", "name": name,
                           "line": declaration["line"], "components": list(bad)})
    # Commands inside syntax quotations are protected by inventory. Their fully
    # qualified identifiers remain covered by the reference scan below.
    code = style.mask(text, inventory["tokens"])
    for line_number, line in enumerate(code.splitlines(), 1):
        match = re.match(r"\s*namespace\s+(" + style.NAME.pattern + r")", line)
        if match and (bad := underscore_owners(components(match[1]))):
            owners.append({"kind": "namespace", "name": match[1],
                           "line": line_number, "components": list(bad)})
    tokens = style.lex(text)
    for token in tokens:
        if token.kind != "ident":
            continue
        # The general editor lexer also recognizes word-like notation tokens
        # such as superscript exponents. Only actual Lean name literals have
        # declaration/reference components to check.
        if not parse_name(token.text):
            continue
        parts = components(token.text)
        suffixes = [part for part in parts if part.endswith("_public")]
        project = parts[1:] if parts and parts[0] == "_root_" else parts
        bad = underscore_owners(project[:-1]) if project and project[0] in PROJECT_ROOTS else ()
        if suffixes or bad:
            references.append({"name": token.text, "line": text.count("\n", 0, token.start) + 1,
                               "start": token.start, "end": token.end,
                               "suffix_components": suffixes, "owner_components": list(bad)})
    return {"path": path, "source_sha256": hashlib.sha256(text.encode()).hexdigest(),
            "declarations": len(inventory["declarations"]),
            "owners": owners, "references": references}


def discover(paths: list[str]) -> list[Path]:
    """Select nonignored current sources, or validate an explicit nonempty scope."""
    if paths:
        selected = [Path(path) for path in paths]
        if any(path.suffix != ".lean" or not path.is_file() for path in selected):
            raise ValueError("explicit scope requires existing .lean files")
    else:
        result = subprocess.run(["rg", "--files", "-g", "*.lean"], cwd=ROOT,
                                text=True, capture_output=True, check=True)
        selected = [Path(path) for path in result.stdout.splitlines()]
    if not selected or len(selected) != len(set(selected)):
        raise ValueError("source scope must be nonempty and contain distinct files")
    return sorted(selected)


def main() -> int:
    """Report current naming debt; check mode fails until that debt is removed."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("paths", nargs="*")
    parser.add_argument("--survey", action="store_true", help="report naming debt without failing")
    parser.add_argument("--json", action="store_true", help="emit source-bound machine-readable results")
    args = parser.parse_args()
    try:
        rows = [inspect_source(path.as_posix(), (ROOT / path).read_text())
                for path in discover(args.paths)]
    except (ValueError, OSError, subprocess.CalledProcessError) as error:
        print(f"authored-name check failed: {error}", file=sys.stderr)
        return 2
    owners = sum(len(row["owners"]) for row in rows)
    references = sum(len(row["references"]) for row in rows)
    summary = {"files": len(rows), "declarations": sum(row["declarations"] for row in rows),
               "owner_sites": owners, "reference_sites": references}
    if args.json:
        print(json.dumps({"schema": 1, "summary": summary, "sources": rows},
                         ensure_ascii=False, sort_keys=True))
    else:
        print("Authored Lean names: " + ", ".join(f"{key}={value}" for key, value in summary.items()))
        shown = 0
        for row in rows:
            for entry in row["owners"] + row["references"]:
                if shown < 20:
                    print(f"{row['path']}:{entry['line']}: {entry['name']}")
                    shown += 1
        if owners + references > shown:
            print(f"... {owners + references - shown} further sites; use --json for the complete survey")
    return 0 if args.survey or not (owners or references) else 1


if __name__ == "__main__":
    raise SystemExit(main())
