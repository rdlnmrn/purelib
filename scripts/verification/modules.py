#!/usr/bin/env python3
"""List active modules at the final Purelib source boundary.

The authoritative proof checks use this inventory. Every Purelib source is
active; configured script owners are selected explicitly.
"""

from __future__ import annotations

import argparse
import os
import sys
import tomllib
from pathlib import Path


from scripts.paths import ROOT
IGNORED_DIRECTORIES = {
    ".git", ".lake", ".elan", ".external", "scripts",
    "docs", ".github",
}
ACTIVE_ROOTS = {
    "Purelib", "Test", "papers", "formalisations",
}


def configured_script_sources(root=None) -> set[str]:
    """Select the mathematical harness/checkpoint roots declared to Lake."""
    root = ROOT if root is None else Path(root)
    config = root / "lakefile.toml"
    targets = tomllib.loads(config.read_text())
    names = set()
    for kind in ("lean_lib", "lean_exe"):
        for target in targets.get(kind, []):
            roots = target.get("roots", []) + ([target["root"]] if "root" in target else [])
            names.update(name for name in roots if name.startswith("scripts."))
    paths = {name.replace(".", "/") + ".lean" for name in names}
    if not paths:
        raise ValueError("configured script inventory is empty")
    missing = sorted(path for path in paths if not (root / path).is_file())
    if missing:
        raise ValueError("missing configured script sources: " + ", ".join(missing))
    return paths


def discover(include_scripts: bool = False, root=None) -> tuple[list[str], list[str]]:
    active: list[str] = []
    inactive: list[str] = []
    unknown: list[str] = []
    root = ROOT if root is None else Path(root)
    script_paths = configured_script_sources(root) if include_scripts else set()
    active.extend(script_paths)
    def discovery_error(error):
        raise error

    for directory, children, files in os.walk(root, onerror=discovery_error):
        if Path(directory) == root:
            children[:] = [name for name in children if name not in IGNORED_DIRECTORIES]
        for filename in files:
            if not filename.endswith(".lean"):
                continue
            relative = (Path(directory) / filename).relative_to(root)
            name = relative.as_posix()
            if len(relative.parts) > 1 and relative.parts[0] in ACTIVE_ROOTS:
                active.append(name)
            else:
                unknown.append(name)
    if unknown:
        raise ValueError("unclassified project Lean sources: " + ", ".join(unknown))
    modules = [path.removesuffix(".lean").replace("/", ".") for path in active]
    if len(modules) != len(set(modules)):
        raise ValueError("duplicate active project module names")
    if not active:
        raise ValueError("active project inventory is empty")
    return sorted(active), inactive


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--kind", choices=("active", "inactive", "all"), default="active")
    parser.add_argument("--format", choices=("module", "path"), default="module")
    parser.add_argument("--configured-scripts", action="store_true", help="also select Lake-declared harness/checkpoint roots")
    args = parser.parse_args()
    try:
        active, inactive = discover(args.configured_scripts)
    except (OSError, ValueError) as error:
        print(f"project module discovery failed: {error}", file=sys.stderr)
        return 1
    selected = active if args.kind == "active" else inactive if args.kind == "inactive" else active + inactive
    selected.sort()
    for path in selected:
        print(path.removesuffix(".lean").replace("/", ".") if args.format == "module" else path)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
