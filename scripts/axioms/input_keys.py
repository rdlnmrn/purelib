#!/usr/bin/env python3
"""Hash every compiled proof part in selected axiom-audit import closures.

The inventory comes from pinned Lean module metadata, not source import text.
Its module keys are Merkle hashes over the actual `.olean` parts and every
transitive import. An explicit module's private proof can therefore change a
receipt even when its public `.olean` and a client's Lake trace do not.
"""

import argparse
from graphlib import TopologicalSorter
import hashlib
import json
from pathlib import Path
import sys


def digest(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def identity(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True).encode()).hexdigest()


def compiled_path(name, search):
    relative = Path(*name.split(".")).with_suffix(".olean")
    for base in search:
        candidate = base / relative
        if candidate.is_file():
            return candidate.resolve()
    raise ValueError(f"cannot resolve compiled module: {name}")


def keys_for_inventory(inventory, search):
    if inventory.get("schema") != 1:
        raise ValueError("unsupported axiom input inventory schema")
    roots = inventory["roots"]
    records = inventory["modules"]
    if not roots or len(roots) != len(set(roots)):
        raise ValueError("empty or duplicate axiom input roots")
    nodes = {record["name"]: record for record in records}
    if len(nodes) != len(records):
        raise ValueError("duplicate compiled module inventory node")
    reached, pending = set(), list(roots)
    while pending:
        name = pending.pop()
        if name in reached:
            continue
        if name not in nodes:
            raise ValueError(f"missing compiled module dependency: {name}")
        reached.add(name)
        pending.extend(nodes[name]["imports"])
    if reached != set(nodes):
        raise ValueError("unreachable compiled module inventory node")

    hashes = {}
    for name in sorted(nodes):
        main = compiled_path(name, search)
        paths = [Path(path).resolve() for path in nodes[name]["files"]]
        expected = ([main], [main, Path(str(main) + ".server"),
                             Path(str(main) + ".private")])
        if paths not in expected:
            raise ValueError(f"compiled module resolution/parts changed: {name}")
        for path in paths:
            if path not in hashes:
                if not path.is_file():
                    raise ValueError(f"missing compiled input: {path}")
                before = path.stat()
                value = digest(path)
                after = path.stat()
                signature = lambda stat: (stat.st_ino, stat.st_size,
                                          stat.st_mtime_ns, stat.st_ctime_ns)
                if signature(before) != signature(after):
                    raise ValueError(f"compiled input changed during audit keying: {path}")
                hashes[path] = value

    keys = {}
    for name in TopologicalSorter({name: node["imports"] for name, node in nodes.items()}).static_order():
        node = nodes[name]
        keys[name] = identity({
            "name": name,
            "files": {path: hashes[Path(path).resolve()] for path in node["files"]},
            "imports": {dependency: keys[dependency] for dependency in node["imports"]},
        })
    return {name: keys[name] for name in roots}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("inventory", type=Path)
    parser.add_argument("--lean-path", required=True)
    args = parser.parse_args()
    search = [Path(path).resolve() for path in args.lean_path.split(":") if path]
    try:
        inventory = json.loads(args.inventory.read_text())
        for name, key in keys_for_inventory(inventory, search).items():
            print(f"{name}\t{key}")
    except (KeyError, OSError, ValueError) as error:
        print(f"axiom input key error: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
