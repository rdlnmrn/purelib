#!/usr/bin/env python3
"""Capture and compare pinned-Lean compiled declaration contracts for reviewed changes.

The host reader checks pinned private kernel metadata bytes. Schema 2 hashes complete DAG
encodings of expressions without expanding shared subexpressions as text.
Schema 1 snapshots remain readable with their original renderer.
"""
import argparse
import hashlib
import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path

from scripts.paths import ROOT
from scripts.nanoda.artifact_inputs import compiled_inputs, verify_inputs
DAG_HELPER = ROOT / "scripts/project-module-data.py"
READER_PARTS = tuple(sorted((ROOT / "scripts/lean_module_data").glob("*.py")))
OBS_HELPER = ROOT / "scripts/observations/ProjectQueryReplay.lean"
OBS_MODULE = "scripts.observations.ProjectQueryReplay"
OBS_TARGET = "project_query_replay_observation"
ARTIFACT_SUFFIXES = ("", ".private", ".server", ".hash", ".trace", ".ir")


def digest(data):
    return hashlib.sha256(data).hexdigest()


def file_digest(path):
    return digest(path.read_bytes()) if path.is_file() else None


def run(*args):
    result = subprocess.run(args, cwd=ROOT, text=True, capture_output=True)
    if result.returncode:
        raise RuntimeError(f"{' '.join(map(str, args))} failed:\n{result.stdout}{result.stderr}")
    return result.stdout


def reader_digest(schema):
    """Bind the complete decoder, including every typed layout and observer."""
    return digest(json.dumps({str(path.relative_to(ROOT)): digest(path.read_bytes())
                              for path in (DAG_HELPER, *READER_PARTS)},
                             sort_keys=True, separators=(",", ":")).encode())


def reader_tool_paths():
    """Return the actual host implementation's complete source inventory."""
    return (DAG_HELPER, *READER_PARTS)


def contract_invocation(module, artifact_root=None, schema=2):
    """Read exact contracts without executing a compiled Lean module or initializer."""
    arguments = ("python3", DAG_HELPER, "contracts", "--schema", str(schema), module)
    default = ROOT / ".lake/build/lib/lean"
    if artifact_root is None or Path(artifact_root).resolve() == default.resolve():
        return (ROOT / "scripts/run-lake.sh", "env", *arguments), None
    search = run(ROOT / "scripts/run-lake.sh", "env", "printenv", "LEAN_PATH").strip()
    sysroot = run(ROOT / "scripts/run-lake.sh", "env", "lean", "--print-prefix").strip()
    env = {**os.environ, "LEAN_PATH": str(Path(artifact_root).resolve()) + ":" + search,
           "LEAN_SYSROOT": sysroot}
    return arguments, env

def modules_from_args(args):
    modules = list(args.module)
    if args.manifest:
        modules += [s.strip() for s in args.manifest.read_text().splitlines()
                    if s.strip() and not s.lstrip().startswith("#")]
    if not modules and args.snapshot and args.snapshot.is_file():
        modules = list(json.loads(args.snapshot.read_text())["modules"])
    if not modules or len(modules) != len(set(modules)):
        raise ValueError("give at least one distinct module, directly or in --manifest")
    return sorted(modules)


def lean_records(modules, schema, artifact_root=None, *, include_metadata=False):
    """Read compiler records, preserving the historical declaration-only API.

    Complete contract capture requests module metadata explicitly; older
    declaration surveys still receive exactly their original record shape.
    """
    for module in modules:
        if artifact_root is not None:
            relative = Path(*module.split(".")).with_suffix(".olean")
            for suffix in ("", ".private"):
                artifact = Path(str(Path(artifact_root) / relative) + suffix)
                if not artifact.is_file():
                    raise FileNotFoundError(f"missing selected compiled artifact: {artifact}")
        command, env = contract_invocation(module, artifact_root, schema)
        with tempfile.TemporaryFile(mode="w+t") as errors:
            with subprocess.Popen(command, cwd=ROOT, text=True,
                                  stdout=subprocess.PIPE, stderr=errors, env=env) as process:
                for line in process.stdout:
                    record = json.loads(line)
                    if include_metadata or 'declaration_count' not in record:
                        yield record
                if process.wait():
                    errors.seek(0)
                    raise RuntimeError(f"contract capture failed for {module}:\n"
                                       f"{errors.read()}")


def contract_digest(value, schema):
    if value is None:
        return None
    if schema == 1:
        return digest(value.encode())
    return digest(json.dumps(value, sort_keys=True, separators=(",", ":"),
                             ensure_ascii=False).encode())


def capture(modules, artifact_root, observation, schema=2):
    if observation and artifact_root.resolve() != (ROOT / ".lake/build/lib/lean").resolve():
        raise ValueError("native observation requires the current default build; "
                         "capture alternate compiled roots without --observation")
    declarations = {module: {} for module in modules}
    module_system = {}
    expected_counts = {}
    for record in lean_records(modules, schema, artifact_root, include_metadata=True):
        module = record["module"]
        if module not in declarations:
            raise RuntimeError(f"Lean returned unrequested module: {module}")
        system = record.get("module_system")
        if type(system) is not bool:
            raise RuntimeError(f"invalid module-system metadata: {module}")
        if "declaration_count" in record:
            if set(record) != {"module", "module_system", "declaration_count"}:
                raise RuntimeError(f"invalid module metadata: {module}")
            count = record["declaration_count"]
            if type(count) is not int or count < 0 or module in expected_counts:
                raise RuntimeError(f"invalid or duplicate module metadata: {module}")
            expected_counts[module] = count
            module_system[module] = system
            continue
        if set(record) != {"module", "module_system", "declaration"}:
            raise RuntimeError(f"invalid declaration record: {module}")
        if module not in expected_counts or module_system[module] != system:
            raise RuntimeError(f"missing or inconsistent module metadata: {module}")
        decl = dict(record["declaration"])
        name = decl.pop("name")
        for key in ("type", "body", "levels", "extra"):
            value = decl.pop(key)
            decl[key + "_sha256"] = contract_digest(value, schema)
        if name in declarations[module]:
            raise RuntimeError(f"duplicate declaration: {module}: {name}")
        declarations[module][name] = decl
    if set(module_system) != set(modules):
        raise RuntimeError("Lean returned an incomplete module set")
    for module, count in expected_counts.items():
        if len(declarations[module]) != count:
            raise RuntimeError(f"Lean returned an incomplete declaration set: {module}")
    artifacts = {}
    sources = {}
    for module in modules:
        relative = Path(*module.split("."))
        source = ROOT / relative.with_suffix(".lean")
        olean = artifact_root / relative.with_suffix(".olean")
        if not olean.is_file():
            raise FileNotFoundError(f"missing compiled module: {olean}")
        if not source.is_file():
            raise FileNotFoundError(f"missing source module: {source}")
        artifacts[module] = {suffix or ".olean": file_digest(Path(str(olean) + suffix))
                             for suffix in ARTIFACT_SUFFIXES}
        sources[module] = {"path": source.relative_to(ROOT).as_posix(),
                           "sha256": file_digest(source)}
    observed = None
    observation_inputs = None
    observation_executable = None
    if observation:
        # Runtime-only imports and owned native externs require the built
        # executable; interpreting the source cannot load that execution phase.
        run(ROOT / "scripts/run-lake.sh", "--wfail", "--no-build", "build", OBS_TARGET)
        search = run(ROOT / "scripts/run-lake.sh", "env", "printenv", "LEAN_PATH").strip()
        sysroot = run(ROOT / "scripts/run-lake.sh", "env", "lean", "--print-prefix").strip()
        search_paths = [Path(p) for p in search.split(os.pathsep)] + [Path(sysroot) / "lib/lean"]
        observation_inputs = compiled_inputs([OBS_MODULE], search_paths)
        executable = ROOT / ".lake/build/bin" / OBS_TARGET
        observation_executable = digest(executable.read_bytes())
        observed = json.loads(run(executable).strip())
        if digest(executable.read_bytes()) != observation_executable:
            raise RuntimeError("observation executable changed during capture")
        verify_inputs(observation_inputs, search_paths)
    return {
        "schema": schema,
        "lean_toolchain": (ROOT / "lean-toolchain").read_text().strip(),
        "source_revision": run("git", "rev-parse", "HEAD").strip(),
        "modules": modules,
        "module_system": module_system,
        "sources": sources,
        "artifacts": artifacts,
        "declarations": declarations,
        "observation": observed,
        "observation_inputs": observation_inputs,
        "tool_sha256": {"lean": reader_digest(schema),
                         "driver": file_digest(Path(__file__)),
                         "observation": file_digest(OBS_HELPER) if observation else None,
                         "observation_input_reader": file_digest(ROOT / "scripts/nanoda/artifact_inputs.py")
                           if observation else None,
                         "observation_executable": observation_executable},
    }


def is_public_source_name(name, old, new):
    leaf = name.rsplit(".", 1)[-1]
    generated = leaf.startswith(("match_", "_proof_"))
    return not generated and not any(
        record.get(flag) for record in (old, new)
        for flag in ("private", "internal"))


def was_public_source_name(name, old):
    leaf = name.rsplit(".", 1)[-1]
    return not leaf.startswith(("match_", "_proof_")) and not any(
        old.get(flag) for flag in ("private", "internal"))


def differences(before, after):
    changes = []
    for module in sorted(set(before["modules"]) | set(after["modules"])):
        old = before["declarations"].get(module, {})
        new = after["declarations"].get(module, {})
        for name in sorted(set(old) | set(new)):
            if name not in old:
                changes.append((module, name, "added"))
            elif name not in new:
                changes.append((module, name, "removed"))
            else:
                for key in sorted(set(old[name]) | set(new[name])):
                    if old[name].get(key) != new[name].get(key):
                        changes.append((module, name, key))
    return changes


def public_visibility_regressions(before, after):
    """Legacy public definitions must remain exported and reducible after conversion."""
    regressions = []
    for module in before["modules"]:
        if not after["module_system"].get(module):
            continue
        for name, old in before["declarations"][module].items():
            new = after["declarations"].get(module, {}).get(name)
            if new is None or not was_public_source_name(name, old):
                continue
            if old.get("exported") is not False and (
                    new.get("private") or new.get("internal") or
                    new.get("exported") is not True):
                regressions.append((module, name, "not-exported"))
            if old["kind"] == "def" and old.get("exposed") is not False \
                    and new.get("exposed") is not True:
                regressions.append((module, name, "not-exposed"))
    return regressions


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode", choices=("capture", "check", "diff"))
    parser.add_argument("--snapshot", type=Path, required=True)
    parser.add_argument("--module", action="append", default=[])
    parser.add_argument("--manifest", type=Path)
    parser.add_argument("--artifact-root", type=Path,
                        default=ROOT / ".lake/build/lib/lean")
    parser.add_argument("--observation", action="store_true",
                        help="execute the current native adaptive regression; requires default build artifacts")
    parser.add_argument("--fail-interface", action="store_true",
                        help="in diff mode, fail if a public name, kind or type changes")
    args = parser.parse_args()
    modules = modules_from_args(args)
    prior = json.loads(args.snapshot.read_text()) if args.mode != "capture" else None
    if prior and prior["modules"] != modules:
        parser.error("selected modules differ from snapshot")
    observed = args.observation or bool(prior and prior.get("observation") is not None)
    schema = prior["schema"] if prior else 2
    if schema not in (1, 2):
        parser.error(f"unsupported snapshot schema: {schema}")
    current = capture(modules, args.artifact_root.resolve(), observed, schema)
    serialized = json.dumps(current, indent=2, sort_keys=True) + "\n"
    if args.mode == "capture":
        args.snapshot.parent.mkdir(parents=True, exist_ok=True)
        args.snapshot.write_text(serialized)
        print(f"captured {len(modules)} modules and "
              f"{sum(map(len, current['declarations'].values()))} declarations: {args.snapshot}")
    elif args.mode == "check":
        if current != prior:
            print("compiled contract snapshot differs; run diff for details", file=sys.stderr)
            raise SystemExit(1)
        print(f"compiled contract snapshot matches: {args.snapshot}")
    else:
        for module, name, key in differences(prior, current):
            print(f"declaration\t{module}\t{name}\t{key}")
        for key in ("source_revision", "lean_toolchain", "module_system", "sources",
                    "artifacts", "observation", "observation_inputs", "tool_sha256"):
            if prior.get(key) != current.get(key):
                print(f"provenance\t{key}\tchanged")
        interface = [(m, n, k) for m, n, k in differences(prior, current)
                     if k in ("added", "removed", "kind", "type_sha256", "levels_sha256")
                     and is_public_source_name(
                         n, prior["declarations"].get(m, {}).get(n, {}),
                         current["declarations"].get(m, {}).get(n, {}))]
        visibility = public_visibility_regressions(prior, current)
        interface += visibility
        for module, name, kind in visibility:
            print(f"interface\t{module}\t{name}\t{kind}")
        print(f"public interface differences: {len(interface)}")
        if args.fail_interface and interface:
            raise SystemExit(1)


if __name__ == "__main__":
    try:
        main()
    except (RuntimeError, ValueError, FileNotFoundError) as exc:
        raise SystemExit(str(exc)) from exc
