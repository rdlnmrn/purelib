#!/usr/bin/env python3
"""Isolated, bounded declaration probes; never builds repository targets."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import time

from scripts.paths import ROOT
# The four baseline compilers have been retired and their replacements built.
# Add module names here before probing alongside any future live compiler.
ACTIVE = set()


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def atomic_json(path, value):
    path = Path(path)
    with tempfile.NamedTemporaryFile(mode="w", dir=path.parent, delete=False) as out:
        json.dump(value, out, indent=2)
        out.flush()
        os.fsync(out.fileno())
        temporary = out.name
    os.replace(temporary, path)


def cached(directory, key, execute):
    directory.mkdir(parents=True, exist_ok=True)
    report = directory / "result.json"
    if report.exists():
        saved = json.loads(report.read_text())
        if saved["key"] == key and all(
                (directory / name).is_file() and digest(directory / name) == checksum
                for name, checksum in saved["outputs"].items()):
            print(f"REUSED {directory.name}: {saved['outcome']}", flush=True)
            return saved
        raise RuntimeError(f"incompatible/corrupt checkpoint: {directory}")
    result = execute(directory)
    result["key"] = key
    result["outputs"] = {p.name: digest(p) for p in directory.iterdir() if p.is_file()
                         and p.name != "result.json"}
    atomic_json(report, result)
    print(f"COMPUTED {directory.name}: {result['outcome']}", flush=True)
    return result


def self_test():
    with tempfile.TemporaryDirectory(prefix="ccl-probe-restart-") as tmp:
        directory = Path(tmp) / "completed"
        calls = []

        def first(out):
            calls.append(1)
            (out / "artifact").write_text("checked-stage")
            return {"outcome": "success"}

        cached(directory, "same", first)
        try:
            raise InterruptedError("interruption before next stage")
        except InterruptedError:
            pass

        def forbidden(_):
            raise AssertionError("completed generator called on restart")

        cached(directory, "same", forbidden)
        assert calls == [1]
        (directory / "artifact").write_text("corrupt")
        try:
            cached(directory, "same", forbidden)
        except RuntimeError:
            pass
        else:
            raise AssertionError("corruption accepted")
        # A real process exit between stages must not rerun completed work.
        child = f"""
import os
from pathlib import Path
from scripts.profiling import branch_builds as module
directory = Path({str(Path(tmp) / 'process-restart')!r})
def produce(out):
    (out / 'artifact').write_text('finished')
    return {{'outcome': 'success'}}
module.cached(directory, 'restart', produce)
os._exit(17)
"""
        assert subprocess.run([sys.executable, "-c", child]).returncode == 17
        restarted = child.replace("(out / 'artifact').write_text('finished')",
                                  "raise AssertionError('completed stage rerun')")
        assert subprocess.run([sys.executable, "-c", restarted]).returncode == 17
    print("restart and corruption regression passed", flush=True)


def imports(source):
    # Lean permits nested block comments and public/meta imports.
    clean = []
    depth = 0
    position = 0
    while position < len(source):
        pair = source[position:position + 2]
        if pair == "/-":
            depth += 1
            position += 2
        elif depth and pair == "-/":
            depth -= 1
            position += 2
        elif not depth and pair == "--":
            end = source.find("\n", position)
            position = len(source) if end < 0 else end
        else:
            clean.append(source[position] if not depth or source[position] == "\n" else " ")
            position += 1
    text = "".join(clean)
    modules = re.findall(r"^\s*(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?([A-Za-z0-9_.]+)", text, re.M)
    if not re.search(r"^\s*prelude\b", text, re.M):
        modules.append("Init")
    return modules


def provenance(source, lean_paths):
    """Hash transitive source imports and every corresponding compiled sidecar."""
    sources = [ROOT] + sorted((ROOT / ".lake/packages").iterdir())
    sources += [ROOT / ".elan/toolchains/leanprover--lean4---v4.32.2/src/lean"]
    pending = imports(source)
    seen = set()
    files = {}
    while pending:
        module = pending.pop()
        if module in seen:
            continue
        if module in ACTIVE:
            raise RuntimeError(f"probe imports a live compiler target: {module}")
        seen.add(module)
        relative = Path(module.replace(".", "/"))
        src = next((p / relative.with_suffix(".lean") for p in sources
                    if (p / relative.with_suffix(".lean")).is_file()), None)
        artifact = next((p / relative.with_suffix(".olean") for p in lean_paths
                         if (p / relative.with_suffix(".olean")).is_file()), None)
        if src is None or artifact is None:
            raise RuntimeError(f"missing source or completed import: {module}")
        files[str(src)] = digest(src)
        pending.extend(imports(src.read_text()))
        for candidate in artifact.parent.glob(artifact.name + "*"):
            if candidate.is_file():
                files[str(candidate)] = digest(candidate)
    return files


def reload_provenance(directory, source, lean_path, lean):
    """Explicitly import a previous closure after checking its full provenance.

    This reuses dependency discovery, never a proof of a different declaration.
    The original result and its artifacts remain in their original directory.
    """
    saved = json.loads((directory / "result.json").read_text())
    for name, checksum in saved["outputs"].items():
        if Path(name).name != name or digest(directory / name) != checksum:
            raise RuntimeError("corrupt imported checkpoint")
    identity = json.loads((directory / "provenance.json").read_text())
    if hashlib.sha256(json.dumps(identity, sort_keys=True).encode()).hexdigest() != saved["key"]:
        raise RuntimeError("checkpoint identity does not match its key")
    if (identity["schema"] != 1 or identity["lean_path"] != lean_path
            or identity["lean"] != digest(lean)
            or identity["toolchain"] != (ROOT / "lean-toolchain").read_text()
            or imports(identity["source"]) != imports(source)):
        raise RuntimeError("incompatible imported dependency closure")
    current = {name: digest(name) for name in identity["imports"]}
    if current != identity["imports"]:
        raise RuntimeError("imported dependencies changed; rediscover the closure")
    print(f"REUSED dependency discovery from {directory}", flush=True)
    return current


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--self-test", action="store_true")
    parser.add_argument("--stage", choices=("module",))
    parser.add_argument("--seconds", type=int, default=45)
    parser.add_argument("--module", help="repository module copied by --stage module")
    parser.add_argument("--source-file", type=Path,
                        help="isolated candidate or closed source prefix under /tmp for --stage module")
    parser.add_argument("--dependency-prefix", type=Path,
                        help="import a checked generic module probe in place of --dependency-module")
    parser.add_argument("--dependency-module", help="direct import replaced by the checked prefix")
    parser.add_argument("--memory", default="3G")
    parser.add_argument("--reuse-provenance", type=Path)
    parser.add_argument("--check-only", action="store_true")
    parser.add_argument("--emit-code", action="store_true", help="also emit C and editor artifacts")
    parser.add_argument("--quiet", action="store_true", help="disable profiling and diagnostics")
    parser.add_argument("--native-stack", action="store_true",
                        help="interrupt only the isolated probe after 10 seconds for native stacks")
    parser.add_argument("--directory", type=Path, default=Path("/tmp/ccl-branch-profiles"))
    args = parser.parse_args()
    if args.self_test:
        self_test()
        return
    if not args.stage or not 1 <= args.seconds <= 180:
        parser.error("choose a stage and a 1–180 second diagnostic budget")
    if args.check_only and args.emit_code:
        parser.error("checking-only and artifact emission are separate measurements")
    if args.stage == "module":
        if not args.module or not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*", args.module):
            parser.error("choose a repository module with --module")
        module_path = ROOT / (args.module.replace(".", "/") + ".lean")
        if not module_path.is_file() or not module_path.resolve().is_relative_to(ROOT):
            parser.error("--module must select an existing repository Lean source")
    elif args.module:
        parser.error("--module requires --stage module")
    if args.source_file:
        if args.stage != "module" or not args.source_file.resolve().is_relative_to(Path("/tmp")):
            parser.error("--source-file requires --stage module and a file under /tmp")
        if args.dependency_prefix:
            parser.error("candidate sources and dependency overlays are separate probes")
    if args.dependency_prefix or args.dependency_module:
        if (args.stage != "module" or not args.dependency_prefix or not args.dependency_module
                or args.reuse_provenance):
            parser.error("dependency reuse requires a module, both dependency options, and no other prefix")
        if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*", args.dependency_module):
            parser.error("choose a repository dependency module")
        dependency_path = ROOT / (args.dependency_module.replace(".", "/") + ".lean")
        if not dependency_path.is_file() or not dependency_path.resolve().is_relative_to(ROOT):
            parser.error("--dependency-module must select an existing repository Lean source")
    directory = args.directory.resolve()
    if not directory.is_relative_to(Path("/tmp")):
        parser.error("probe outputs must be under /tmp")
    env = os.environ.copy()
    lean_path = subprocess.check_output([str(ROOT / "scripts/run-lake.sh"), "env",
                                        "printenv", "LEAN_PATH"], cwd=ROOT, text=True).strip()
    env["LEAN_PATH"] = lean_path
    lean = ROOT / ".elan/toolchains/leanprover--lean4---v4.32.2/bin/lean"
    source = (ROOT / (args.module.replace(".", "/") + ".lean")).read_text()
    if args.source_file:
        source = args.source_file.read_text()
    if args.dependency_prefix:
        prefix = args.dependency_prefix.resolve()
        expected = (ROOT / (args.dependency_module.replace(".", "/") + ".lean")).read_text()
        before = reload_provenance(prefix, expected, lean_path, lean)
        saved = json.loads((prefix / "result.json").read_text())
        if (saved["outcome"] != "success" or not (prefix / "Probe.olean").is_file()
                or (prefix / "Probe.lean").read_text() != expected):
            raise RuntimeError("dependency prefix is not the checked current repository module")
        direct_import = "import " + args.dependency_module + "\n"
        if source.count(direct_import) != 1:
            raise RuntimeError("dependency must be an explicit single-module direct import")
        source = source.replace(direct_import, "import Probe\n", 1)
        # Validate every other import and reject indirect imports of the original
        # dependency: those would create two copies of its declarations.
        other_source = source.replace("import Probe\n", "", 1)
        others = provenance(other_source, [Path(p) for p in lean_path.split(":")])
        original_path = str(ROOT / (args.dependency_module.replace(".", "/") + ".lean"))
        if original_path in others:
            raise RuntimeError("another import also loads the original dependency; overlay its closure first")
        before.update(others)
        before[str(prefix / "Probe.lean")] = digest(prefix / "Probe.lean")
        for artifact in prefix.glob("Probe.olean*"):
            before[str(artifact)] = digest(artifact)
        lean_path = str(prefix) + ":" + lean_path
        env["LEAN_PATH"] = lean_path
    else:
        before = (reload_provenance(args.reuse_provenance, source, lean_path, lean)
                  if args.reuse_provenance else
                  provenance(source, [Path(p) for p in lean_path.split(":")]))
    module = "Continuation" if args.dependency_prefix else "Probe"
    identity = {"schema": 1, "driver": digest(__file__), "source": source,
                "imports": before, "toolchain": (ROOT / "lean-toolchain").read_text(),
                "lean": digest(lean), "lean_path": lean_path,
                "seconds": args.seconds, "memory": args.memory, "cpu": "4",
                "check_only": args.check_only, "quiet": args.quiet,
                "native_stack": args.native_stack, "emit_code": args.emit_code}
    key = hashlib.sha256(json.dumps(identity, sort_keys=True).encode()).hexdigest()
    destination = directory / (args.stage + "-" + key[:16])

    def execute(out):
        atomic_json(out / "provenance.json", identity)
        (out / (module + ".lean")).write_text(source)
        command = ["systemd-run", "--user", "--wait", "--pipe", "--collect",
                   "-p", "MemoryMax=" + args.memory, "-p", "MemorySwapMax=0",
                   "--", "taskset", "-c", "4", "/usr/bin/time", "-v", "-o",
                   str(out / "resources.txt"), "timeout", "--signal=KILL",
                   str(args.seconds), "env", "LEAN_PATH=" + lean_path]
        if args.native_stack:
            command += ["gdb", "--batch", "-ex", "set pagination off", "-ex", "set confirm off",
                        "-ex", "set debuginfod enabled off", "-ex",
                        "python import threading,os,signal; threading.Timer(10,lambda:os.kill(os.getpid(),signal.SIGINT)).start()",
                        "-ex", "run", "-ex", "thread apply all bt 500",
                        "-ex", "quit", "--args"]
        command += [str(lean), "-R", str(out), "-DwarningAsError=true"]
        if not args.quiet:
            command += ["-Dtrace.profiler=true", "-Dtrace.profiler.threshold=100",
                        "-Ddiagnostics=true",
                        "-Dtrace.profiler.output=" + str(out / "profile.json")]
        if not args.check_only:
            command += ["-o", str(out / (module + ".olean"))]
        if args.emit_code:
            command += ["-c", str(out / (module + ".c")), "-i", str(out / (module + ".ilean"))]
        command.append(str(out / (module + ".lean")))
        atomic_json(out / "command.json", command)
        start = time.monotonic()
        with (out / "output.log").open("w") as log:
            code = subprocess.run(command, cwd=ROOT, env=env, stdout=log,
                                  stderr=subprocess.STDOUT).returncode
        elapsed = time.monotonic() - start
        after = {name: digest(name) for name in before}
        if before != after:
            raise RuntimeError("import provenance changed during probe; result not reusable")
        success = (not args.native_stack and code == 0
                   and (args.check_only or (out / (module + ".olean")).is_file()))
        if args.emit_code:
            success = success and all((out / (module + suffix)).is_file() for suffix in (".c", ".ilean"))
        return {"outcome": "success" if success else "inconclusive-or-error",
                "exit_code": code, "elapsed_seconds": elapsed,
                "last_completed_stage": args.stage if success else None,
                "stopping_reason": "native-stack-snapshot" if args.native_stack else
                    "completed" if success else "diagnostic-process-exit",
                "note": "A debugger exit or timeout is not a checked theorem. See output.log."}

    result = cached(destination, key, execute)
    print(json.dumps({"directory": str(destination), **result}, indent=2))


if __name__ == "__main__":
    main()
