"""Run every completion gate, retaining the existing checkers' validated caches."""

from __future__ import annotations

import argparse
import fcntl
import hashlib
import os
from pathlib import Path
import shlex
import shutil
import signal
import subprocess
import sys
import time

from scripts.paths import ROOT
from scripts.profiling.build_costs import atomic, stop_owned

GIB = 1024**3


def stages() -> list[tuple[str, list[str]]]:
    """Keep full proof scope and run each tooling regression once."""
    python = sys.executable
    return [
        ("source-policy", ["scripts/check-source.sh"]),
        ("build-surfaces", ["scripts/check-purelib-surfaces.py"]),
        ("build", ["scripts/run-lake.sh", "--quiet", "--wfail", "build"]),
        ("unreserved-sharpness", [".lake/build/bin/unreserved_sharpness_regression"]),
        ("tooling-tests", ["scripts/run-lake.sh", "env", python, "-m",
                          "scripts.verification.tooling"]),
        *[(name, [python, "-m", "scripts.test.nanoda." + module]) for name, module in [
            ("checker-cache-tests", "test_check_cache"),
            ("input-cache-tests", "test_input_key"),
            ("graph-cache-tests", "test_graph_cache"),
        ]],
        ("restart-tests", [python, "-m", "scripts.profiling.branch_builds", "--self-test"]),
        ("projection-tests", ["scripts/check-prepared-projections.sh", "--models"]),
        ("lint", ["scripts/run-lake.sh", "--no-build", "--wfail", "lint"]),
        ("axioms", ["scripts/check-axioms.sh", "--configured-scripts", "--full"]),
        ("nanoda", ["scripts/check-nanoda.sh"]),
    ]


def environment(environ: dict[str, str], cpus: int, available: int | None) -> dict[str, str]:
    """Budget serialized stages and both simultaneous nanoda pools."""
    env = dict(environ)
    if env.get("NANODA_MODULE_MANIFEST"):
        raise ValueError("unset NANODA_MODULE_MANIFEST: completion requires the full inventory")
    # The three standalone cache regressions use assertions as checks.
    env.pop("PYTHONOPTIMIZE", None)
    # Keep the pinned Lake scheduling workaround until an installed fix passes
    # full acceptance. Independent checker worker pools retain their parallelism.
    env.setdefault("LEAN_NUM_THREADS", "1")
    # Reserve a quarter of available memory and respect the repository's 250 GiB
    # combined-work budget. With no measurement, retain conservative defaults.
    budget = min(250 * GIB, available) * 3 // 4 if available is not None else None
    audit = min(cpus, max(1, budget // (12 * GIB))) if budget is not None else min(cpus, 2)
    lint = min(cpus, max(1, budget // (2 * GIB))) if budget is not None else min(cpus, 8)
    def bounded(key: str, default: int, ceiling: int) -> int:
        value = env.get(key, "auto")
        number = default if value == "auto" else int(value)
        if number < 1:
            raise ValueError(f"{key} must be a positive integer")
        number = min(number, ceiling)
        env[key] = str(number)
        return number

    bounded("LEAN_NUM_THREADS", 1, cpus)
    bounded("AXIOM_AUDIT_JOBS", audit, audit)
    bounded("CCL_LINT_JOBS", lint, lint)
    bounded("CCL_TOOLING_JOBS", cpus, cpus)
    env["CCL_CHECK_CORES"] = str(cpus)
    env["CCL_CHECK_MEMORY_BYTES"] = str(budget or 24 * GIB)
    # Cold full-inventory measurements reached 12.4 GiB per nanoda process.
    # Reserve 16 GiB per exporter/checker, including overlap between the pools.
    slots = max(1, budget // (16 * GIB)) if budget is not None else 2
    threads = bounded("NANODA_JOBS", 2, max(2, cpus))
    # Two checker threads retain normal worker stacks even on a single core.
    if threads < 2:
        raise ValueError("NANODA_JOBS must be at least 2 for the pinned checker worker stacks")
    if cpus <= threads or slots < 3 or env.get("NANODA_PIPELINE") == "0":
        env["NANODA_PIPELINE"] = "0"
        bounded("NANODA_EXPORT_JOBS", min(cpus, slots), min(cpus, slots))
        bounded("NANODA_POST_EXPORT_CHECKS", max(1, min(cpus // threads, slots)),
                max(1, min(cpus // threads, slots)))
    else:
        exporters = bounded("NANODA_EXPORT_JOBS", max(1, min(cpus // 3, slots // 3)),
                            min(cpus - threads, slots - 1))
        checkers = max(1, min((cpus - exporters) // threads, slots - exporters))
        bounded("NANODA_POST_EXPORT_CHECKS", checkers, checkers)
    return env


def available_memory() -> int | None:
    """Read currently available host memory for pool sizing."""
    try:
        fields = dict(line.split(":", 1) for line in Path("/proc/meminfo").read_text().splitlines())
        return int(fields["MemAvailable"].split()[0]) * 1024
    except (OSError, KeyError, ValueError):
        return None


def snapshot(root: Path) -> dict[str, str]:
    """Bind tracked and unignored new files, including dirty source and tooling."""
    names = subprocess.check_output(
        ["git", "ls-files", "-z", "--cached", "--others", "--exclude-standard"], cwd=root)
    result = {}
    for raw in set(names.split(b"\0")) - {b""}:
        name = os.fsdecode(raw)
        path = root / name
        if path.is_symlink():
            result[name] = "symlink:" + os.readlink(path)
        elif path.exists():
            with path.open("rb") as stream:
                result[name] = hashlib.file_digest(stream, "sha256").hexdigest()
        else:
            result[name] = "missing"
    return result


def run_stage(name: str, command: list[str], directory: Path, env: dict[str, str], root: Path) -> dict:
    """Stream one gate's output to the terminal and its retained log."""
    log_path = directory / (name + ".log")
    print(f"\n[{name}] {shlex.join(command)}", flush=True)
    started = time.monotonic()
    with log_path.open("wb") as log:
        process = subprocess.Popen(command, cwd=root, env=env, stdout=subprocess.PIPE,
                                   stderr=subprocess.STDOUT, start_new_session=True)
        try:
            assert process.stdout is not None
            while block := process.stdout.read1(65536):
                log.write(block)
                log.flush()
                sys.stdout.buffer.write(block)
                sys.stdout.buffer.flush()
            code = process.wait()
        except BaseException:
            stop_owned(process)
            raise
        finally:
            if process.stdout is not None:
                process.stdout.close()
    elapsed = time.monotonic() - started
    print(f"[{name}] {'passed' if code == 0 else 'FAILED'} in {elapsed:.1f}s; {log_path}", flush=True)
    return {"name": name, "command": command, "exit_code": code, "seconds": elapsed,
            "log": str(log_path)}


def execute(plan: list[tuple[str, list[str]]], directory: Path, env: dict[str, str], root: Path = ROOT) -> int:
    """Fail at the first failed gate; never treat a prior run's summary as a cache."""
    inputs = snapshot(root)
    results = []
    report = {"status": "running", "inputs": inputs, "stages": results,
              "workers": {key: env.get(key) for key in (
                  "CCL_CHECK_CORES", "CCL_CHECK_MEMORY_BYTES", "CCL_TOOLING_JOBS",
                  "LEAN_NUM_THREADS", "AXIOM_AUDIT_JOBS", "CCL_LINT_JOBS",
                  "NANODA_EXPORT_JOBS", "NANODA_POST_EXPORT_CHECKS", "NANODA_JOBS", "NANODA_PIPELINE")}}
    env = dict(env, CCL_COMPLETION_REPORT=str(directory))
    atomic(directory / "summary.json", report)
    try:
        for name, command in plan:
            result = run_stage(name, command, directory, env, root)
            results.append(result)
            atomic(directory / "summary.json", report)
            if result["exit_code"]:
                report["status"] = "failed"
                return result["exit_code"] if result["exit_code"] > 0 else 128 - result["exit_code"]
        if inputs != snapshot(root):
            raise ValueError("repository files changed during checks; rerun on the final tree")
        report["status"] = "passed"
        print(f"\nAll {len(results)} completion gates passed. Report: {directory}", flush=True)
        return 0
    except KeyboardInterrupt:
        report["status"] = "interrupted"
        return 130
    except BaseException:
        report["status"] = "failed"
        raise
    finally:
        atomic(directory / "summary.json", report)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--list", action="store_true", help="show the complete commands without running them")
    parser.add_argument("--max-cores", type=int, help="maximum CPU cores for the entire process tree (default: all available)")
    args = parser.parse_args(argv)
    if args.max_cores is not None and args.max_cores < 1:
        parser.error("--max-cores must be positive")
    plan = stages()
    if args.list:
        for name, command in plan:
            print(f"{name}: {shlex.join(command)}")
        return 0
    try:
        affinity = sorted(os.sched_getaffinity(0)) if hasattr(os, "sched_getaffinity") else None
        cpus = len(affinity) if affinity is not None else os.cpu_count() or 1
        cpus = min(cpus, args.max_cores or cpus)
        if affinity is not None:
            # Every child and grandchild inherits this restriction, including
            # compiler and Rust threads outside our explicit worker pools.
            os.sched_setaffinity(0, affinity[:cpus])
        env = environment(dict(os.environ), cpus, available_memory())
        checker = env.get("NANODA_BIN") or str(ROOT / ".external/nanoda/target/release/nanoda_bin")
        if not (Path(checker).is_file() and os.access(checker, os.X_OK)):
            checker = shutil.which(env.get("NANODA_BIN") or "nanoda_bin", path=env.get("PATH")) or ""
        if not checker:
            raise ValueError("missing nanoda: build the pinned checker or set NANODA_BIN before running checks")
        env["NANODA_BIN"] = str(Path(checker).resolve())
        base = ROOT / ".lake/completion-checks"
        base.mkdir(parents=True, exist_ok=True)
        with (base / "lock").open("a+b") as lock:
            try:
                fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
            except BlockingIOError:
                raise ValueError("another completion-check run is active in this worktree") from None
            directory = base / f"{time.strftime('%Y%m%dT%H%M%SZ', time.gmtime())}-{time.time_ns()}"
            directory.mkdir()
            print(f"Completion report: {directory}\nCore limit={cpus}, tooling workers={env['CCL_TOOLING_JOBS']}, "
                  f"Lean threads={env['LEAN_NUM_THREADS']}, audit workers={env['AXIOM_AUDIT_JOBS']}, "
                  f"lint workers={env['CCL_LINT_JOBS']}, nanoda exporters={env['NANODA_EXPORT_JOBS']}, "
                  f"checkers={env['NANODA_POST_EXPORT_CHECKS']} × {env['NANODA_JOBS']} threads", flush=True)
            return execute(plan, directory, env)
    except (OSError, ValueError) as error:
        print(f"completion checks failed: {error}", file=sys.stderr)
        return 1
    except KeyboardInterrupt:
        return 130


if __name__ == "__main__":
    def interrupt(signum, frame):
        raise KeyboardInterrupt

    signal.signal(signal.SIGTERM, interrupt)
    raise SystemExit(main())
