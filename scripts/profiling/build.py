#!/usr/bin/env python3
"""Dispatch --profile and --cold for the repository's Lake build wrapper."""

from __future__ import annotations

import fcntl
import math
import os
from pathlib import Path
import subprocess
import signal
import sys
import time

from scripts.profiling.build_costs import Digests, Probes, atomic, stop_owned, timings

from scripts.paths import ROOT
VALUE_OPTIONS = {"-d", "--dir", "-f", "--file", "-K", "--config",
                 "--log-level", "--fail-level"}


def flags(args: list[str]) -> tuple[list[str], bool, bool]:
    """Consume wrapper flags without reinterpreting values or arguments after --."""
    result = []
    profile = cold = False
    i = 0
    command_seen = False
    while i < len(args):
        arg = args[i]
        if arg == "--":
            result += args[i:]
            break
        if arg == "--profile":
            profile = True
        elif arg == "--cold":
            cold = True
        elif arg in VALUE_OPTIONS:
            result += args[i:i + 2]
            i += 1
        else:
            if not command_seen and not arg.startswith("-"):
                if arg != "build":
                    result += args[i:]
                    break
                command_seen = True
            result.append(arg)
        i += 1
    return result, profile, cold


def is_project_build(args: list[str]) -> bool:
    i = 0
    while i < len(args):
        arg = args[i]
        if arg in {"-d", "--dir", "-f", "--file", "--no-build", "--", "--help", "-h"}:
            return False
        if arg.startswith(("--dir=", "--file=")):
            return False
        if arg in VALUE_OPTIONS:
            i += 2
        elif arg.startswith("-"):
            i += 1
        else:
            return arg == "build" and not any(x in {"--help", "-h"} for x in args[i + 1:])
    return False


def writer_lock(args: list[str]):
    """Serialize repository build writers, including diagnostic artifact readers."""
    cwd = Path.cwd().resolve()
    if not is_project_build(args) or (cwd != ROOT and ROOT not in cwd.parents):
        return None
    path = ROOT / ".lake/BUILD.lock"
    path.parent.mkdir(parents=True, exist_ok=True)
    lock = path.open("a+b")
    try:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError:
        lock.close()
        raise ValueError("another repository build/profile is running; serialize these invocations")
    os.set_inheritable(lock.fileno(), True)
    return lock


def inventory() -> list[str]:
    return subprocess.check_output(
        [sys.executable, ROOT / "scripts/project-modules.py", "--configured-scripts"],
        cwd=ROOT, text=True).splitlines()


def source_hashes(modules: list[str]) -> dict[str, str]:
    digests = Digests()
    return {module: digests.sha(ROOT / (module.replace(".", "/") + ".lean")) for module in modules}


def execute(args: list[str], profile: bool, cold: bool) -> int:
    cwd = Path.cwd().resolve()
    if not is_project_build(args) or (cwd != ROOT and ROOT not in cwd.parents):
        raise ValueError("--profile and --cold require this repository's build command")
    jobs = int(os.environ.get("CCL_PROFILE_JOBS", "4"))
    threads = int(os.environ.get("LEAN_NUM_THREADS", "8"))
    threshold = float(os.environ.get("CCL_PROFILE_THRESHOLD", "5"))
    if not 1 <= jobs <= 4 or threads < 1 or not math.isfinite(threshold) or threshold < 0:
        raise ValueError("profiling requires 1..4 workers, positive threads and a nonnegative threshold")
    modules = inventory()
    if not modules or len(modules) != len(set(modules)):
        raise ValueError("empty or duplicate project inventory")
    stamp = time.strftime("%Y%m%dT%H%M%SZ", time.gmtime())
    directory = ROOT / ".lake/build-profiles" / (stamp + f"-{time.time_ns()}")
    directory.mkdir(parents=True)
    sources = source_hashes(modules)
    digest = Digests()
    configuration = [ROOT / p for p in ("lakefile.toml", "lake-manifest.json", "lean-toolchain",
                                        "scripts/toolchain/config.json", "scripts/run-lake.sh",
                                        "scripts/profiling/build.py", "scripts/profiling/build_costs.py")]
    configuration_hashes = {str(p): digest.sha(p) for p in configuration if p.is_file()}
    inputs = {"revision": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
              "modules": modules, "source_sha256": sources, "command": args,
              "lean_num_threads": threads, "profile": profile, "cold": cold,
              "cold_scope": "Project artifacts absent; toolchain, dependency and OS caches retained.",
              "profile_threshold_seconds": threshold, "profile_jobs": jobs}
    inputs["configuration_sha256"] = configuration_hashes
    atomic(directory / "inputs.json", inputs)
    build = ROOT / ".lake/build"
    if cold and build.exists():
        build.rename(directory / "preserved-build")
    command = [str(ROOT / "scripts/run-lake.sh"), *args]
    if cold and "--no-cache" not in args:
        command.insert(1, "--no-cache")
    # Child wrapper dispatch is suppressed, retaining provider preparation and
    # the ordinary Lake invocation. Cache downloads cannot defeat cold mode.
    env = {**os.environ, "CCL_BUILD_PROFILE_DRIVER": "1", "LEAN_NUM_THREADS": str(threads)}
    print(f"Build report: {directory}", flush=True)
    started = time.monotonic()
    with (directory / "build.log").open("w") as log:
        process = subprocess.Popen(command, cwd=ROOT, env=env, stdout=subprocess.PIPE,
                                   stderr=subprocess.STDOUT, text=True, start_new_session=True)
        assert process.stdout is not None
        try:
            for line in process.stdout:
                log.write(line)
                print(line, end="", flush=True)
            code = process.wait()
        except BaseException:
            stop_owned(process)
            raise
        finally:
            process.stdout.close()
    elapsed = time.monotonic() - started
    atomic(directory / "result.json", {"exit_code": code, "wall_seconds": elapsed})
    if code:
        print(f"Build failed; diagnostics were not run. Log: {directory / 'build.log'}", file=sys.stderr)
        return code
    if sources != source_hashes(modules):
        raise ValueError(f"sources changed during the build; report is invalid: {directory}")
    if any(digest.sha(Path(p)) != expected for p, expected in configuration_hashes.items()):
        raise ValueError(f"build configuration changed; report is invalid: {directory}")
    measured = timings((directory / "build.log").read_text(), modules)
    if cold and set(measured) != set(modules) and "build" == args[-1]:
        raise ValueError("unscoped cold build did not freshly time every configured project module")
    summary = {"exit_code": code, "wall_seconds": elapsed, "module_count": len(modules),
               "module_seconds": measured, "summed_module_seconds": sum(measured.values()),
               "unmeasured_modules": sorted(set(modules) - measured.keys()),
               "at_least_five_seconds": sum(t >= 5 for t in measured.values()),
               "over_thirty_seconds": sum(t > 30 for t in measured.values())}
    atomic(directory / "summary.json", summary)
    print(f"Build wall time: {elapsed:.2f}s; freshly timed modules: {len(measured)}/{len(modules)}")
    slow = sorted((m for m, t in measured.items() if t >= threshold), key=lambda m: -measured[m])
    for module in sorted(measured, key=lambda m: -measured[m])[:10]:
        print(f"  {measured[module]:7.3f}s  {module}")
    diagnostics = []
    if profile and slow:
        print(f"Profiling {len(slow)} modules at or above {threshold:g}s, with {jobs} workers.", flush=True)
        probes = Probes(ROOT, ROOT / ".lake/build-profiles/probe-cache", threads)
        diagnostics = probes.selected(slow, jobs)
        atomic(directory / "diagnostics.json", diagnostics)
        print("Quiet replay estimates: imports/setup | declarations (elaboration + kernel) | artifact emission")
        for row in diagnostics:
            if row["valid_quiet_runs"]:
                print(f"  {row['estimated_import_setup_seconds']:6.2f}s | "
                      f"{row['estimated_declaration_seconds']:6.2f}s | "
                      f"{row['estimated_emission_seconds']:6.2f}s  {row['module']}")
            else:
                print(f"  Diagnostic replay failed: {row['module']}")
            if row["runs"]["profile"]["exit_code"]:
                print("    Profiler failed; inspect its log. Ordinary limits were retained.")
            hotspots = [f for f in row["runs"]["profile"]["frames"] if f["kind"] != "Elab.step"]
            for frame in hotspots[:3]:
                print(f"    {frame['seconds']:.2f}s [{frame['kind']}] {frame['label'][:160]}")
        print("Separate-run differences are estimates; nested profiler frames overlap.")
    elif profile:
        print("No newly built project modules crossed the profiling threshold.")
    print(f"Report retained in {directory}")
    return 1 if any(not row["valid_quiet_runs"] for row in diagnostics) else 0


def main() -> int:
    args, profile, cold = flags(sys.argv[1:])
    lock = None
    try:
        lock = writer_lock(args)
        if not profile and not cold:
            env = {**os.environ, "CCL_BUILD_PROFILE_DRIVER": "1"}
            if args in (["--help"], ["-h"]):
                print("Repository build options: --profile (diagnostic cost breakdown), --cold (fresh project artifacts).",
                      flush=True)
            os.execve(ROOT / "scripts/run-lake.sh", [str(ROOT / "scripts/run-lake.sh"), *args], env)
        return execute(args, profile, cold)
    except (ValueError, OSError, KeyError) as error:
        print(f"build profiling failed: {error}", file=sys.stderr)
        return 1
    except KeyboardInterrupt:
        print("Build profiling interrupted; completed checkpoints and preserved artifacts remain.", file=sys.stderr)
        return 130
    finally:
        if lock is not None:
            lock.close()


if __name__ == "__main__":
    def interrupt(signum, frame):
        raise KeyboardInterrupt
    signal.signal(signal.SIGTERM, interrupt)
    raise SystemExit(main())
