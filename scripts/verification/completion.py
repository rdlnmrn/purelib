"""Run every completion gate, retaining the existing checkers' validated caches."""

from __future__ import annotations

import argparse
import fcntl
import os
from pathlib import Path
import selectors
import shlex
import shutil
import signal
import subprocess
import sys
import time

from scripts.paths import ROOT
from scripts.profiling.build_costs import atomic
from scripts.verification.checkpoints import Checkpoints, Inputs, execution_environment, source_snapshot as snapshot
from scripts.verification.preflight import run as run_preflight
from scripts.verification.preflight import source as release_source
from scripts.verification.processes import ChildScope, live_owned, observe, process_record, process_table, stop_tree

GIB = 1024**3
PROGRESS_INTERVAL = 30.0
STAGE_TIMEOUT = 300.0
AGGREGATE_STAGES = frozenset({"build", "tooling-tests", "lint", "axioms", "nanoda"})
TERMINATION_GRACE = 15.0
PROCESS_SAMPLE_INTERVAL = .25


def stages() -> list[tuple[str, list[str]]]:
    """Keep full proof scope and run each tooling regression once."""
    python = sys.executable
    return [
        ("source-policy", ["scripts/check-source.sh"]),
        ("build-surfaces", ["scripts/check-purelib-surfaces.py"]),
        ("build", ["scripts/run-lake.sh", "--quiet", "--wfail", "build"]),
        ("decimal-rendering", [".lake/build/bin/decimal_regression"]),
        ("unreserved-sharpness", [".lake/build/bin/unreserved_sharpness_regression"]),
        ("enclosure-observers", [".lake/build/bin/enclosure_observer_regression"]),
        ("cursor-continuations", [".lake/build/bin/ccl_cursor_continuation_regression"]),
        ("machine-simulation", [".lake/build/bin/machine_simulation_regression"]),
        ("observer-coverage", [".lake/build/bin/observer_coverage_regression"]),
        ("integration-replay", [".lake/build/bin/integration_replay_regression"]),
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
    env = execution_environment(environ)
    if available is not None and available <= 0:
        raise ValueError('no available memory headroom for completion checks')
    if env.get("NANODA_MODULE_MANIFEST"):
        raise ValueError("unset NANODA_MODULE_MANIFEST: completion requires the full inventory")
    # The three standalone cache regressions use assertions as checks.
    env.pop("PYTHONOPTIMIZE", None)
    env["PYTHONUNBUFFERED"] = "1"
    # Keep the pinned Lake scheduling workaround until an installed fix passes
    # full acceptance. Independent checker worker pools retain their parallelism.
    env.setdefault("LEAN_NUM_THREADS", "1")
    # Reserve a quarter of available memory and respect the repository's 250 GiB
    # combined-work budget. With no measurement, retain conservative defaults.
    budget = min(250 * GIB, available) * 3 // 4 if available is not None else None
    if budget == 0:
        raise ValueError('no available memory headroom after reserving worker overhead')
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
    env["CCL_CHECK_MEMORY_BYTES"] = str(budget if budget is not None else 24 * GIB)
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


def cgroup_memory_available(root=Path('/sys/fs/cgroup'), membership=Path('/proc/self/cgroup')):
    """Respect v2 memory limits at every ancestor, subtracting its current usage."""
    try:
        paths = [line.split(':', 2)[2] for line in membership.read_text().splitlines()
                 if line.startswith('0::')]
    except OSError:
        return None
    if not paths:
        return None
    relative = Path(paths[0].lstrip('/'))
    if '..' in relative.parts:
        raise ValueError('invalid cgroup membership path')
    directory = root / relative
    bounds = []
    while True:
        for name in ('memory.max', 'memory.high'):
            try:
                value = (directory / name).read_text().strip()
            except OSError:
                continue
            if value != 'max':
                try:
                    used = int((directory / 'memory.current').read_text())
                    limit = int(value)
                except (OSError, ValueError) as error:
                    raise ValueError('cannot determine cgroup memory headroom') from error
                bounds.append(max(0, limit - used))
        if directory == root:
            break
        directory = directory.parent
    return min(bounds) if bounds else None


def available_memory() -> int | None:
    """Bound worker pools by both host availability and inherited cgroup limits."""
    host = None
    try:
        fields = dict(line.split(":", 1) for line in Path("/proc/meminfo").read_text().splitlines())
        host = int(fields["MemAvailable"].split()[0]) * 1024
    except (OSError, KeyError, ValueError):
        pass
    group = cgroup_memory_available()
    values = [value for value in (host, group) if value is not None]
    return min(values) if values else None


def run_stage(name: str, command: list[str], directory: Path, env: dict[str, str], root: Path) -> dict:
    """Supervise one stage, preserve its raw exit and stop retained descendants."""
    with ChildScope(grace=TERMINATION_GRACE) as owner:
        return _run_stage(name, command, directory, env, root, owner)


def _run_stage(name, command, directory, env, root, owner):
    """Run a stage inside the caller's exclusive child-adoption scope."""
    # Aggregate gates may outlast five minutes. Module workers enforce their
    # own deadline; retain cancellation and descendant supervision here.
    timeout_seconds = None if name in AGGREGATE_STAGES else STAGE_TIMEOUT
    log_path = directory / (name + ".log")
    print(f"\n[{name}] {shlex.join(command)}", flush=True)
    started = time.monotonic()
    timed_out = False
    errors = []
    code = None
    with log_path.open("wb") as log:
        process = subprocess.Popen(command, cwd=root, env=env, stdout=subprocess.PIPE,
                                   stderr=subprocess.STDOUT, start_new_session=True)
        process.verification_owner = owner
        identity = process_record(process.pid)
        known = {process.pid: identity[0]} if identity else {}

        def record_exit(raw_code):
            nonlocal code
            if code is None:
                code = raw_code
                atomic(directory / (name + "-exit.json"), {"raw_exit_code": raw_code})

        def stop_owned():
            deadline = time.monotonic() + TERMINATION_GRACE
            record_exit(stop_tree(process, known, TERMINATION_GRACE))
            owner.reap(terminate=True, deadline=deadline)

        try:
            assert process.stdout is not None
            last_output = started
            next_progress = started + PROGRESS_INTERVAL
            with selectors.DefaultSelector() as selector:
                selector.register(process.stdout, selectors.EVENT_READ)
                while selector.get_map() or process.poll() is None:
                    returned = process.poll()
                    if returned is not None:
                        record_exit(returned)
                    observe(process, known, process_table())
                    if returned is not None and live_owned(known):
                        errors.append("stage exited while owned descendants remained live")
                        stop_owned()
                    now = time.monotonic()
                    if timeout_seconds is not None and not timed_out and now - started >= timeout_seconds:
                        timed_out = True
                        print(f"\n[{name}] exceeded {timeout_seconds:g}s; stopping owned processes", flush=True)
                        stop_owned()
                    timeout = max(0, min(next_progress - time.monotonic(),
                                         timeout_seconds - (time.monotonic() - started)
                                         if timeout_seconds is not None and not timed_out else PROCESS_SAMPLE_INTERVAL,
                                         PROCESS_SAMPLE_INTERVAL))
                    if selector.get_map():
                        for key, _ in selector.select(timeout):
                            block = os.read(key.fd, 65536)
                            if not block:
                                selector.unregister(key.fileobj)
                                continue
                            log.write(block)
                            log.flush()
                            sys.stdout.buffer.write(block)
                            sys.stdout.buffer.flush()
                            last_output = time.monotonic()
                    else:
                        # A child can close stdout before finishing its work.
                        try:
                            record_exit(process.wait(timeout=timeout))
                            break
                        except subprocess.TimeoutExpired:
                            pass
                    now = time.monotonic()
                    if now >= next_progress and (selector.get_map() or process.poll() is None):
                        print(f"\n[{name}] still running ({now - started:.0f}s elapsed; "
                              f"{now - last_output:.0f}s since last output)", flush=True)
                        next_progress = now + PROGRESS_INTERVAL
            record_exit(process.wait())
            observe(process, known, process_table())
            if live_owned(known) and not errors:
                errors.append("stage exited while owned descendants remained live")
                stop_owned()
            if live_owned(known):
                errors.append("owned descendants survived termination")
            owner.reap()
        except BaseException:
            stop_owned()
            raise
        finally:
            if process.stdout is not None:
                process.stdout.close()
    elapsed = time.monotonic() - started
    result_code = 124 if timed_out else 1 if errors else code
    print(f"[{name}] {'passed' if result_code == 0 else 'FAILED'} in {elapsed:.1f}s; {log_path}", flush=True)
    return {"name": name, "command": command, "exit_code": result_code, "raw_exit_code": code,
            "timed_out": timed_out, "wall_timeout_seconds": timeout_seconds,
            "errors": errors, "seconds": elapsed, "log": str(log_path)}


def execute(plan: list[tuple[str, list[str]]], directory: Path, env: dict[str, str], root: Path = ROOT,
            *, resume=False, finalize=None) -> int:
    """Fail at the first failed gate, reusing only content-bound completed work."""
    if not plan or len({name for name, _ in plan}) != len(plan):
        raise ValueError('completion requires a nonempty plan with unique stage names')
    env = execution_environment(env)
    inputs = snapshot(root)
    results = []
    report = {"status": "running", "inputs": inputs, "stages": results,
              "workers": {key: env.get(key) for key in (
                  "CCL_CHECK_CORES", "CCL_CHECK_MEMORY_BYTES", "CCL_TOOLING_JOBS",
                  "LEAN_NUM_THREADS", "AXIOM_AUDIT_JOBS", "CCL_LINT_JOBS",
                  "NANODA_EXPORT_JOBS", "NANODA_POST_EXPORT_CHECKS", "NANODA_JOBS", "NANODA_PIPELINE")}}
    env = dict(env, CCL_COMPLETION_REPORT=str(directory), CCL_CHECK_RESUME='1' if resume else '0')
    checkpoints = Checkpoints(root / '.lake/completion-checkpoints/stages') if resume else None
    bindings = Inputs(root, env, checkpoints) if resume else None
    atomic(directory / "summary.json", report)
    try:
        for name, command in plan:
            # Build and proof gates retain their own finer-grained currentness
            # checks. Tooling resumes individual cases, not a whole-suite flag.
            reusable = checkpoints is not None and name not in AGGREGATE_STAGES
            request = bindings.request(name, command) if reusable else None
            result = checkpoints.lookup(request) if reusable else None
            if result is not None:
                print(f'[{name}] reusing validated completed check', flush=True)
            else:
                result = run_stage(name, command, directory, env, root)
                result['reused'] = False
                if reusable and result['exit_code'] == 0:
                    if bindings.request(name, command) != request:
                        raise ValueError('stage inputs changed during checks: ' + name)
                    checkpoints.save(request, result)
            results.append(result)
            atomic(directory / "summary.json", report)
            if result["exit_code"]:
                report["status"] = "failed"
                return result["exit_code"] if result["exit_code"] > 0 else 128 - result["exit_code"]
        if inputs != snapshot(root):
            raise ValueError("repository files changed during checks; rerun on the final tree")
        if finalize is not None:
            finalize()
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
    parser.add_argument('--resume', action='store_true', help='reuse validated stages and individual tooling cases')
    parser.add_argument('--release', metavar='TAG', help='preflight publication history and access for this release')
    args = parser.parse_args(argv)
    if args.max_cores is not None and args.max_cores < 1:
        parser.error("--max-cores must be positive")
    plan = stages()
    if args.list:
        if args.release is not None:
            print('publication-preflight: ' + shlex.join(
                ['scripts/maintenance/public-history.sh', 'preflight', args.release]))
        print('socket-preflight: local socketpair and Unix listener handshake')
        print('nanoda-preflight: scripts/build-nanoda-module-checker.sh')
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
                  f"Lean threads={env['LEAN_NUM_THREADS']}, audit environments={env['AXIOM_AUDIT_JOBS']}, "
                  f"lint workers={env['CCL_LINT_JOBS']}, nanoda exporters={env['NANODA_EXPORT_JOBS']}, "
                  f"checkers={env['NANODA_POST_EXPORT_CHECKS']} × {env['NANODA_JOBS']} threads", flush=True)
            prerequisites = run_preflight(ROOT, directory, env, release=args.release)
            finalize = None
            if args.release is not None:
                expected = prerequisites['steps'][0]['source_commit']
                finalize = lambda: release_source(ROOT, expected)
            return execute(plan, directory, env, resume=args.resume, finalize=finalize)
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
