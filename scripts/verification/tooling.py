"""Distribute every discovered tooling regression over isolated worker processes."""

from __future__ import annotations

import argparse
import json
import math
import os
from pathlib import Path
import signal
import subprocess
import sys
import time
import unittest

from scripts.paths import ROOT
from scripts.profiling.build_costs import atomic
from scripts.verification.checkpoints import Checkpoints, Inputs, execution_environment
from scripts.verification.preflight import tooling as preflight_tooling
from scripts.verification.processes import live_owned, observe, process_record, process_table, stop_tree

GIB = 1024**3
TEST_TIMEOUT = 300.0
TIMEOUT_OVERRIDES_ENV = 'CCL_TOOLING_TIMEOUT_OVERRIDES'
TERMINATION_GRACE = 15.0
HORNER_CASE_PREFIX = "scripts.test.lean_module_data.test_kernel_equivalence.SuppliedHornerTests."
# These modules have been checked to use temporary fixtures and small imports.
# New modules receive the conservative whole-host-audit reservation until reviewed.
LIGHT_MODULES = {
    "experiments.test_finite_search",
    "axioms.test_graph", "axioms.test_orchestration", "axioms.test_parallel", "axioms.test_propext_frontier", "axioms.test_trace",
    "generators.test_sewing", "lean_module_data.test_reader",
    "linting.test_runner", "module_style.test_contracts", "module_style.test_core",
    "maintenance.test_worktrees",
    "profiling.test_build_costs",
    "toolchain.test_module_guard", "verification.test_module_process",
    "nanoda.test_benchmark_pipeline", "nanoda.test_check_stream", "nanoda.test_compare_exports",
    "nanoda.test_export_validation", "nanoda.test_planning", "nanoda.test_policy",
    "nanoda.test_root_inventory", "nanoda.test_scheduling",
    "nanoda.test_modules",
    "verification.test_authored_names", "verification.test_checkpoints", "verification.test_completion",
    "verification.test_preflight",
    "verification.test_declarations", "verification.test_imports",
    "verification.test_namespace_prefixes",
    "verification.test_prepared_projections", "verification.test_reader_provenance",
    "verification.test_source_policy",
    "verification.test_surfaces", "verification.test_tooling",
}


def inventory() -> list[str]:
    """Discover the same complete inventory as unittest's ordinary discovery."""
    loader = unittest.TestLoader()
    suite = loader.discover(str(ROOT / "scripts/test"), "test_*.py", str(ROOT))
    def flatten(tests):
        for test in tests:
            if isinstance(test, unittest.TestSuite):
                yield from flatten(test)
            else:
                yield test.id()
    names = list(flatten(suite))
    if loader.errors or not names or len(names) != len(set(names)):
        raise ValueError("empty, duplicate or failed tooling discovery: " + "\n".join(loader.errors))
    return names


def reservation(name: str) -> int:
    """Reserve memory for small fixtures or complete decoded audit imports."""
    module = name.removeprefix("scripts.test.").rsplit(".", 2)[0]
    return (2 if module in LIGHT_MODULES else 12) * GIB


def timeout_overrides(names, environment):
    """Select explicitly configured, finite deadlines for exact discovered cases."""
    values = json.loads(environment.get(TIMEOUT_OVERRIDES_ENV, '{}'))
    if not isinstance(values, dict) or set(values) - set(names):
        raise ValueError('tooling timeout overrides require exact discovered case names')
    for seconds in values.values():
        if (isinstance(seconds, bool) or not isinstance(seconds, (int, float)) or
                not 0 < seconds <= 600 or not math.isfinite(seconds)):
            raise ValueError('tooling case timeouts must be finite numbers in (0, 600]')
    return values


def worker_environment(name: str) -> dict[str, str]:
    """Give only actual Horner cases the owned session's authenticated socket."""
    env = execution_environment(os.environ, isolated_case=True)
    # Isolated subprocesses do not inherit the descriptor protocol. Other
    # fixtures own their own sessions, including deliberate native crashes.
    env.pop("FC_SUPPLIED_SESSION_FD", None)
    env.pop('CCL_CHECK_RESUME', None)
    env.pop(TIMEOUT_OVERRIDES_ENV, None)
    if not name.startswith(HORNER_CASE_PREFIX):
        env.pop("FC_SUPPLIED_SESSION_PATH", None)
    return env


def run_jobs(jobs: list[tuple[str, list[str], int]], directory: Path,
             workers: int, memory: int, *, checkpoints=None, requests=None, validate=None,
             case_timeouts=None) -> int:
    """Keep cores busy within the memory budget; retain exact test coverage and logs."""
    if not jobs or len({name for name, _, _ in jobs}) != len(jobs) or min(workers, memory) < 1:
        raise ValueError("nonempty unique jobs and positive resource budgets are required")
    case_timeouts = timeout_overrides([job[0] for job in jobs], {
        TIMEOUT_OVERRIDES_ENV: json.dumps({} if case_timeouts is None else case_timeouts)})
    if checkpoints is not None and (requests is None or set(requests) != {job[0] for job in jobs} or validate is None):
        raise ValueError('checkpointing requires exact requests and input validation for every job')
    directory.mkdir(parents=True, exist_ok=True)
    affinity = sorted(os.sched_getaffinity(0)) if hasattr(os, "sched_getaffinity") else None
    workers = min(workers, len(affinity)) if affinity else workers
    free = list(range(workers))
    pending = sorted(enumerate(jobs), key=lambda item: -item[1][2])
    running = {}
    report = {"status": "running", "inventory": [job[0] for job in jobs], "results": [],
              "workers": workers, "memory_budget_bytes": memory, "peak_workers": 0,
              "default_case_timeout_seconds": TEST_TIMEOUT,
              "case_timeout_overrides": case_timeouts,
              "sampled_peak_combined_rss_bytes": 0}
    try:
        if checkpoints is not None:
            unresolved = []
            for index, job in pending:
                saved = checkpoints.lookup(requests[job[0]])
                if saved is None:
                    unresolved.append((index, job))
                else:
                    report['results'].append(saved)
                    print(f"Reusing completed tooling case: {job[0]}", flush=True)
            pending = unresolved
        atomic(directory / 'summary.json', report)
        last_sample = 0.0
        while pending or running:
            used = sum(row["memory"] for row in running.values())
            while free and pending:
                candidate = next((i for i, (_, job) in enumerate(pending)
                                  if min(job[2], memory) <= memory - used), None)
                if candidate is None:
                    break
                index, (name, command, cost) = pending.pop(candidate)
                cost = min(cost, memory)  # A small host still runs one heavy fixture.
                core = free.pop()
                log_path = directory / f"{index:04d}.log"
                with log_path.open("wb") as log:
                    pin = (lambda cpu=affinity[core]: os.sched_setaffinity(0, {cpu})) if affinity else None
                    process = subprocess.Popen(command, cwd=ROOT, stdout=log, preexec_fn=pin,
                                               stderr=subprocess.STDOUT, start_new_session=True,
                                               env=worker_environment(name))
                identity = process_record(process.pid)
                running[process] = {"name": name, "command": command, "memory": cost,
                                    "core": core, "log": str(log_path), "started": time.monotonic(),
                                    "timeout": case_timeouts.get(name, TEST_TIMEOUT),
                                    "known": {process.pid: identity[0]} if identity else {}}
                used += cost
                report["peak_workers"] = max(report["peak_workers"], len(running))
            if time.monotonic() - last_sample >= .25:
                table = process_table()
                owned = set()
                for process, row in running.items():
                    owned.update(observe(process, row["known"], table))
                report["sampled_peak_combined_rss_bytes"] = max(
                    report["sampled_peak_combined_rss_bytes"], sum(table[pid]["rss"] for pid in owned))
                last_sample = time.monotonic()
            for process, row in list(running.items()):
                raw_code = process.poll()
                timed_out = raw_code is None and time.monotonic() - row["started"] >= row['timeout']
                if raw_code is None and not timed_out:
                    continue
                if timed_out:
                    print(f"{row['name']}: exceeded {row['timeout']:g}s; stopping owned processes; "
                          "investigate before retrying", flush=True)
                    raw_code = stop_tree(process, row["known"], TERMINATION_GRACE)
                code = 124 if timed_out else raw_code if raw_code >= 0 else 128 - raw_code
                result = {key: row[key] for key in ("name", "command", "log")}
                result.update(exit_code=code, raw_exit_code=raw_code, timed_out=timed_out,
                              wall_timeout_seconds=row['timeout'],
                              termination_grace_seconds=TERMINATION_GRACE,
                              seconds=time.monotonic() - row["started"])
                report["results"].append(result)
                # Persist the returned exit before further cleanup or log reads.
                atomic(directory / "summary.json", report)
                leaked = live_owned(row['known'])
                stop_tree(process, row["known"], TERMINATION_GRACE)
                if leaked or live_owned(row['known']):
                    result['errors'] = ['test exited with live owned descendants']
                    result['exit_code'] = code = code or 1
                del running[process]
                free.append(row["core"])
                if code == 0 and checkpoints is not None:
                    validate(row['name'])
                    checkpoints.save(requests[row['name']], result)
                print(f"[{len(report['results'])}/{len(jobs)}] {row['name']}: "
                      f"{'PASS' if code == 0 else 'FAIL'} ({result['seconds']:.1f}s)", flush=True)
                atomic(directory / "summary.json", report)
                if code:
                    sys.stdout.write(Path(row["log"]).read_text(errors="replace"))
                    report["status"] = "failed"
                    return code if code > 0 else 128 - code
            if running:
                time.sleep(.02)
        names = [result['name'] for result in report['results']]
        if len(names) != len(set(names)) or set(names) != set(report['inventory']):
            raise ValueError("tooling workers did not cover the complete discovered inventory")
        if checkpoints is not None:
            for name in names:
                validate(name)
        report["status"] = "passed"
        print(f"All {len(jobs)} tooling tests passed; peak workers={report['peak_workers']}, "
              f"sampled peak RSS={report['sampled_peak_combined_rss_bytes'] / GIB:.2f} GiB", flush=True)
        return 0
    except KeyboardInterrupt:
        report["status"] = "interrupted"
        raise
    except BaseException:
        report["status"] = "failed"
        raise
    finally:
        for process, row in running.items():
            stop_tree(process, row["known"], TERMINATION_GRACE)
        atomic(directory / "summary.json", report)


def _main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--case", help="run one discovered case in this isolated process")
    parser.add_argument('--resume', action='store_true', help='reuse only validated completed test cases')
    args = parser.parse_args(argv)
    if args.case:
        env = worker_environment(args.case)
        for key in set(os.environ) - set(env):
            os.environ.pop(key, None)
        if args.case.startswith(HORNER_CASE_PREFIX) and not env.get("FC_SUPPLIED_SESSION_PATH"):
            raise ValueError("isolated Horner case requires a prepared production session")
        suite = unittest.defaultTestLoader.loadTestsFromName(args.case)
        if suite.countTestCases() != 1:
            raise ValueError("worker must select exactly one test")
        return 0 if unittest.TextTestRunner(verbosity=2).run(suite).wasSuccessful() else 1
    names = inventory()
    case_timeouts = timeout_overrides(names, os.environ)
    if case_timeouts:
        print('Explicit tooling case deadlines: ' + json.dumps(case_timeouts, sort_keys=True), flush=True)
    workers = int(os.environ.get("CCL_TOOLING_JOBS", "1"))
    memory = int(os.environ.get("CCL_CHECK_MEMORY_BYTES", str(24 * GIB)))
    directory = Path(os.environ["CCL_COMPLETION_REPORT"]) / "tooling-tests"
    atomic(directory / 'setup.json', {'status': 'preparing', 'phase': 'input-binding'})
    summary = directory / 'summary.json'
    if summary.exists():
        preparing = json.loads(summary.read_text())
        preparing['inventory'] = names
        atomic(summary, preparing)
    jobs = [(name, [sys.executable, "-m", "scripts.verification.tooling", "--case", name],
             reservation(name)) for name in names]
    checkpoint_options = {}
    pending = names
    resume = args.resume or os.environ.get('CCL_CHECK_RESUME') == '1'
    if resume:
        store = Checkpoints(ROOT / '.lake/completion-checkpoints/tooling')
        case_environment = worker_environment('')
        inputs = Inputs(ROOT, case_environment, store)
        def request(name, command):
            value = inputs.request(name, command, native=name.startswith('scripts.test.nanoda.'))
            value['wall_timeout_seconds'] = case_timeouts.get(name, TEST_TIMEOUT)
            return value
        print(f'Binding inputs for {len(jobs)} tooling cases', flush=True)
        requests = {}
        next_progress = time.monotonic() + 30
        for index, (name, command, _) in enumerate(jobs, 1):
            requests[name] = request(name, command)
            if time.monotonic() >= next_progress:
                print(f'Bound tooling inputs: {index}/{len(jobs)}', flush=True)
                next_progress = time.monotonic() + 30
        commands = {name: command for name, command, _ in jobs}
        pending = [name for name in names if store.lookup(requests[name]) is None]
        def validate(name):
            if request(name, commands[name]) != requests[name]:
                raise ValueError('tooling inputs changed during checks: ' + name)
        checkpoint_options = dict(checkpoints=store, requests=requests, validate=validate)
        print(f'Tooling resume: {len(names) - len(pending)} validated, {len(pending)} unresolved', flush=True)
    atomic(directory / 'setup.json', {'status': 'preparing', 'phase': 'native-preflight',
                                    'pending_cases': pending})
    preflight_tooling(pending, ROOT, directory, os.environ)
    if any(name.startswith(HORNER_CASE_PREFIX) for name in pending) and not os.environ.get("FC_SUPPLIED_SESSION_PATH"):
        if resume:
            # Preserve independent successes before paying for a live producer.
            # The child still covers the complete inventory and validates these
            # exact requests again before reusing their durable receipts.
            independent = [job for job in jobs if not job[0].startswith(HORNER_CASE_PREFIX)]
            if independent:
                print('Checking independent cases before live producer preparation', flush=True)
                independent_directory = directory / 'independent'
                options = dict(checkpoint_options, requests={
                    name: requests[name] for name, _, _ in independent},
                    case_timeouts={name: case_timeouts[name] for name, _, _ in independent
                                   if name in case_timeouts})
                code = run_jobs(independent, independent_directory, workers, memory, **options)
                atomic(directory / 'summary.json', json.loads(
                    (independent_directory / 'summary.json').read_text()))
                if code:
                    return code
        from scripts.lean_module_data.supplied import supervise_session
        # Source-witness preparation is an aggregate of individually guarded
        # modules. Start each unchanged case watchdog only after readiness.
        directory.mkdir(parents=True, exist_ok=True)
        module = "Purelib.Approximation.Gaussian.Exponential.E"
        print("Preparing live E producer: fresh compilation and input validation", flush=True)
        started = time.monotonic()
        setup = {'status': 'preparing', 'phase': 'producer-preparation',
                 'pending_horner_cases': [n for n in pending if n.startswith(HORNER_CASE_PREFIX)]}
        atomic(directory / 'setup.json', setup)
        def ready():
            setup.update(status='running', phase='test-execution',
                         preparation_seconds=time.monotonic() - started)
            atomic(directory / 'setup.json', setup)
            print(f"Live producer ready after {setup['preparation_seconds']:.1f}s; starting test execution", flush=True)
        try:
            code = supervise_session(module, module + ".horner_sample_eq_factorial",
                                     ROOT / "Purelib/Approximation/Gaussian/Exponential/E.lean",
                                     Path(os.environ["LEAN_SYSROOT"]), ROOT / ".lake/kernel-replay-tests",
                                     directory / "supplied-horner-session.json",
                                     [sys.executable, "-m", "scripts.verification.tooling"] + (['--resume'] if resume else []),
                                     on_ready=ready)
            setup['status'] = 'passed' if code == 0 else 'failed'
            return code
        except KeyboardInterrupt:
            setup['status'] = 'interrupted'
            raise
        except BaseException:
            setup['status'] = 'failed'
            raise
        finally:
            setup['seconds'] = time.monotonic() - started
            atomic(directory / 'setup.json', setup)
    atomic(directory / 'setup.json', {'status': 'running', 'phase': 'test-execution',
                                    'pending_cases': pending})
    print(f"Discovered {len(names)} tests; up to {workers} workers, {memory / GIB:.1f} GiB budget", flush=True)
    return run_jobs(jobs, directory, workers, memory, case_timeouts=case_timeouts,
                    **checkpoint_options)


def main(argv=None) -> int:
    """Retain an interrupted status even before the first worker can start."""
    argv = list(sys.argv[1:] if argv is None else argv)
    if any(arg == '--case' or arg.startswith('--case=') for arg in argv) or any(arg in ('-h', '--help') for arg in argv):
        return _main(argv)
    if 'CCL_COMPLETION_REPORT' not in os.environ:
        os.environ['CCL_COMPLETION_REPORT'] = str(ROOT / '.lake/completion-checks' / f'tooling-{time.time_ns()}')
    directory = Path(os.environ['CCL_COMPLETION_REPORT']) / 'tooling-tests'
    directory.mkdir(parents=True, exist_ok=True)
    summary = directory / 'summary.json'
    atomic(summary, {'status': 'preparing', 'inventory': [], 'results': []})

    def finish(status, error=None):
        report = json.loads(summary.read_text())
        if report['status'] in ('preparing', 'running') or status != 'passed':
            report['status'] = status
            if error is not None:
                report['error'] = str(error)
            atomic(summary, report)
        setup_path = directory / 'setup.json'
        if setup_path.exists():
            setup = json.loads(setup_path.read_text())
            setup['status'] = status
            if error is not None:
                setup['error'] = str(error)
            atomic(setup_path, setup)

    try:
        code = _main(argv)
        if code == 0:
            report = json.loads(summary.read_text())
            expected = inventory()
            observed = [row['name'] for row in report['results']]
            if (report['status'] != 'passed' or report['inventory'] != expected or
                    len(observed) != len(set(observed)) or set(observed) != set(expected)):
                raise ValueError('tooling result does not cover the complete discovered inventory')
        finish('passed' if code == 0 else 'failed')
        return code
    except KeyboardInterrupt:
        finish('interrupted')
        raise
    except BaseException as error:
        finish('failed', error)
        raise


if __name__ == "__main__":
    def interrupt(signum, frame):
        raise KeyboardInterrupt
    signal.signal(signal.SIGTERM, interrupt)
    try:
        raise SystemExit(main())
    except KeyboardInterrupt:
        raise SystemExit(130)
