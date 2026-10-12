"""Distribute every discovered tooling regression over isolated worker processes."""

from __future__ import annotations

import argparse
import os
from pathlib import Path
import signal
import subprocess
import sys
import time
import unittest

from scripts.paths import ROOT
from scripts.profiling.build_costs import atomic
from scripts.nanoda.benchmark_pipeline import descendants, process_table
from scripts.nanoda.processes import process_record

GIB = 1024**3
# These modules have been checked to use temporary fixtures and small imports.
# New modules receive the conservative whole-host-audit reservation until reviewed.
LIGHT_MODULES = {
    "axioms.test_orchestration", "axioms.test_propext_frontier", "axioms.test_trace",
    "generators.test_sewing", "lean_module_data.test_reader",
    "linting.test_runner", "module_style.test_contracts", "module_style.test_core",
    "module_style.test_public_imports", "profiling.test_build_costs",
    "nanoda.test_benchmark_pipeline", "nanoda.test_check_stream", "nanoda.test_compare_exports",
    "nanoda.test_export_validation", "nanoda.test_planning", "nanoda.test_policy",
    "nanoda.test_root_inventory", "nanoda.test_scheduling",
    "verification.test_authored_names", "verification.test_completion",
    "verification.test_declarations", "verification.test_imports",
    "verification.test_reader_provenance", "verification.test_source_policy",
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


def observe(process, known, table):
    """Follow ancestry only while the original leader identity still matches."""
    leader = table.get(process.pid)
    parent = process.pid if leader and leader["started"] == known.get(process.pid) else -1
    return descendants(table, parent, known)


def stop_tree(process, known) -> None:
    """Stop owned descendants, including helpers that created their own sessions."""
    def live():
        table = process_table()
        observe(process, known, table)
        return [pid for pid, started in known.items()
                if (record := process_record(pid, live=True)) is not None and record[0] == started]
    for pid in live():
        try:
            os.kill(pid, signal.SIGTERM)
        except ProcessLookupError:
            pass
    deadline = time.monotonic() + 5
    while live() and time.monotonic() < deadline:
        process.poll()
        time.sleep(.02)
    for pid in live():
        try:
            os.kill(pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
    process.wait()


def run_jobs(jobs: list[tuple[str, list[str], int]], directory: Path,
             workers: int, memory: int) -> int:
    """Keep cores busy within the memory budget; retain exact test coverage and logs."""
    if not jobs or len({name for name, _, _ in jobs}) != len(jobs) or min(workers, memory) < 1:
        raise ValueError("nonempty unique jobs and positive resource budgets are required")
    directory.mkdir(parents=True, exist_ok=True)
    affinity = sorted(os.sched_getaffinity(0)) if hasattr(os, "sched_getaffinity") else None
    workers = min(workers, len(affinity)) if affinity else workers
    free = list(range(workers))
    pending = sorted(enumerate(jobs), key=lambda item: -item[1][2])
    running = {}
    report = {"status": "running", "inventory": [job[0] for job in jobs], "results": [],
              "workers": workers, "memory_budget_bytes": memory, "peak_workers": 0,
              "sampled_peak_combined_rss_bytes": 0}
    try:
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
                                               stderr=subprocess.STDOUT, start_new_session=True)
                identity = process_record(process.pid)
                running[process] = {"name": name, "command": command, "memory": cost,
                                    "core": core, "log": str(log_path), "started": time.monotonic(),
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
                code = process.poll()
                if code is None:
                    continue
                stop_tree(process, row["known"])
                result = {key: row[key] for key in ("name", "command", "log")}
                result.update(exit_code=code, seconds=time.monotonic() - row["started"])
                report["results"].append(result)
                del running[process]
                free.append(row["core"])
                print(f"[{len(report['results'])}/{len(jobs)}] {row['name']}: "
                      f"{'PASS' if code == 0 else 'FAIL'} ({result['seconds']:.1f}s)", flush=True)
                atomic(directory / "summary.json", report)
                if code:
                    sys.stdout.write(Path(row["log"]).read_text(errors="replace"))
                    report["status"] = "failed"
                    return code if code > 0 else 128 - code
            if running:
                time.sleep(.02)
        if {result["name"] for result in report["results"]} != set(report["inventory"]):
            raise ValueError("tooling workers did not cover the complete discovered inventory")
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
            stop_tree(process, row["known"])
        atomic(directory / "summary.json", report)


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--case", help="run one discovered case in this isolated process")
    args = parser.parse_args(argv)
    if args.case:
        suite = unittest.defaultTestLoader.loadTestsFromName(args.case)
        if suite.countTestCases() != 1:
            raise ValueError("worker must select exactly one test")
        return 0 if unittest.TextTestRunner(verbosity=2).run(suite).wasSuccessful() else 1
    names = inventory()
    workers = int(os.environ.get("CCL_TOOLING_JOBS", "1"))
    memory = int(os.environ.get("CCL_CHECK_MEMORY_BYTES", str(24 * GIB)))
    directory = Path(os.environ["CCL_COMPLETION_REPORT"]) / "tooling-tests"
    jobs = [(name, [sys.executable, "-m", "scripts.verification.tooling", "--case", name],
             reservation(name)) for name in names]
    print(f"Discovered {len(names)} tests; up to {workers} workers, {memory / GIB:.1f} GiB budget", flush=True)
    return run_jobs(jobs, directory, workers, memory)


if __name__ == "__main__":
    def interrupt(signum, frame):
        raise KeyboardInterrupt
    signal.signal(signal.SIGTERM, interrupt)
    try:
        raise SystemExit(main())
    except KeyboardInterrupt:
        raise SystemExit(130)
