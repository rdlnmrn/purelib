"""Bound an individual module worker without limiting its aggregate caller."""

import json
import math
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import time

from scripts.verification.processes import live_owned, observe, process_record, process_table, stop_tree

MODULE_TIMEOUT = 120.0
TERMINATION_GRACE = 15.0
MODULE_TARGET = 30.0


def selected_timeout(environment=None):
    """Select an explicitly authorized build deadline, retaining the normal default.

    Release exceptions cannot exceed the existing five-minute emergency bound.
    This changes wall-clock supervision, not Lean's mathematical resource limits.
    """
    environment = os.environ if environment is None else environment
    value = environment.get('CCL_MODULE_TIMEOUT_SECONDS', str(MODULE_TIMEOUT))
    try:
        seconds = float(value)
    except (TypeError, ValueError) as error:
        raise ValueError('CCL_MODULE_TIMEOUT_SECONDS must be a finite number in (0, 300]') from error
    if not math.isfinite(seconds) or not 0 < seconds <= 300:
        raise ValueError('CCL_MODULE_TIMEOUT_SECONDS must be a finite number in (0, 300]')
    return seconds


def run(command, module, reports, *, timeout=MODULE_TIMEOUT, grace=TERMINATION_GRACE,
        cwd=None, env=None, stdout=None, receipt_path=None, performance_target=MODULE_TARGET):
    """Record the raw exit and terminate all retained descendants on an overrun."""
    reports = Path(reports)
    reports.mkdir(parents=True, exist_ok=True)
    started = time.monotonic()
    process = subprocess.Popen(command, start_new_session=True, cwd=cwd, env=env,
                               stdout=stdout, stderr=subprocess.STDOUT if stdout is not None else None)
    record = process_record(process.pid)
    known = {process.pid: record[0]} if record else {}
    code = None
    timed_out = False
    errors = []
    interrupted = False
    previous = {}

    def interrupt(*_):
        raise KeyboardInterrupt

    for signum in (signal.SIGTERM, signal.SIGINT):
        previous[signum] = signal.signal(signum, interrupt)
    try:
        while True:
            observe(process, known, process_table())
            code = process.poll()
            if code is not None:
                break
            if time.monotonic() - started >= timeout:
                timed_out = True
                print(f"module {module}: exceeded {timeout:g}s; terminating", file=sys.stderr, flush=True)
                code = stop_tree(process, known, grace)
                break
            try:
                code = process.wait(timeout=min(.25, max(.001, timeout - (time.monotonic() - started))))
                break
            except subprocess.TimeoutExpired:
                pass
    except BaseException:
        interrupted = True
        code = stop_tree(process, known, grace)
        raise
    finally:
        # Save the returned exit before further cleanup or receipt processing.
        raw_code = code
        try:
            observe(process, known, process_table())
            if live_owned(known):
                errors.append("module exited with live descendants")
                stop_tree(process, known, grace)
            if live_owned(known):
                errors.append("module descendants survived termination")
            elapsed = time.monotonic() - started
            report = {"module": module, "command": command, "raw_exit_code": raw_code,
                      "timed_out": timed_out, "interrupted": interrupted, "errors": errors,
                      "seconds": elapsed, "wall_timeout_seconds": timeout,
                      "termination_grace_seconds": grace}
            with tempfile.NamedTemporaryFile(mode="w", dir=reports, suffix=".json", delete=False) as receipt:
                json.dump(report, receipt, sort_keys=True)
                receipt.write("\n")
            if receipt_path is not None:
                os.replace(receipt.name, receipt_path)
            if performance_target is not None and elapsed >= performance_target:
                print(f"module {module}: {elapsed:.3f}s (target <{performance_target:g}s); profile before integration into master", file=sys.stderr)
        finally:
            for signum, handler in previous.items():
                signal.signal(signum, handler)
    return 124 if timed_out else 1 if errors else (code if code >= 0 else 128 - code)


def lean(compiler, args, reports):
    """Guard source compilation; metadata queries, servers and executed programs keep their callers."""
    sources = [arg for arg in args if arg.endswith(".lean") and not arg.startswith("-")]
    if not sources or any(arg in ("--run", "--server", "--worker") for arg in args):
        os.execv(compiler, [compiler, *args])
    return run([compiler, *args], ",".join(sources), reports, timeout=selected_timeout())
