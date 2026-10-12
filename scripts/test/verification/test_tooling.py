"""Check parallel coverage, resource bounds and cancellation of isolated workers."""

import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import time
import unittest
from unittest.mock import patch

from scripts.paths import ROOT
from scripts.verification import tooling


class ToolingTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="tooling-pool-tests-")
        self.addCleanup(self.temp.cleanup)
        self.directory = Path(self.temp.name)

    def job(self, name, body, cost=1):
        return name, [sys.executable, "-c", body], cost

    def report(self):
        return json.loads((self.directory / "summary.json").read_text())

    def test_workers_overlap_and_preserve_complete_logs_and_coverage(self):
        # Two cooperating processes prove overlap even on a single-core host.
        jobs = []
        for name, other in (("left", "right"), ("right", "left")):
            body = f"""import time
from pathlib import Path
p = Path({str(self.directory)!r})
(p / {name!r}).touch()
deadline = time.monotonic() + 5
while not (p / {other!r}).exists() and time.monotonic() < deadline: time.sleep(.01)
assert (p / {other!r}).exists(), 'workers did not overlap'
print({name!r})
"""
            jobs.append(self.job(name, body))
        affinity = list(os.sched_getaffinity(0))
        with patch.object(tooling.os, "sched_getaffinity", return_value=[affinity[0], affinity[0]]):
            self.assertEqual(tooling.run_jobs(jobs, self.directory, 2, 2), 0)
        report = self.report()
        self.assertEqual(report["peak_workers"], 2)
        self.assertEqual({r["name"] for r in report["results"]}, {"left", "right"})
        for row in report["results"]:
            self.assertEqual(Path(row["log"]).read_text().strip(), row["name"])

    def test_memory_reservations_serialize_heavy_jobs(self):
        jobs = [self.job(str(i), "import time; time.sleep(.05)", 2) for i in range(3)]
        self.assertEqual(tooling.run_jobs(jobs, self.directory, 3, 2), 0)
        self.assertEqual(self.report()["peak_workers"], 1)

    def test_worker_affinity_is_inherited_by_grandchildren(self):
        job = self.job("affinity", "import os,subprocess,sys; "
                       "assert len(os.sched_getaffinity(0)) == 1; "
                       "subprocess.run([sys.executable,'-c',"
                       "'import os; assert len(os.sched_getaffinity(0)) == 1'],check=True)")
        self.assertEqual(tooling.run_jobs([job], self.directory, 1, 1), 0)

    def test_failure_cancels_owned_descendants_in_separate_sessions(self):
        ready = self.directory / "ready"
        sleeper = "import os,time; from pathlib import Path; " + f"Path({str(ready)!r}).write_text(str(os.getpid())); time.sleep(60)"
        helper = self.job("helper", f"import subprocess,sys,time; "
                          f"subprocess.Popen([sys.executable,'-c',{sleeper!r}],start_new_session=True); time.sleep(60)")
        failure = self.job("failure", f"import time; from pathlib import Path; p=Path({str(ready)!r}); "
                           "\ndeadline=time.monotonic()+5\n"
                           "while not p.exists() and time.monotonic()<deadline: time.sleep(.01)\n"
                           "time.sleep(.3)\nraise SystemExit(9)")
        affinity = list(os.sched_getaffinity(0))
        with patch.object(tooling.os, "sched_getaffinity", return_value=[affinity[0], affinity[0]]):
            self.assertEqual(tooling.run_jobs([helper, failure], self.directory, 2, 2), 9)
        self.assertEqual(self.report()["status"], "failed")
        self.assertIsNone(tooling.process_record(int(ready.read_text()), live=True))

    def test_interruption_retains_summary_and_reaps_workers(self):
        ready = self.directory / "ready"
        job = self.job("slow", f"import os,time; from pathlib import Path; "
                       f"Path({str(ready)!r}).write_text(str(os.getpid())); time.sleep(60)")
        harness = f"""import signal
from pathlib import Path
from scripts.verification.tooling import run_jobs
def interrupt(signum, frame): raise KeyboardInterrupt
signal.signal(signal.SIGTERM, interrupt)
try: run_jobs([{job!r}], Path({str(self.directory)!r}), 1, 1)
except KeyboardInterrupt: raise SystemExit(130)
"""
        process = subprocess.Popen([sys.executable, "-c", harness], cwd=ROOT,
                                   stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        try:
            deadline = time.monotonic() + 10
            while not ready.exists() and time.monotonic() < deadline:
                time.sleep(.02)
            self.assertTrue(ready.exists())
            process.send_signal(signal.SIGTERM)
            self.assertEqual(process.wait(timeout=10), 130)
        finally:
            if process.poll() is None:
                process.kill()
                process.wait()
        self.assertEqual(self.report()["status"], "interrupted")
        self.assertIsNone(tooling.process_record(int(ready.read_text()), live=True))


if __name__ == "__main__":
    unittest.main()
