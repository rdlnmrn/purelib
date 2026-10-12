"""Exercise completion failure, interruption recovery and final-tree validation."""

import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import time
import unittest

from scripts.paths import ROOT
from scripts.verification import completion


class CompletionTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="completion-test-")
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        subprocess.run(["git", "init", "-q", str(self.root)], check=True)
        (self.root / "source").write_text("original source")
        subprocess.run(["git", "add", "source"], cwd=self.root, check=True)
        self.directory = self.root / ".git/report"
        self.directory.mkdir()

    def command(self, text):
        return [sys.executable, "-c", text]

    def report(self):
        return json.loads((self.directory / "summary.json").read_text())

    def test_failure_preserves_output_and_stops_before_later_gate(self):
        plan = [("failure", self.command("print('useful diagnostic', flush=True); raise SystemExit(7)")),
                ("later", self.command("from pathlib import Path; Path('.git/later').touch()"))]
        self.assertEqual(completion.execute(plan, self.directory, dict(os.environ), self.root), 7)
        self.assertFalse((self.root / ".git/later").exists())
        self.assertEqual((self.directory / "failure.log").read_text(), "useful diagnostic\n")
        self.assertEqual(self.report()["status"], "failed")
        self.assertEqual(len(self.report()["stages"]), 1)

    def test_success_reruns_commands_instead_of_trusting_summary(self):
        plan = [("gate", self.command("from pathlib import Path; p = Path('.git/count'); "
                                     "p.write_text(str(int(p.read_text()) + 1 if p.exists() else 1))"))]
        for _ in range(2):
            self.assertEqual(completion.execute(plan, self.directory, dict(os.environ), self.root), 0)
            self.assertEqual(self.report()["status"], "passed")
        self.assertEqual((self.root / ".git/count").read_text(), "2")

    def test_changed_dirty_or_new_source_invalidates_success(self):
        for operation in ["Path('source').write_text('changed')", "Path('new-source').touch()"]:
            with self.subTest(operation=operation):
                (self.root / "source").write_text("dirty but initially stable")
                (self.root / "new-source").unlink(missing_ok=True)
                plan = [("edit", self.command("from pathlib import Path; " + operation))]
                with self.assertRaisesRegex(ValueError, "files changed"):
                    completion.execute(plan, self.directory, dict(os.environ), self.root)
                self.assertEqual(self.report()["status"], "failed")

    def test_full_scope_and_assertion_checks_cannot_be_silently_disabled(self):
        with self.assertRaisesRegex(ValueError, "full inventory"):
            completion.environment({"NANODA_MODULE_MANIFEST": "small.modules"}, 8, None)
        env = completion.environment({"PYTHONOPTIMIZE": "1"}, 8, None)
        self.assertNotIn("PYTHONOPTIMIZE", env)
        self.assertEqual(env["LEAN_NUM_THREADS"], "1")

    def test_worker_budget_and_explicit_overrides(self):
        env = completion.environment({}, 192, 1024 * completion.GIB)
        self.assertLessEqual(int(env["AXIOM_AUDIT_JOBS"]) * 12 * completion.GIB, 250 * completion.GIB * 3 // 4)
        self.assertLessEqual(int(env["CCL_LINT_JOBS"]) * 2 * completion.GIB, 250 * completion.GIB * 3 // 4)
        small = completion.environment({}, 8, 4 * completion.GIB)
        self.assertEqual((small["AXIOM_AUDIT_JOBS"], small["CCL_LINT_JOBS"]), ("1", "1"))
        overrides = {"AXIOM_AUDIT_JOBS": "3", "CCL_LINT_JOBS": "4", "LEAN_NUM_THREADS": "8"}
        env = completion.environment(overrides, 8, 128 * completion.GIB)
        self.assertEqual({key: env[key] for key in overrides}, overrides)

    def test_core_cap_covers_all_pools_and_nanoda_overlap(self):
        for cores in (1, 2, 4, 8, 32, 192):
            env = completion.environment({}, cores, 1024 * completion.GIB)
            for key in ("AXIOM_AUDIT_JOBS", "CCL_LINT_JOBS", "CCL_TOOLING_JOBS", "LEAN_NUM_THREADS"):
                self.assertLessEqual(int(env[key]), cores)
            exports = int(env["NANODA_EXPORT_JOBS"])
            checks = int(env["NANODA_POST_EXPORT_CHECKS"])
            threads = int(env["NANODA_JOBS"])
            self.assertGreaterEqual(threads, 2)
            if env.get("NANODA_PIPELINE") != "0":
                self.assertLessEqual(exports + checks * threads, cores)
                self.assertLessEqual((exports + checks) * 16 * completion.GIB,
                                     int(env["CCL_CHECK_MEMORY_BYTES"]))
        env = completion.environment({"CCL_LINT_JOBS": "99", "LEAN_NUM_THREADS": "99",
                                      "AXIOM_AUDIT_JOBS": "99"}, 2, 128 * completion.GIB)
        self.assertEqual((env["CCL_LINT_JOBS"], env["LEAN_NUM_THREADS"], env["AXIOM_AUDIT_JOBS"]),
                         ("2", "2", "2"))

    def test_interrupt_stops_owned_child_and_retains_recoverable_summary(self):
        ready = self.root / ".git/ready"
        child = self.command("import os, time; from pathlib import Path; "
                             "Path('.git/ready').write_text(str(os.getpid())); time.sleep(30)")
        harness = "\n".join([
            "import signal", "from pathlib import Path",
            "from scripts.verification.completion import execute",
            "def interrupt(signum, frame): raise KeyboardInterrupt",
            "signal.signal(signal.SIGTERM, interrupt)",
            f"raise SystemExit(execute([('slow', {child!r})], Path({str(self.directory)!r}), "
            f"dict(__import__('os').environ), Path({str(self.root)!r})))",
        ])
        with (self.root / ".git/harness.log").open("w") as log:
            process = subprocess.Popen(self.command(harness), cwd=ROOT, stdout=log, stderr=log)
            try:
                deadline = time.monotonic() + 10
                while not ready.exists() and time.monotonic() < deadline and process.poll() is None:
                    time.sleep(0.02)
                self.assertTrue(ready.exists(), "child did not start")
                child_pid = int(ready.read_text())
                process.send_signal(signal.SIGTERM)
                self.assertEqual(process.wait(timeout=10), 130)
                with self.assertRaises(ProcessLookupError):
                    os.kill(child_pid, 0)
            finally:
                if process.poll() is None:
                    process.kill()
                    process.wait()
        self.assertEqual(self.report()["status"], "interrupted")
        self.assertEqual(completion.execute([("recovered", self.command("pass"))], self.directory,
                                            dict(os.environ), self.root), 0)


if __name__ == "__main__":
    unittest.main()
