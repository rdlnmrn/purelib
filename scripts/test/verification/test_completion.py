"""Exercise completion failure, interruption recovery and final-tree validation."""

import contextlib
import ctypes
import io
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import threading
import time
import unittest
from unittest import mock

from scripts.paths import ROOT
from scripts.verification import completion


class CompletionTests(unittest.TestCase):
    def setUp(self):
        # These process-control fixtures own temporary repositories and their
        # fake artifacts; a surrounding Lake invocation must not make them
        # inventory the real toolchain before starting their observed children.
        excluded = {'LEAN_SYSROOT', 'LEAN_PATH', 'CCL_CORE_PREFIX', 'CCL_TEST_CORE_PREFIX', 'NANODA_BIN'}
        environment = {key: value for key, value in os.environ.items() if key not in excluded}
        patcher = mock.patch.dict(os.environ, environment, clear=True)
        patcher.start()
        self.addCleanup(patcher.stop)
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

    def test_list_includes_release_prerequisites_without_running_checks(self):
        output = io.StringIO()
        with contextlib.redirect_stdout(output), mock.patch.object(completion, 'run_preflight') as preflight:
            self.assertEqual(completion.main(['--list', '--resume', '--release', '2.0.0']), 0)
        preflight.assert_not_called()
        lines = output.getvalue().splitlines()
        self.assertEqual(lines[0], 'publication-preflight: scripts/maintenance/public-history.sh preflight 2.0.0')
        self.assertTrue(lines[1].startswith('socket-preflight:'))
        self.assertTrue(lines[2].startswith('nanoda-preflight:'))
        self.assertEqual([line.split(':', 1)[0] for line in lines[3:]],
                         [name for name, _ in completion.stages()])

    def test_memory_pools_respect_parent_cgroup_headroom_and_throttling_limit(self):
        base = self.root / '.git/cgroup'
        worker = base / 'parent/worker'
        worker.mkdir(parents=True)
        membership = self.root / '.git/membership'
        membership.write_text('0::/parent/worker\n')
        gib = completion.GIB
        for directory, high, maximum, current in (
                (base, 'max', 'max', 0),
                (worker.parent, str(7*gib), str(8*gib), gib),
                (worker, 'max', 'max', 0)):
            for name, value in [('memory.high', high), ('memory.max', maximum), ('memory.current', current)]:
                (directory / name).write_text(str(value))
        available = completion.cgroup_memory_available(base, membership)
        self.assertEqual(available, 6*gib)
        env = completion.environment({}, 5, available)
        self.assertEqual(env['AXIOM_AUDIT_JOBS'], '1')
        self.assertEqual(env['NANODA_PIPELINE'], '0')
        self.assertEqual(int(env['CCL_CHECK_MEMORY_BYTES']), available*3//4)
        (worker / 'memory.max').write_text(str(3*gib))
        (worker / 'memory.current').write_text(str(gib))
        self.assertEqual(completion.cgroup_memory_available(base, membership), 2*gib)

    def test_exhausted_memory_does_not_fall_back_to_a_large_default_budget(self):
        for available in (0, 1):
            with self.subTest(available=available), self.assertRaisesRegex(ValueError, 'no available memory'):
                completion.environment({}, 5, available)

    def test_failure_preserves_output_and_stops_before_later_gate(self):
        plan = [("failure", self.command("print('useful diagnostic', flush=True); raise SystemExit(7)")),
                ("later", self.command("from pathlib import Path; Path('.git/later').touch()"))]
        self.assertEqual(completion.execute(plan, self.directory, dict(os.environ), self.root), 7)
        self.assertFalse((self.root / ".git/later").exists())
        self.assertEqual((self.directory / "failure.log").read_text(), "useful diagnostic\n")
        self.assertEqual(self.report()["status"], "failed")
        self.assertEqual(len(self.report()["stages"]), 1)

    def test_quiet_partial_and_closed_output_receive_live_progress(self):
        cases = [
            ("import time; time.sleep(.15)", "", 0),
            ("import sys, time; sys.stdout.write('partial'); sys.stdout.flush(); "
             "time.sleep(.15); print(' done'); raise SystemExit(7)", "partial done\n", 7),
            ("import os, time; os.close(1); os.close(2); time.sleep(.15)", "", 0),
        ]
        for command, expected, code in cases:
            with self.subTest(command=command):
                terminal = io.TextIOWrapper(io.BytesIO(), encoding="utf-8")
                with contextlib.redirect_stdout(terminal), mock.patch.object(
                        completion, "PROGRESS_INTERVAL", .03):
                    result = completion.run_stage(
                        "quiet", self.command(command), self.directory, dict(os.environ), self.root)
                terminal.flush()
                output = terminal.buffer.getvalue().decode()
                self.assertEqual(result["exit_code"], code)
                self.assertIn("[quiet] still running (", output)
                self.assertIn("since last output)", output)
                ending = "[quiet] " + ("passed" if code == 0 else "FAILED")
                self.assertLess(output.index("still running"), output.index(ending))
                self.assertEqual((self.directory / "quiet.log").read_text(), expected)
                terminal.close()

    def test_success_reruns_commands_instead_of_trusting_summary(self):
        plan = [("gate", self.command("from pathlib import Path; p = Path('.git/count'); "
                                     "p.write_text(str(int(p.read_text()) + 1 if p.exists() else 1))"))]
        for _ in range(2):
            self.assertEqual(completion.execute(plan, self.directory, dict(os.environ), self.root), 0)
            self.assertEqual(self.report()["status"], "passed")
        self.assertEqual((self.root / ".git/count").read_text(), "2")

    def test_resume_reuses_completed_stages_and_checks_new_stages(self):
        (self.root / '.git/info/exclude').write_text('.lake/\n')
        first = ('first', self.command("from pathlib import Path; p=Path('.git/count'); "
                                       "p.write_text(str(int(p.read_text())+1 if p.exists() else 1))"))
        failure = ('retry', self.command("from pathlib import Path; "
                                        "raise SystemExit(0 if Path('.git/repaired').exists() else 7)"))
        self.assertEqual(completion.execute([first, failure], self.directory, dict(os.environ),
                                            self.root, resume=True), 7)
        (self.root / '.git/repaired').touch()
        added = ('added', self.command("from pathlib import Path; Path('.git/added').touch()"))
        self.assertEqual(completion.execute([first, failure, added], self.directory,
                                            dict(os.environ), self.root, resume=True), 0)
        self.assertEqual((self.root / '.git/count').read_text(), '1')
        self.assertTrue(self.report()['stages'][0]['reused'])
        self.assertEqual([row['name'] for row in self.report()['stages']], ['first', 'retry', 'added'])
        self.assertTrue((self.root / '.git/added').exists())

    def test_resume_survives_new_launcher_metadata_without_exposing_it_to_checks(self):
        (self.root / '.git/info/exclude').write_text('.lake/\n')
        plan = [('gate', self.command(
            "import os; from pathlib import Path; "
            "assert 'INVOCATION_ID' not in os.environ; "
            "assert 'SYSTEMD_EXEC_PID' not in os.environ; "
            "assert os.environ['CHECKER_FIXTURE_CONFIG']=='kept'; "
            "p=Path('.git/count'); p.write_text(str(int(p.read_text())+1 if p.exists() else 1))"))]
        for invocation in ('first', 'second'):
            env = dict(os.environ, INVOCATION_ID=invocation, SYSTEMD_EXEC_PID=invocation,
                       MEMORY_PRESSURE_WATCH='/unit/' + invocation,
                       CHECKER_FIXTURE_CONFIG='kept')
            self.assertEqual(completion.execute(plan, self.directory, env, self.root, resume=True), 0)
        self.assertEqual((self.root / '.git/count').read_text(), '1')
        self.assertTrue(self.report()['stages'][0]['reused'])

    def test_resume_invalidates_private_artifact_changes_and_damaged_output(self):
        (self.root / '.git/info/exclude').write_text('.lake/\n')
        library = self.root / '.lake/build/lib/lean'
        library.mkdir(parents=True)
        private = library / 'Fixture.olean.private'
        private.write_text('protocol fixture, not a Lean artifact')
        plan = [('gate', self.command("from pathlib import Path; p=Path('.git/count'); "
                                      "p.write_text(str(int(p.read_text())+1 if p.exists() else 1))"))]
        for expected in (1, 2, 3):
            self.assertEqual(completion.execute(plan, self.directory, dict(os.environ),
                                                self.root, resume=True), 0)
            self.assertEqual((self.root / '.git/count').read_text(), str(expected))
            if expected == 1:
                private.write_text('changed private proof input')
            elif expected == 2:
                from scripts.verification.checkpoints import Checkpoints, Inputs
                env = completion.execution_environment(dict(
                    os.environ, CCL_COMPLETION_REPORT=str(self.directory), CCL_CHECK_RESUME='1'))
                store = Checkpoints(self.root / '.lake/completion-checkpoints/stages')
                request = Inputs(self.root, env, store).request(*plan[0])
                saved = store.lookup(request)
                Path(saved['log']).write_text('damaged retained output')

    def test_resume_preserves_completed_stage_after_actual_sigterm(self):
        (self.root / '.git/info/exclude').write_text('.lake/\n')
        first = ('first', self.command("from pathlib import Path; p=Path('.git/count'); "
                                       "p.write_text(str(int(p.read_text())+1 if p.exists() else 1))"))
        pending = ('pending', self.command("import time; from pathlib import Path; "
                                           "Path('.git/ready').touch(); time.sleep(30)"))
        script = ("import json,os,signal,sys; from pathlib import Path; "
                  "from scripts.verification.completion import execute\n"
                  "def stop(*_): raise KeyboardInterrupt\n"
                  "signal.signal(signal.SIGTERM,stop)\n"
                  "plan,report,root=json.loads(sys.argv[1]); "
                  "sys.exit(execute(plan,Path(report),dict(os.environ),Path(root),resume=True))")
        process = subprocess.Popen([sys.executable, '-c', script,
                                    json.dumps(([first, pending], str(self.directory), str(self.root)))],
                                   cwd=ROOT, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        try:
            deadline = time.monotonic() + 10
            while not (self.root / '.git/ready').exists() and process.poll() is None and time.monotonic() < deadline:
                time.sleep(.02)
            self.assertTrue((self.root / '.git/ready').exists())
            process.send_signal(signal.SIGTERM)
            self.assertEqual(process.wait(timeout=10), 130)
        finally:
            if process.poll() is None:
                process.kill()
                process.wait()
        self.assertEqual(self.report()['status'], 'interrupted')
        self.assertEqual(completion.execute([first, ('pending', self.command('pass'))],
                                            self.directory, dict(os.environ), self.root, resume=True), 0)
        self.assertEqual((self.root / '.git/count').read_text(), '1')
        self.assertTrue(self.report()['stages'][0]['reused'])

    def test_timeout_rejects_zero_exit_and_closed_output(self):
        for close_output in (False, True):
            with self.subTest(close_output=close_output):
                command = ("import os, signal, sys, time; "
                           "signal.signal(signal.SIGTERM, lambda *_: sys.exit(0)); "
                           + ("os.close(1); os.close(2); " if close_output else "print('started', flush=True); ")
                           + "time.sleep(30)")
                plan = [("slow", self.command(command)),
                        ("later", self.command("from pathlib import Path; Path('.git/later').touch()"))]
                with mock.patch.multiple(completion, STAGE_TIMEOUT=.5, TERMINATION_GRACE=.1,
                                         PROCESS_SAMPLE_INTERVAL=.01):
                    self.assertEqual(completion.execute(plan, self.directory, dict(os.environ), self.root), 124)
                result = self.report()["stages"][0]
                self.assertTrue(result["timed_out"])
                self.assertEqual(result["raw_exit_code"], 0)
                self.assertEqual(json.loads((self.directory / "slow-exit.json").read_text()),
                                 {"raw_exit_code": 0})
                self.assertFalse((self.root / ".git/later").exists())

    def test_timeout_kills_detached_term_resistant_descendants(self):
        child = ("import os, signal, time; from pathlib import Path; "
                 "signal.signal(signal.SIGTERM, signal.SIG_IGN); "
                 "Path('.git/ready').write_text(str(os.getpid())); time.sleep(30)")
        parent = ("import signal, subprocess, sys, time; "
                  "signal.signal(signal.SIGTERM, signal.SIG_IGN); "
                  f"subprocess.Popen([sys.executable, '-c', {child!r}], start_new_session=True); "
                  "time.sleep(30)")
        with mock.patch.multiple(completion, STAGE_TIMEOUT=.8, TERMINATION_GRACE=.05,
                                 PROCESS_SAMPLE_INTERVAL=.01):
            self.assertEqual(completion.execute([("slow", self.command(parent))], self.directory,
                                                dict(os.environ), self.root), 124)
        child_pid = int((self.root / ".git/ready").read_text())
        self.assertIsNone(completion.process_record(child_pid, live=True))
        self.assertEqual(self.report()["stages"][0]["raw_exit_code"], -signal.SIGKILL)

    def test_aggregate_gates_may_outlast_module_deadline(self):
        with mock.patch.multiple(completion, STAGE_TIMEOUT=.05, TERMINATION_GRACE=.05,
                                 PROCESS_SAMPLE_INTERVAL=.005):
            for name in ("build", "tooling-tests", "lint", "axioms", "nanoda"):
                with self.subTest(name=name):
                    result = completion.run_stage(name, self.command("import time; time.sleep(.15)"),
                                                  self.directory, dict(os.environ), self.root)
                    self.assertEqual(result["exit_code"], 0)
                    self.assertFalse(result["timed_out"])
                    self.assertIsNone(result["wall_timeout_seconds"])

    def test_successful_leader_with_detached_worker_is_rejected(self):
        child = ("import os, time; from pathlib import Path; "
                 "Path('.git/ready').write_text(str(os.getpid())); time.sleep(30)")
        for streams in ("", ", stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL"):
            with self.subTest(streams=streams):
                (self.root / ".git/ready").unlink(missing_ok=True)
                parent = ("import subprocess, sys, time; from pathlib import Path; "
                          f"subprocess.Popen([sys.executable, '-c', {child!r}], start_new_session=True{streams})\n"
                          "while not Path('.git/ready').exists(): time.sleep(.01)\n"
                          "time.sleep(.1)")
                with mock.patch.multiple(completion, TERMINATION_GRACE=.05, PROCESS_SAMPLE_INTERVAL=.01):
                    self.assertEqual(completion.execute([("orphan", self.command(parent))], self.directory,
                                                        dict(os.environ), self.root), 1)
                result = self.report()["stages"][0]
                self.assertEqual(result["raw_exit_code"], 0)
                self.assertFalse(result["timed_out"])
                self.assertTrue(result["errors"])
                self.assertIsNone(completion.process_record(int((self.root / ".git/ready").read_text()), live=True))

    def test_detached_worker_reparented_before_first_sample_is_rejected(self):
        ready = self.root / ".git/ready-pipe"
        release = self.root / ".git/release-pipe"
        os.mkfifo(ready)
        os.mkfifo(release)
        child = "import time; time.sleep(30)"
        parent = ("import json, os, subprocess, sys; from pathlib import Path; "
                  f"p = subprocess.Popen([sys.executable, '-c', {child!r}], "
                  "start_new_session=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL); "
                  f"Path({str(ready)!r}).write_text(json.dumps([os.getpid(), p.pid])); "
                  f"Path({str(release)!r}).read_text()")
        table = completion.process_table
        owned = {}

        def sample_after_exit():
            if not owned:
                leader, worker = json.loads(ready.read_text())
                owned[worker] = completion.process_record(worker)
                release.write_text("exit")
                # Leave the actual leader unreaped, but establish that its
                # child has already lost the original ancestry before sampling.
                os.waitid(os.P_PID, leader, os.WEXITED | os.WNOWAIT)
            return table()

        try:
            with mock.patch.object(completion, "process_table", side_effect=sample_after_exit), \
                    mock.patch.object(completion, "TERMINATION_GRACE", .05):
                self.assertEqual(completion.execute([("orphan", self.command(parent))], self.directory,
                                                    dict(os.environ), self.root), 1)
            result = self.report()["stages"][0]
            self.assertEqual(result["raw_exit_code"], 0)
            self.assertTrue(result["errors"])
            for worker in owned:
                self.assertIsNone(completion.process_record(worker, live=True))
                with self.assertRaises(ChildProcessError):
                    os.waitpid(worker, os.WNOHANG)
        finally:
            for worker, identity in owned.items():
                if completion.process_record(worker, live=True) == identity:
                    os.kill(worker, signal.SIGKILL)
                try:
                    os.waitpid(worker, 0)
                except ChildProcessError:
                    pass

    def test_preexisting_child_is_never_claimed_by_a_stage(self):
        process = subprocess.Popen(self.command("import time; time.sleep(30)"))
        identity = completion.process_record(process.pid)
        try:
            with self.assertRaisesRegex(RuntimeError, "dedicated process"):
                completion.run_stage("unlaunched", self.command("raise SystemExit(7)"),
                                     self.directory, dict(os.environ), self.root)
            self.assertEqual(completion.process_record(process.pid, live=True), identity)
            self.assertIsNone(process.poll())
            self.assertFalse((self.directory / "unlaunched.log").exists())
        finally:
            process.kill()
            process.wait()

    def unobserved_detached_worker(self):
        """Synchronize actual adoption independently of process-table sampling."""
        fixture = Path(tempfile.mkdtemp(prefix="adoption-", dir=self.root / ".git"))
        ready = fixture / "ready-pipe"
        release = fixture / "release-pipe"
        os.mkfifo(ready)
        os.mkfifo(release)
        child = ("import json, os, signal, time; from pathlib import Path; "
                 "signal.signal(signal.SIGTERM, signal.SIG_IGN); "
                 f"Path({str(ready)!r}).write_text(json.dumps([os.getppid(), os.getpid()])); "
                 "time.sleep(30)")
        parent = ("import subprocess, sys; from pathlib import Path; "
                  f"subprocess.Popen([sys.executable, '-c', {child!r}], start_new_session=True, "
                  "stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL); "
                  f"Path({str(release)!r}).read_text()")
        owned = {}
        libc = ctypes.CDLL(None, use_errno=True)
        previous = ctypes.c_int()
        self.assertEqual(libc.prctl(37, ctypes.byref(previous), 0, 0, 0), 0)

        def cleanup_fixture():
            for worker, identity in owned.items():
                if completion.process_record(worker, live=True) == identity:
                    os.kill(worker, signal.SIGKILL)
                try:
                    os.waitpid(worker, 0)
                except ChildProcessError:
                    pass
            self.assertEqual(libc.prctl(36, previous.value, 0, 0, 0), 0)

        self.addCleanup(cleanup_fixture)

        def adopt():
            if not owned:
                leader, worker = json.loads(ready.read_text())
                owned[worker] = completion.process_record(worker)
                self.assertIsNotNone(owned[worker])
                release.write_text("exit")
                os.waitid(os.P_PID, leader, os.WEXITED | os.WNOWAIT)
            return {}  # Omit sampling; the kernel still owns the actual child.

        def assert_clean(expected_setting):
            current = ctypes.c_int()
            self.assertEqual(libc.prctl(37, ctypes.byref(current), 0, 0, 0), 0)
            remaining = [pid for pid in owned if completion.process_record(pid) is not None]
            print("Adopted-child cleanup:", json.dumps({
                "owned": list(owned), "remaining": remaining,
                "subreaper_expected": expected_setting, "subreaper_after": current.value,
            }), flush=True)
            self.assertEqual(remaining, [])
            for worker in owned:
                with self.assertRaises(ChildProcessError):
                    os.waitpid(worker, os.WNOHANG)
            self.assertEqual(current.value, expected_setting)

        return parent, adopt, assert_clean, libc, previous.value

    def test_unobserved_adopted_worker_is_reaped_before_scope_exit(self):
        parent, omit, assert_clean, _, previous = self.unobserved_detached_worker()
        with mock.patch.object(completion, "process_table", side_effect=omit), \
                mock.patch.object(completion, "TERMINATION_GRACE", .05):
            with self.assertRaisesRegex(RuntimeError, "still owns live descendants"):
                completion.execute([("orphan", self.command(parent))], self.directory,
                                   dict(os.environ), self.root)
        self.assertEqual(json.loads((self.directory / "orphan-exit.json").read_text()),
                         {"raw_exit_code": 0})
        self.assertEqual(self.report()["status"], "failed")
        assert_clean(previous)

    def test_child_scope_exits_reap_and_restore_prior_setting(self):
        from scripts.verification.processes import ChildScope
        libc = ctypes.CDLL(None, use_errno=True)
        previous = ctypes.c_int()
        self.assertEqual(libc.prctl(37, ctypes.byref(previous), 0, 0, 0), 0)
        # Exercise restoration to both values, rather than assuming the caller
        # originally had adoption disabled. No fixture child exists on entry.
        for setting in (1 - previous.value, previous.value):
            for exceptional in (False, True):
                with self.subTest(previous_setting=setting, exceptional=exceptional):
                    parent, adopt, assert_clean, _, _ = self.unobserved_detached_worker()
                    self.assertEqual(libc.prctl(36, setting, 0, 0, 0), 0)
                    error = OSError if exceptional else RuntimeError
                    message = "injected scope failure" if exceptional else "still owns live descendants"
                    with self.assertRaisesRegex(error, message):
                        with ChildScope(grace=.05):
                            process = subprocess.Popen(self.command(parent), cwd=self.root,
                                                       start_new_session=True)
                            adopt()
                            self.assertEqual(process.wait(), 0)
                            if exceptional:
                                raise OSError("injected scope failure")
                    assert_clean(setting)

    def test_concurrent_caller_is_rejected_before_launching_a_stage(self):
        release = threading.Event()
        thread = threading.Thread(target=release.wait)
        thread.start()
        try:
            with self.assertRaisesRegex(RuntimeError, "dedicated process"):
                completion.run_stage("unlaunched", self.command("pass"), self.directory,
                                     dict(os.environ), self.root)
            self.assertFalse((self.directory / "unlaunched.log").exists())
        finally:
            release.set()
            thread.join()

    def test_reaping_failure_retains_raw_exit_and_rejects_acceptance(self):
        from scripts.verification.processes import ChildScope
        reap = ChildScope.reap
        failed = False

        def fail_once(owner, *, terminate=False, deadline=None):
            nonlocal failed
            if terminate and not failed:
                failed = True
                raise OSError("injected orphan-reaping failure")
            return reap(owner, terminate=terminate, deadline=deadline)

        command = ("import signal, sys, time; "
                   "signal.signal(signal.SIGTERM, lambda *_: sys.exit(0)); time.sleep(30)")
        with mock.patch.object(ChildScope, "reap", fail_once), mock.patch.multiple(
                completion, STAGE_TIMEOUT=.5, TERMINATION_GRACE=.05, PROCESS_SAMPLE_INTERVAL=.01):
            with self.assertRaisesRegex(OSError, "orphan-reaping failure"):
                completion.execute([("gate", self.command(command))], self.directory,
                                   dict(os.environ), self.root)
        self.assertEqual(json.loads((self.directory / "gate-exit.json").read_text()),
                         {"raw_exit_code": 0})
        self.assertEqual(self.report()["status"], "failed")

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
        self.assertEqual(env["PYTHONUNBUFFERED"], "1")
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
                             "p = Path('.git/ready.tmp'); p.write_text(str(os.getpid())); "
                             "p.replace('.git/ready'); time.sleep(30)")
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
