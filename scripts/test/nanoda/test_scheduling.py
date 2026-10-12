"""Exercise readiness, simultaneous checks, cancellation and owned descendants."""

from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
import sys
import tempfile
import threading
import time
import unittest

from scripts.nanoda.processes import ProcessSessions
from scripts.nanoda.scheduling import schedule


class SchedulingTests(unittest.TestCase):
    """Require checker progress during export, including multiple long checks."""

    def test_two_checkers_start_before_the_last_export_can_finish(self):
        events = [threading.Event(), threading.Event()]
        def export(index):
            if index == 2:
                if not all(event.wait(3) for event in events):
                    raise RuntimeError('ready checks were serialized or delayed until export completion')
            return index
        def check(index):
            if index < 2:
                events[index].set()
                if not all(event.wait(3) for event in events):
                    raise RuntimeError('checks did not run together')
            return index
        self.assertEqual(schedule([0, 1, 2], export, check, exporters=1, checkers=2,
                                  cancel=lambda: None), [(0, 0), (1, 1), (2, 2)])

    def test_failure_cancels_other_live_work_and_publishes_no_success(self):
        cancelled = threading.Event()
        def export(index):
            if index == 1:
                if not cancelled.wait(3):
                    raise RuntimeError('live export was not cancelled')
            return index
        def check(_):
            raise RuntimeError('independent checker rejected the stream')
        with self.assertRaisesRegex(RuntimeError, 'checker rejected'):
            schedule([0, 1], export, check, exporters=2, checkers=1, cancel=cancelled.set)
        self.assertTrue(cancelled.is_set())

    def test_sequential_mode_and_invalid_requests(self):
        exported = []
        def export(index):
            exported.append(index)
            return index
        def check(index):
            self.assertEqual(len(exported), 3)
            return index
        schedule([0, 1, 2], export, check, exporters=1, checkers=2,
                 cancel=lambda: None, pipeline=False)
        with self.assertRaises(ValueError):
            schedule([], export, check, exporters=1, checkers=2, cancel=lambda: None)

    def test_cancel_stops_a_child_even_after_its_group_leader_exits(self):
        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary)
            child = folder / 'child.py'
            child.write_text(
                'from pathlib import Path\nimport os, signal, time\n'
                f'folder = Path({str(folder)!r})\n'
                'def stop(*_):\n (folder / "stopped").write_text("stopped")\n raise SystemExit(0)\n'
                'signal.signal(signal.SIGTERM, stop)\n'
                '(folder / "pid").write_text(str(os.getpid()))\n'
                'time.sleep(30)\n')
            leader = folder / 'leader.py'
            leader.write_text(
                'import subprocess, sys, time\n'
                f'subprocess.Popen([sys.executable, {str(child)!r}])\n'
                'time.sleep(.5)\n')
            sessions = ProcessSessions()
            with ThreadPoolExecutor(max_workers=1) as pool:
                future = pool.submit(sessions.run, [sys.executable, str(leader)])
                try:
                    deadline = time.monotonic() + 5
                    while not (folder / 'pid').exists() and time.monotonic() < deadline:
                        time.sleep(.02)
                    self.assertTrue((folder / 'pid').exists())
                    time.sleep(.7)
                    sessions.cancel()
                    future.result(timeout=5)
                    self.assertTrue((folder / 'stopped').exists())
                    with self.assertRaisesRegex(RuntimeError, 'cancelled'):
                        sessions.run([sys.executable, '-c', 'raise SystemExit(99)'])
                finally:
                    sessions.cancel()

    def test_successful_helper_cannot_leave_a_child_that_closed_its_stdout(self):
        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary)
            child = folder / 'child.py'
            child.write_text(
                'from pathlib import Path\nimport os, signal, time\n'
                f'folder = Path({str(folder)!r})\n'
                'os.close(1)\n'
                'def stop(*_):\n (folder / "stopped").write_text("stopped")\n raise SystemExit(0)\n'
                'signal.signal(signal.SIGTERM, stop)\n'
                '(folder / "ready").write_text("ready")\n'
                'time.sleep(30)\n')
            leader = folder / 'leader.py'
            leader.write_text(
                'import subprocess, sys, time\n'
                f'subprocess.Popen([sys.executable, {str(child)!r}])\n'
                'time.sleep(.3)\nprint("success")\n')
            sessions = ProcessSessions()
            try:
                result = sessions.run([sys.executable, str(leader)])
                self.assertEqual(result.returncode, 0)
                self.assertEqual(result.stdout.strip(), 'success')
                self.assertTrue((folder / 'stopped').exists())
            finally:
                sessions.cancel()


if __name__ == '__main__':
    unittest.main()
