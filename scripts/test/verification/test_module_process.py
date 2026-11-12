"""Runaway module workers cannot turn termination or orphaned work into success."""

import json
from pathlib import Path
import signal
import sys
import tempfile
import unittest
from unittest import mock

from scripts.verification.module_process import lean, run, selected_timeout
from scripts.verification.processes import process_record


class ModuleProcessTests(unittest.TestCase):
    def test_explicit_build_deadline_keeps_default_and_rejects_invalid_bounds(self):
        self.assertEqual(selected_timeout({}), 120)
        self.assertEqual(selected_timeout({'CCL_MODULE_TIMEOUT_SECONDS': '300'}), 300)
        for value in ('', '0', '-1', 'nan', 'inf', '301', 'unbounded'):
            with self.subTest(value=value), self.assertRaises(ValueError):
                selected_timeout({'CCL_MODULE_TIMEOUT_SECONDS': value})
        with mock.patch.dict('os.environ', {'CCL_MODULE_TIMEOUT_SECONDS': '300'}), \
                mock.patch('scripts.verification.module_process.run', return_value=0) as worker:
            self.assertEqual(lean('checked-compiler', ['Fixture.lean'], 'reports'), 0)
            self.assertEqual(worker.call_args.kwargs['timeout'], 300)

    def test_timeout_rejects_zero_exit_even_with_closed_output(self):
        with tempfile.TemporaryDirectory() as temporary:
            code = run([sys.executable, "-c", "import os, signal, sys, time; "
                        "signal.signal(signal.SIGTERM, lambda *_: sys.exit(0)); "
                        "os.close(1); os.close(2); time.sleep(30)"],
                       "Slow", temporary, timeout=.3, grace=.1)
            receipt = json.loads(next(Path(temporary).glob("*.json")).read_text())
            self.assertEqual(code, 124)
            self.assertEqual(receipt["raw_exit_code"], 0)
            self.assertTrue(receipt["timed_out"])

    def test_timeout_kills_detached_term_resistant_descendant(self):
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "child"
            child = ("import os, signal, time; from pathlib import Path; "
                     f"Path({str(path)!r}).write_text(str(os.getpid())); "
                     "signal.signal(signal.SIGTERM, signal.SIG_IGN); time.sleep(30)")
            parent = ("import signal, subprocess, sys, time; "
                      "signal.signal(signal.SIGTERM, signal.SIG_IGN); "
                      f"subprocess.Popen([sys.executable, '-c', {child!r}], start_new_session=True); "
                      "time.sleep(30)")
            self.assertEqual(run([sys.executable, "-c", parent], "Slow", temporary,
                                 timeout=.5, grace=.05), 124)
            receipt = json.loads(next(Path(temporary).glob("*.json")).read_text())
            self.assertEqual(receipt["raw_exit_code"], -signal.SIGKILL)
            self.assertIsNone(process_record(int(path.read_text()), live=True))

    def test_success_records_individual_wall_time(self):
        with tempfile.TemporaryDirectory() as temporary:
            self.assertEqual(run([sys.executable, "-c", "pass"], "Fast", temporary), 0)
            receipt = json.loads(next(Path(temporary).glob("*.json")).read_text())
            self.assertFalse(receipt["timed_out"])
            self.assertEqual(receipt["raw_exit_code"], 0)
            self.assertGreater(receipt["seconds"], 0)
            self.assertEqual(receipt["wall_timeout_seconds"], 120)
            self.assertEqual(receipt["termination_grace_seconds"], 15)
            self.assertEqual(receipt["errors"], [])

    def test_tool_context_and_named_receipt_preserve_actual_output_and_exit(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            receipt = root / 'result.json'
            with (root / 'output.log').open('w') as log:
                code = run([sys.executable, '-c',
                            "import os; print(os.getcwd()); print(os.environ['CHECKER_TEST_VALUE'])"],
                           'fixture', root, cwd=root, env={'CHECKER_TEST_VALUE': 'bound environment'},
                           stdout=log, receipt_path=receipt, performance_target=None)
            self.assertEqual(code, 0)
            self.assertEqual((root / 'output.log').read_text().splitlines(), [str(root), 'bound environment'])
            self.assertEqual(json.loads(receipt.read_text())['raw_exit_code'], 0)
