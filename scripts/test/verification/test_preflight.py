"""Check prerequisite ordering, native failures and interrupted setup reporting."""

import json
import fcntl
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

from scripts.paths import ROOT
from scripts.verification import completion, preflight


class PreflightTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix='checker-preflight-')
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.report = self.root / '.git/report'
        subprocess.run(['git', 'init', '-q', str(self.root)], check=True)
        subprocess.run(['git', 'config', 'user.name', 'Preflight fixture'], cwd=self.root, check=True)
        subprocess.run(['git', 'config', 'user.email', 'fixture@example.invalid'], cwd=self.root, check=True)
        (self.root / 'source').write_text('fixture')
        subprocess.run(['git', 'add', 'source'], cwd=self.root, check=True)
        subprocess.run(['git', 'commit', '-qm', 'Fixture source'], cwd=self.root, check=True)
        self.report.mkdir()

    def test_real_local_socket_handshake(self):
        preflight.sockets()

    def test_socket_denial_fails_before_native_preparation(self):
        with mock.patch.object(preflight.socket, 'socketpair', side_effect=PermissionError('denied')), \
                mock.patch.object(preflight, 'native_tools') as native:
            with self.assertRaisesRegex(ValueError, 'socket preflight failed'):
                preflight.run(self.root, self.report, os.environ)
        native.assert_not_called()
        saved = json.loads((self.report / 'preflight.json').read_text())
        self.assertEqual((saved['status'], saved['active_step']), ('failed', 'sockets'))

    def test_publication_failure_precedes_sockets_and_native_preparation(self):
        with mock.patch.object(preflight, 'publication', side_effect=ValueError('missing historical records')), \
                mock.patch.object(preflight, 'sockets') as sockets, \
                mock.patch.object(preflight, 'native_tools') as native:
            with self.assertRaisesRegex(ValueError, 'historical records'):
                preflight.run(self.root, self.report, os.environ, release='2.0.0')
        sockets.assert_not_called()
        native.assert_not_called()
        self.assertEqual(json.loads((self.report / 'summary.json').read_text())['status'], 'failed')

    def test_native_failure_and_interruption_are_recorded_before_source_checks(self):
        for exception, status in ((ValueError('incompatible native ABI'), 'failed'),
                                  (KeyboardInterrupt(), 'interrupted')):
            with self.subTest(status=status), mock.patch.object(preflight, 'sockets'), \
                    mock.patch.object(preflight, 'native_tools', side_effect=exception):
                with self.assertRaises(type(exception)):
                    preflight.run(self.root, self.report, os.environ)
                self.assertEqual(json.loads((self.report / 'summary.json').read_text())['status'], status)

    def test_only_unresolved_case_families_require_native_prerequisites(self):
        with mock.patch.object(preflight, 'sockets') as sockets, \
                mock.patch.object(preflight, 'native_tools') as native:
            preflight.tooling(['scripts.test.verification.test_completion.Case.test_one'],
                              self.root, self.report, os.environ)
            sockets.assert_not_called()
            native.assert_not_called()
            preflight.tooling(['scripts.test.nanoda.test_modules.Case.test_one'],
                              self.root, self.report, os.environ)
            sockets.assert_not_called()
            self.assertEqual(native.call_args.kwargs, {'kernel': False, 'nanoda': True})
            preflight.tooling(['scripts.test.lean_module_data.test_kernel_equivalence.Case.test_one'],
                              self.root, self.report, os.environ)
            sockets.assert_called_once()
            self.assertEqual(native.call_args.kwargs, {'kernel': True, 'nanoda': False})

    def test_real_rust_linker_rejects_incompatible_library_before_tests(self):
        # Invalid metadata is an ABI-preflight control, never a fake kernel pass.
        source = self.root / 'scripts/nanoda'
        source.mkdir(parents=True)
        for name in ('scripts/build-nanoda-module-checker.sh', 'scripts/nanoda/Modules.rs'):
            target = self.root / name
            shutil.copy2(ROOT / name, target)
        release = self.root / '.external/nanoda/target/release'
        (release / 'deps').mkdir(parents=True)
        (release / 'libnanoda_lib.rlib').write_bytes(b'incompatible Rust library metadata fixture')
        (release / 'deps/libfixture.rlib').write_bytes(b'fixture dependency')
        with self.assertRaisesRegex(ValueError, 'pinned native library'):
            preflight.native_tools(self.root, self.report, dict(os.environ))
        log = (self.report / 'nanoda-preflight.log').read_text()
        self.assertIn('error', log)
        self.assertFalse(list((self.root / '.lake/nanoda-module-tools').glob('*/checker')))

    def test_release_source_is_rechecked_even_when_file_contents_do_not_change(self):
        expected = preflight.source(self.root)
        subprocess.run(['git', 'commit', '--allow-empty', '-qm', 'Different source commit'],
                       cwd=self.root, check=True)
        with self.assertRaisesRegex(ValueError, 'source changed'):
            preflight.source(self.root, expected)

    def test_completion_cannot_report_pass_when_final_release_pin_fails(self):
        def changed():
            raise ValueError('release source changed')
        with self.assertRaisesRegex(ValueError, 'release source changed'):
            completion.execute([('fixture', [sys.executable, '-c', 'pass'])], self.report,
                               dict(os.environ), self.root, finalize=changed)
        self.assertEqual(json.loads((self.report / 'summary.json').read_text())['status'], 'failed')

    def test_cli_holds_worktree_lock_and_stops_before_source_gates_on_preflight_failure(self):
        def unavailable(*args):
            lock_path = self.root / '.lake/completion-checks/lock'
            with lock_path.open('a+b') as other:
                with self.assertRaises(BlockingIOError):
                    fcntl.flock(other, fcntl.LOCK_EX | fcntl.LOCK_NB)
            raise ValueError('missing publication provenance')
        with mock.patch.object(completion, 'ROOT', self.root), \
                mock.patch.object(preflight, 'publication', side_effect=unavailable), \
                mock.patch.object(completion, 'execute') as checks, \
                mock.patch.object(os, 'sched_setaffinity'), \
                mock.patch.dict(os.environ, NANODA_BIN=sys.executable):
            self.assertEqual(completion.main(['--resume', '--release', '2.0.0', '--max-cores', '1']), 1)
        checks.assert_not_called()
        reports = list((self.root / '.lake/completion-checks').glob('*/summary.json'))
        self.assertEqual(len(reports), 1)
        self.assertEqual(json.loads(reports[0].read_text())['status'], 'failed')
