"""Exercise local completed-check records, not mathematical proof certificates."""

import json
import contextlib
import io
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

from scripts.verification.checkpoints import Checkpoints, Inputs


class CheckpointTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix='completed-checks-')
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        subprocess.run(['git', 'init', '-q', str(self.root)], check=True)
        (self.root / '.git/info/exclude').write_text('.lake/\n.external/\nSDK/\n')
        (self.root / 'source').write_text('original source')
        self.store = Checkpoints(self.root / '.lake/completed')
        excluded = {'LEAN_SYSROOT', 'LEAN_PATH', 'CCL_CORE_PREFIX', 'CCL_TEST_CORE_PREFIX', 'NANODA_BIN'}
        self.environment = {key: value for key, value in os.environ.items() if key not in excluded}
        self.inputs = Inputs(self.root, self.environment, self.store)

    def request(self):
        return self.inputs.request('fixture', [sys.executable, '-c', 'pass'])

    def success(self):
        log = self.root / '.git/output.log'
        log.write_text('observed subprocess output\n')
        return {'name': 'fixture', 'command': [sys.executable, '-c', 'pass'],
                'exit_code': 0, 'raw_exit_code': 0, 'timed_out': False,
                'errors': [], 'log': str(log), 'seconds': 1}

    def test_completed_output_survives_original_run_removal_and_corruption_is_rejected(self):
        request, result = self.request(), self.success()
        self.store.save(request, result)
        Path(result['log']).unlink()
        saved = self.store.lookup(request)
        self.assertTrue(saved['reused'])
        self.assertEqual(Path(saved['log']).read_text(), 'observed subprocess output\n')
        Path(saved['log']).write_text('corrupt output')
        self.assertIsNone(self.store.lookup(request))

    def test_failures_timeouts_and_cleanup_errors_cannot_be_saved(self):
        request, result = self.request(), self.success()
        for changes in ({'exit_code': 7}, {'raw_exit_code': -9}, {'timed_out': True},
                        {'errors': ['child survived']}):
            with self.subTest(changes=changes), self.assertRaises(ValueError):
                self.store.save(request, dict(result, **changes))
        self.assertIsNone(self.store.lookup(request))

    def test_all_compiled_parts_new_inputs_and_source_changes_invalidate_success(self):
        library = self.root / '.lake/build/lib/lean'
        library.mkdir(parents=True)
        for suffix in ('.olean', '.olean.private', '.olean.server', '.ir'):
            path = library / ('Fixture' + suffix)
            path.write_text('protocol fixture, not a Lean artifact')
            before = self.request()
            self.store.save(before, self.success())
            path.write_text('changed serialized input')
            self.assertIsNone(self.store.lookup(self.request()), suffix)
        before = self.request()
        self.store.save(before, self.success())
        (library / 'New.olean').write_text('new input')
        self.assertIsNone(self.store.lookup(self.request()))
        before = self.request()
        self.store.save(before, self.success())
        (self.root / 'source').write_text('changed source')
        self.assertIsNone(self.store.lookup(self.request()))

    def test_native_repair_does_not_invalidate_non_native_checks(self):
        release = self.root / '.external/nanoda/target/release'
        release.mkdir(parents=True)
        compiler = release / 'rustc-fixture'
        compiler.write_text('#!/bin/sh\nprintf "fixture Rust compiler\\n"\n')
        compiler.chmod(0o755)
        library = release / 'libnanoda_lib.rlib'
        library.write_text('old compiler library fixture')
        inputs = Inputs(self.root, dict(self.environment, RUSTC=str(compiler)), self.store)
        command = [sys.executable, '-c', 'pass']
        horner = inputs.request('horner', command)
        native = inputs.request('native', command, native=True)
        self.store.save(horner, dict(self.success(), name='horner'))
        self.store.save(native, dict(self.success(), name='native'))
        library.write_text('repaired compiler library fixture')
        self.assertIsNotNone(self.store.lookup(inputs.request('horner', command)))
        self.assertIsNone(self.store.lookup(inputs.request('native', command, native=True)))

    def test_changed_module_watchdog_cannot_reuse_a_different_execution_budget(self):
        command = [sys.executable, '-c', 'pass']
        exception = Inputs(self.root, dict(self.environment, CCL_MODULE_TIMEOUT_SECONDS='300'), self.store)
        ordinary = Inputs(self.root, dict(self.environment, CCL_MODULE_TIMEOUT_SECONDS='120'), self.store)
        self.store.save(exception.request('fixture', command), self.success())
        self.assertIsNone(self.store.lookup(ordinary.request('fixture', command)))

    def test_missing_or_corrupt_shared_input_manifest_prevents_reuse(self):
        request = self.request()
        self.store.save(request, self.success())
        key = request['bindings']['compiled']
        manifest = self.store.directory / 'inputs' / (key + '.json')
        original = manifest.read_text()
        manifest.write_text(json.dumps({'wrong': 'compiled inputs'}))
        self.assertIsNone(self.store.lookup(request))
        manifest.write_text(original)
        self.assertIsNotNone(self.store.lookup(request))
        manifest.unlink()
        self.assertIsNone(self.store.lookup(request))

    def test_python_consumers_invalidate_without_invalidating_unrelated_tools(self):
        files = {
            'scripts/__init__.py': '',
            'scripts/test/__init__.py': '',
            'scripts/test/subject/__init__.py': '',
            'scripts/test/subject/test_case.py': 'from scripts.helper import operation\n',
            'scripts/helper.py': 'def operation(): return 1\n',
            'scripts/unrelated.py': 'value = 1\n',
        }
        for name, content in files.items():
            path = self.root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(content)
        name = 'scripts.test.subject.test_case.Case.test_operation'
        command = [sys.executable, '-c', 'pass']
        request = self.inputs.request(name, command)
        self.store.save(request, dict(self.success(), name=name))
        (self.root / 'scripts/unrelated.py').write_text('value = 2\n')
        self.assertIsNotNone(self.store.lookup(self.inputs.request(name, command)))
        (self.root / 'scripts/helper.py').write_text('def operation(): return 2\n')
        self.assertIsNone(self.store.lookup(self.inputs.request(name, command)))

    def test_unknown_dynamic_python_loading_conservatively_binds_all_python(self):
        case = self.root / 'scripts/test/subject/test_case.py'
        case.parent.mkdir(parents=True)
        unrelated = self.root / 'scripts/unrelated.py'
        name = 'scripts.test.subject.test_case.Case.test_operation'
        command = [sys.executable, '-c', 'pass']
        for source in ('exec("dynamically selected code")', '__import__(module_name)',
                       '__import__("scripts.helper", fromlist=members)',
                       '__import__("helper", level=relative_level)'):
            with self.subTest(source=source):
                case.write_text(source + '\n')
                unrelated.write_text('value = 1\n')
                request = self.inputs.request(name, command)
                self.store.save(request, dict(self.success(), name=name))
                unrelated.write_text('value = 2\n')
                self.assertIsNone(self.store.lookup(self.inputs.request(name, command)))

    def test_literal_imports_bind_module_and_fromlist_owners_without_unrelated_python(self):
        paths = {'scripts/test/subject/test_case.py': '',
                 'scripts/helper.py': 'def operation(): return 1\n',
                 'scripts/retained/__init__.py': '',
                 'scripts/retained/child.py': 'value = 1\n',
                 'scripts/unrelated.py': 'value = 1\n'}
        for name, content in paths.items():
            path = self.root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(content)
        name = 'scripts.test.subject.test_case.Case.test_operation'
        command = [sys.executable, '-c', 'pass']
        for source, dependency in (
                ('__import__("scripts.helper")', 'scripts/helper.py'),
                ('__import__("scripts.helper", fromlist=["operation"])', 'scripts/helper.py'),
                ('__import__("scripts.retained", fromlist=["child"])', 'scripts/retained/child.py'),
                ('__import__("functools")', None)):
            with self.subTest(source=source):
                (self.root / 'scripts/test/subject/test_case.py').write_text(source + '\n')
                unrelated = self.root / 'scripts/unrelated.py'
                unrelated.write_text('value = 1\n')
                request = self.inputs.request(name, command)
                self.store.save(request, dict(self.success(), name=name))
                unrelated.write_text('value = 2\n')
                self.assertIsNotNone(self.store.lookup(self.inputs.request(name, command)))
                if dependency:
                    path = self.root / dependency
                    path.write_text(path.read_text() + '\nchanged = True\n')
                    self.assertIsNone(self.store.lookup(self.inputs.request(name, command)))

    def test_default_sdk_private_parts_and_command_input_files_are_bound(self):
        sdk = self.root / '.lake/core-toolchain/lib/lean'
        sdk.mkdir(parents=True)
        private = sdk / 'Init.olean.private'
        private.write_text('private SDK fixture')
        request = self.request()
        self.store.save(request, self.success())
        private.write_text('changed SDK fixture')
        self.assertIsNone(self.store.lookup(self.request()))
        data = self.root / '.git/runtime-input'
        data.write_text('original argument input')
        command = [sys.executable, '-c', 'pass', str(data)]
        request = self.inputs.request('fixture', command)
        self.store.save(request, dict(self.success(), command=command))
        data.write_text('changed argument input')
        self.assertIsNone(self.store.lookup(self.inputs.request('fixture', command)))

    def test_invalidation_explains_changed_input_group(self):
        request = self.request()
        self.store.save(request, self.success())
        (self.root / 'source').write_text('changed source')
        output = io.StringIO()
        with contextlib.redirect_stdout(output):
            self.assertIsNone(self.store.lookup(self.request()))
        self.assertIn('source dependencies', output.getvalue())
