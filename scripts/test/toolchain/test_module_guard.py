"""Verify compiler interception without changing the original SDK or metadata CLI."""

import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest import mock

from scripts.toolchain.module_guard import prepare


class GuardTests(unittest.TestCase):
    def metadata_fixture(self, root):
        """Supply an isolated SDK and control files without executing their bodies."""
        sdk = root / 'sdk'
        (sdk / 'bin').mkdir(parents=True)
        (sdk / 'lib/lean').mkdir(parents=True)
        (sdk / 'bin/lean').write_bytes(b'checked compiler fixture')
        (sdk / 'bin/lake').write_bytes(b'checked Lake fixture')
        for name in ('verification/module_process.py', 'verification/processes.py',
                     'nanoda/processes.py', 'nanoda/benchmark_pipeline.py'):
            path = root / 'scripts' / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text('original control fixture\n')
        return sdk

    def test_control_and_deadline_updates_reuse_legacy_sdk_path_with_current_bindings(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            sdk = self.metadata_fixture(root)
            with mock.patch('scripts.toolchain.module_guard.ROOT', root), \
                    mock.patch.dict(os.environ, {'CCL_MODULE_TIMEOUT_SECONDS': '120'}):
                guard = prepare(sdk, root / 'cache')
                old = json.loads((guard / 'MODULE-GUARD.json').read_text())
                legacy = guard.with_name('existing-sdk-path')
                guard.rename(legacy)
                helper = root / 'scripts/nanoda/benchmark_pipeline.py'
                helper.write_text('updated control fixture\n')
                with mock.patch.dict(os.environ, {'CCL_MODULE_TIMEOUT_SECONDS': '300'}):
                    self.assertEqual(prepare(sdk, root / 'cache'), legacy)
                current = json.loads((legacy / 'MODULE-GUARD.json').read_text())
                self.assertNotEqual(old['helpers'], current['helpers'])
                self.assertEqual(current['helpers'][str(helper)], hashlib.sha256(helper.read_bytes()).hexdigest())
                self.assertEqual(current['module_timeout_seconds'], 300)
                (sdk / 'bin/lean').write_bytes(b'new checked compiler fixture')
                self.assertNotEqual(prepare(sdk, root / 'cache'), legacy)

    def test_control_rebinding_rejects_sdk_damage_and_keeps_previous_record(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            sdk = self.metadata_fixture(root)
            with mock.patch('scripts.toolchain.module_guard.ROOT', root):
                guard = prepare(sdk, root / 'cache')
                before = (guard / 'MODULE-GUARD.json').read_bytes()
                (guard / 'lib').unlink()
                (guard / 'lib').symlink_to(root)
                with mock.patch.dict(os.environ, {'CCL_MODULE_TIMEOUT_SECONDS': '300'}), \
                        self.assertRaises(ValueError):
                    prepare(sdk, root / 'cache')
                self.assertEqual((guard / 'MODULE-GUARD.json').read_bytes(), before)

    def test_lake_symlink_cannot_bypass_the_guard_even_with_identical_bytes(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            sdk = self.metadata_fixture(root)
            with mock.patch('scripts.toolchain.module_guard.ROOT', root):
                guard = prepare(sdk, root / 'cache')
                (guard / 'bin/lake').unlink()
                (guard / 'bin/lake').symlink_to(sdk / 'bin/lake')
                with self.assertRaises(ValueError):
                    prepare(sdk, root / 'cache')

    def test_complete_overlay_reuses_sdk_and_preserves_metadata_dispatch(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            sdk = root / 'sdk'
            (sdk / 'bin').mkdir(parents=True)
            (sdk / 'lib/lean').mkdir(parents=True)
            compiler = sdk / 'bin/lean'
            compiler.write_text('#!/usr/bin/env python3\nimport sys\nprint(" ".join(sys.argv[1:]))\n')
            compiler.chmod(0o755)
            (sdk / 'bin/lake').write_bytes(b'checked lake executable')
            original = compiler.read_bytes()
            with mock.patch('scripts.toolchain.module_guard.ROOT', root):
                # The generated shim imports the real repository helper; put
                # only its durable report location under this isolated root.
                from scripts.paths import ROOT
                (root / 'scripts').symlink_to(ROOT / 'scripts', target_is_directory=True)
                guard = prepare(sdk, root / 'cache')
                self.assertEqual(prepare(sdk, root / 'cache'), guard)
            self.assertEqual(compiler.read_bytes(), original)
            self.assertEqual((guard / 'lib').resolve(), (sdk / 'lib').resolve())
            self.assertFalse((guard / 'bin/lake').is_symlink())
            self.assertEqual(subprocess.check_output([guard / 'bin/lean', '--githash'], text=True), '--githash\n')
            self.assertFalse((root / '.lake/module-times').exists())
            subprocess.run([guard / 'bin/lean', 'Fixture.lean'], check=True, stdout=subprocess.DEVNULL,
                           env=dict(os.environ, CCL_MODULE_TIMEOUT_SECONDS='300'))
            self.assertEqual(len(list((root / '.lake/module-times/lean').glob('*.json'))), 1)
            receipt = next((root / '.lake/module-times/lean').glob('*.json'))
            self.assertEqual(json.loads(receipt.read_text())['wall_timeout_seconds'], 300)
            (guard / 'bin/lean').write_text('damaged')
            with mock.patch('scripts.toolchain.module_guard.ROOT', root), self.assertRaises(ValueError):
                prepare(sdk, root / 'cache')
