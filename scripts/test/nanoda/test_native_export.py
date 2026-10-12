"""Exercise native artifact import, exact records, provenance and real nanoda checks.

Run through ``scripts/run-lake.sh env python3 -m unittest``. Fixture artifacts
are isolated; missing parts and proof edits never alter project build outputs.
"""

import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time
import unittest

from scripts.lean_module_data.audit import SUPPORT
from scripts.lean_module_data.paths import search_path
from scripts.nanoda.artifact_inputs import compiled_inputs, digest, verify_inputs
from scripts.nanoda.build_exporter import build, initialize_meta_entrypoint
from scripts.nanoda.compare_exports import compare
from scripts.nanoda.export_cache import export_group
from scripts.nanoda.planning import group_inputs, plan
from scripts.nanoda.processes import process_record
from scripts.nanoda.root_inventory import authoritative_roots, validate_roots


from scripts.paths import ROOT
CHECKER = Path(os.environ.get('NANODA_BIN', ROOT / '.external/nanoda/target/release/nanoda_bin'))


class NativeExportTests(unittest.TestCase):
    """Check complete private imports without target code execution."""

    @classmethod
    def setUpClass(cls):
        cls.binary = build(ROOT / '.lake/nanoda-tools')
        if not CHECKER.is_file():
            raise RuntimeError('the real pinned nanoda checker is required')

    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix='nanoda-native-fixtures-')
        self.addCleanup(self.temporary.cleanup)
        self.work = Path(self.temporary.name)
        self.library = self.work / 'library'
        self.library.mkdir()
        self.search = [self.library, *search_path()]
        self.env = dict(os.environ, LEAN_PATH=os.pathsep.join(map(str, self.search)),
                        NANODA_INITIALIZER_MARKER=str(self.work / 'initializer-ran'),
                        NANODA_CALLBACK_MARKER=str(self.work / 'callback-ran'))

    def compile(self, module, source):
        """Compile a copied fixture with the same module identity across variants."""
        copied = self.work / 'sources' / (module.replace('.', '/') + '.lean')
        copied.parent.mkdir(parents=True, exist_ok=True)
        copied.write_text(source)
        target = self.library / (module.replace('.', '/') + '.olean')
        target.parent.mkdir(parents=True, exist_ok=True)
        result = subprocess.run(['lean', '-R', str(self.work / 'sources'), '-DwarningAsError=true',
                                 '-o', str(target), str(copied)], env=self.env,
                                capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        return target

    def export(self, modules, name='native', *, success=True):
        """Capture a complete native stream and root inventory from isolated inputs."""
        manifest = self.work / f'{name}.modules'
        manifest.write_text('\n'.join(modules) + '\n')
        stream, roots = self.work / f'{name}.ndjson', self.work / f'{name}.roots.json'
        with stream.open('wb') as output:
            result = subprocess.run([str(self.binary), '--export', str(manifest), str(roots)],
                                    env=self.env, stdout=output, stderr=subprocess.PIPE, text=True)
        self.assertEqual(result.returncode == 0, success, result.stderr)
        return stream, roots, result.stderr

    def check(self, stream, *, success=True):
        """Require the real checker and its exact-byte receipt helper to accept or reject."""
        result = subprocess.run(['python3', '-m', 'scripts.nanoda.check_stream',
                                 '--checker', str(CHECKER), '--config',
                                 str(ROOT / 'scripts/nanoda/config.json'), '--cache',
                                 str(self.work / 'checked'), str(stream)],
                                env=self.env, capture_output=True, text=True)
        self.assertEqual(result.returncode == 0, success, result.stdout + result.stderr)
        return result.stdout + result.stderr

    def audit_fixture(self, module, source, expected_roots):
        """Audit normal fixture closures with the authoritative project backend.

        Canonical checking remains with check-axioms.sh and its existing cache;
        this fresh temporary project checks every fixture root and dependency.
        """
        copied = self.work / 'sources' / (module.replace('.', '/') + '.lean')
        self.assertEqual(copied.read_text(), source)
        inputs = compiled_inputs(list(dict.fromkeys([module, *SUPPORT])), self.search)
        code = [ROOT / 'scripts/project-module-data.py', ROOT / 'scripts/paths.py',
                ROOT / 'lean-toolchain', Path(__file__),
                ROOT / 'scripts/nanoda/artifact_inputs.py',
                ROOT / 'scripts/nanoda/root_inventory.py',
                *sorted((ROOT / 'scripts/lean_module_data').glob('*.py'))]
        source_path = ROOT / 'scripts/test/fixtures/nanoda/Dependencies.lean'
        pins = {str(path): digest(path) for path in [copied, source_path, *code]}
        manifests = {}
        for role in ('project', 'assigned', 'imports'):
            manifests[role] = self.work / f'audit-{role}.modules'
            manifests[role].write_text(module + '\n')
        result_path = self.work / 'audit-results.tsv'
        command = [sys.executable, str(ROOT / 'scripts/project-module-data.py'), 'audit',
                   '--project', str(manifests['project']),
                   '--assigned', str(manifests['assigned']),
                   '--imports', str(manifests['imports']), '--canonical', 'false',
                   '--result', str(result_path)]
        for path in self.search:
            command.extend(['--search-path', str(path)])
        result = subprocess.run(command, cwd=ROOT, env=self.env,
                                text=True, capture_output=True)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        verify_inputs(inputs, self.search)
        self.assertEqual(pins, {path: digest(path) for path in pins})
        closures = Path(str(result_path) + '.closures.jsonl')
        rows = [json.loads(line) for line in closures.read_text().splitlines()]
        self.assertTrue(rows, 'an empty fixture audit establishes no coverage')
        for row in rows:
            self.assertEqual(row['kind'], 'root')
            self.assertEqual(row['scanned_module'], module)
            self.assertFalse(row['canonical'])
            self.assertFalse(row['all_helpers'])
            self.assertEqual(row['axioms'], [], row['name'])
        audited = [{'scanned_module': row['scanned_module'], 'owner': row['owner'],
                    'name': row['name'], 'phase': 'kernel'} for row in rows]
        self.assertEqual(audited, expected_roots['roots'])
        self.assertEqual(result_path.read_text().splitlines(),
                         [f'project\t{module}\t{len(rows)}'])
        receipt = {'selected_module': module, 'canonical': False, 'all_helpers': False,
                   'command': command, 'inputs': inputs, 'source_and_code': pins,
                   'manifests': {role: digest(path) for role, path in manifests.items()},
                   'results_sha256': digest(result_path), 'closures_sha256': digest(closures)}
        (self.work / 'fixture-audit-receipt.json').write_text(json.dumps(receipt, sort_keys=True) + '\n')

    def test_mutual_groups_literals_private_bodies_and_complete_record_comparison(self):
        module = 'NanodaDependencyFixture'
        source = (ROOT / 'scripts/test/fixtures/nanoda/Dependencies.lean').read_text()
        self.compile(module, source)
        stream, inventory, _ = self.export([module])
        roots = json.loads(inventory.read_text())
        validate_roots(roots, authoritative_roots([module], self.search))
        names = {row['name'] for row in roots['roots']}
        certificates = {f'{module}.{tree}.branch.{law}'
                        for tree in ('LeftTree', 'RightTree') for law in ('inj', 'injEq')}
        self.assertTrue(certificates <= names, 'both original mutual constructor APIs must remain roots')
        self.assertNotIn(f'{module}.LeftTree.leaf.inj', names)
        self.assertNotIn(f'{module}.LeftTree.leaf.injEq', names)
        self.audit_fixture(module, source, roots)
        manifest = self.work / 'native.modules'
        reference = self.work / 'reference.ndjson'
        subprocess.run(['python3', '-m', 'scripts.test.nanoda.reference_export',
                        str(manifest), str(reference)], env=self.env, check=True, capture_output=True)
        self.assertGreater(compare([reference], [stream]), 400)
        self.check(reference)
        self.check(stream)

    def test_target_initializers_callbacks_meta_unsafe_and_registered_rewrite(self):
        module = 'ImportEffects'
        self.compile(module, (ROOT / 'scripts/test/fixtures/nanoda/ImportEffects.lean').read_text())
        # Declaration-time initialization is permitted when compiling the fixture.
        # Artifact import must not execute it again.
        for marker in ('initializer-ran', 'callback-ran'):
            (self.work / marker).unlink(missing_ok=True)
        stream, inventory, _ = self.export([module])
        roots = json.loads(inventory.read_text())
        validate_roots(roots, authoritative_roots([module], self.search))
        names = {row['name'] for row in roots['roots']}
        self.assertIn('NanodaImportEffects.compiler.eq_def', names)
        self.assertTrue(any(name.startswith('_private.') and name.endswith('.unusedProof') for name in names))
        self.assertNotIn('NanodaImportEffects.metaValue', names)
        self.assertNotIn('NanodaImportEffects.unsafeValue', names)
        self.check(stream)
        for marker in ('initializer-ran', 'callback-ran'):
            self.assertFalse((self.work / marker).exists())

    def test_private_proof_changes_and_missing_or_stale_parts_are_bound(self):
        module = 'ImportEffects'
        source = (ROOT / 'scripts/test/fixtures/nanoda/ImportEffects.lean').read_text()
        target = self.compile(module, source)
        context = compiled_inputs([module], self.search)
        first, _, _ = self.export([module], 'first')
        before = digest(target)
        self.compile(module, source.replace('by exact True.intro', 'by exact (id True.intro)'))
        self.assertEqual(digest(target), before, 'private proof edit must preserve the public interface')
        with self.assertRaisesRegex(ValueError, 'compiled input changed'):
            verify_inputs(context, self.search)
        changed = compiled_inputs([module], self.search)
        self.assertNotEqual(context, changed)
        second, _, _ = self.export([module], 'second')
        self.assertNotEqual(digest(first), digest(second))
        self.check(second)
        for suffix in ('.olean.private', '.olean.server', '.ir'):
            part = target.with_suffix(suffix)
            saved = part.read_bytes()
            part.unlink()
            with self.subTest(suffix=suffix):
                with self.assertRaises((ValueError, FileNotFoundError)):
                    compiled_inputs([module], self.search)
                if suffix != '.ir':
                    self.export([module], f'missing-{suffix}', success=False)
            part.write_bytes(saved)

    def test_dirty_private_proof_is_rejected_by_the_real_checker(self):
        source = (ROOT / 'scripts/test/fixtures/module_verification/Explicit.lean').read_text()
        self.compile('ModuleVerification.Explicit', source)
        stream, inventory, _ = self.export(['ModuleVerification.Explicit'])
        validate_roots(json.loads(inventory.read_text()),
                       authoritative_roots(['ModuleVerification.Explicit'], self.search))
        report = self.check(stream, success=False)
        self.assertIn('unpermitted axiom', report)
        self.assertIn('propext', report)
        self.assertEqual(list((self.work / 'checked').glob('*.json')), [])

    def test_legacy_module_and_exposed_facade_keep_complete_private_dependencies(self):
        fixtures = ROOT / 'scripts/test/fixtures/module_verification'
        for name in ('Explicit', 'Facade', 'Legacy'):
            source = (fixtures / f'{name}.lean').read_text()
            # Keep the retained negative fixture unchanged; repair only this copy.
            if name == 'Explicit':
                source = source.replace('propext Iff.rfl', 'rfl')
            self.compile(f'ModuleVerification.{name}', source)
        modules = [f'ModuleVerification.{name}' for name in ('Explicit', 'Facade', 'Legacy')]
        stream, inventory, _ = self.export(modules)
        roots = json.loads(inventory.read_text())
        validate_roots(roots, authoritative_roots(modules, self.search))
        names = {row['name'] for row in roots['roots']}
        self.assertIn('ModuleVerification.legacyFacadeClient', names)
        self.assertIn('ModuleVerification.hiddenValue_readback', names)
        self.assertTrue(any(name.startswith('_private.') and name.endswith('.privateBridge') for name in names))
        self.check(stream)

    def test_cache_reload_corruption_and_incomplete_export_recovery(self):
        module = 'ImportEffects'
        self.compile(module, (ROOT / 'scripts/test/fixtures/nanoda/ImportEffects.lean').read_text())
        context = compiled_inputs([module], self.search)
        # export_group's subprocess inherits the ambient search path.
        from unittest.mock import patch
        with patch.dict(os.environ, self.env):
            folder, receipt, hit = export_group([module], context, self.binary,
                                                self.work / 'exported', self.search, 'fixture')
            self.assertFalse(hit)
            before = {path.name: path.stat().st_mtime_ns for path in folder.iterdir()
                      if path.suffix != '.lock'}
            self.assertTrue(export_group([module], context, self.binary,
                                         self.work / 'exported', self.search, 'fixture')[2])
            self.assertEqual(before, {path.name: path.stat().st_mtime_ns for path in folder.iterdir()
                                     if path.suffix != '.lock'})
            self.check(folder / 'stream.ndjson')
            stream = folder / 'stream.ndjson'
            saved = stream.read_bytes()
            stream.write_bytes(b'!' + saved[1:])
            with self.assertRaisesRegex(ValueError, 'corrupt completed native export'):
                export_group([module], context, self.binary, self.work / 'exported', self.search, 'fixture')
            stream.write_bytes(saved)
            (folder / 'complete.json').unlink()
            stream.write_bytes(b'interrupted export')
            restored, second, hit = export_group([module], context, self.binary,
                                                 self.work / 'exported', self.search, 'fixture')
            self.assertFalse(hit)
            self.assertEqual(second, receipt)
            self.assertEqual((restored / 'stream.ndjson').read_bytes(), saved)

    def test_empty_duplicate_and_missing_module_requests_fail(self):
        for modules in ([], ['Init', 'Init'], ['NoSuchNanodaFixture']):
            with self.subTest(modules=modules):
                self.export(modules, success=False)

    def test_coordinator_interrupts_export_and_check_descendants_then_reuses_completed_work(self):
        # Keep the interruption watchdog focused on process cleanup and replay;
        # importing all of Lean adds unrelated root-inventory preparation here.
        module = 'CoordinatorLifecycle'
        self.compile(module, '''module

/-- A kernel-checked witness retained across coordinator interruption and replay. -/
public theorem checkpointWitness : True := True.intro
''')
        manifest = self.work / 'selected.modules'
        manifest.write_text(module + '\n')
        cache = self.work / 'pipeline-cache'
        wrappers = []
        for role, executable in [('export', self.binary), ('check', CHECKER)]:
            folder = self.work / role
            folder.mkdir()
            child = folder / 'child.py'
            child.write_text(
                'import os, signal, time\nfrom pathlib import Path\n'
                f'folder = Path({str(folder)!r})\n'
                'def stop(*_):\n (folder / "stopped").write_text("stopped")\n raise SystemExit(0)\n'
                'signal.signal(signal.SIGTERM, stop)\n'
                '(folder / "child-pid").write_text(str(os.getpid()))\n'
                'time.sleep(120)\n')
            wrapper = folder / 'wrapper'
            wrapper.write_text(
                '#!/usr/bin/env python3\nimport os, subprocess, sys, time\nfrom pathlib import Path\n'
                f'folder = Path({str(folder)!r})\n'
                'if not (folder / "release").exists():\n'
                f' subprocess.Popen([sys.executable, {str(child)!r}])\n'
                ' while not (folder / "child-pid").exists(): time.sleep(.01)\n'
                ' (folder / "blocked").write_text("blocked")\n'
                ' time.sleep(120)\n'
                f'os.execv({str(executable)!r}, [{str(executable)!r}, *sys.argv[1:]])\n')
            wrapper.chmod(0o755)
            wrappers.append(wrapper)
        harness = self.work / 'coordinator.py'
        harness.write_text(
            'from pathlib import Path\nfrom unittest.mock import patch\n'
            'from scripts.nanoda.pipeline import run\n'
            f'with patch("scripts.nanoda.pipeline.build", return_value=Path({str(wrappers[0])!r})):\n'
            f' run({str(manifest)!r}, {str(cache)!r}, {str(wrappers[1])!r}, '
            f'{str(ROOT / "scripts/nanoda/config.json")!r}, exporters=1, checkers=1)\n')
        environment = dict(self.env, PYTHONPATH=str(ROOT))
        for role in ('export', 'check'):
            folder = self.work / role
            with (self.work / f'interrupted-{role}.log').open('w') as output:
                process = subprocess.Popen([sys.executable, str(harness)], env=environment,
                                           stdout=output, stderr=subprocess.STDOUT, start_new_session=True)
                try:
                    deadline = time.monotonic() + 30
                    while not (folder / 'blocked').exists() and process.poll() is None:
                        if time.monotonic() > deadline:
                            self.fail(f'{role} never reached its interruption point')
                        time.sleep(.02)
                    self.assertTrue((folder / 'blocked').exists())
                    child_pid = int((folder / 'child-pid').read_text())
                    child_identity = process_record(child_pid, live=True)
                    self.assertIsNotNone(child_identity)
                    process.terminate()
                    self.assertNotEqual(process.wait(timeout=10), 0)
                    self.assertTrue((folder / 'stopped').exists())
                    self.assertNotEqual(process_record(child_pid, live=True), child_identity)
                finally:
                    if process.poll() is None:
                        process.terminate()
                        process.wait(timeout=10)
            self.assertEqual(list((cache / 'nanoda-runs').glob('*/checked.json')), [])
            self.assertEqual(list((cache / 'nanoda-checked').glob('*.json')), [])
            completed = list((cache / 'nanoda-native').glob('*/complete.json'))
            self.assertEqual(len(completed), 0 if role == 'export' else 1)
            (folder / 'release').write_text('release')
        before = digest(completed[0])
        result = subprocess.run([sys.executable, str(harness)], env=environment,
                                capture_output=True, text=True, timeout=30)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn('retained=True', result.stdout)
        self.assertEqual(digest(completed[0]), before)
        reports = list((cache / 'nanoda-runs').glob('*/checked.json'))
        self.assertEqual(len(reports), 1)
        self.assertGreater(json.loads(reports[0].read_text())['groups'][0][1]['result']['declarations'], 0)

    def test_colliding_standalone_names_keep_scanned_owners_and_distinct_proofs(self):
        modules = ['scripts.First', 'scripts.Second']
        for module, number in zip(modules, (3, 7)):
            self.compile(module, f'module\npublic import Init\n'
                         f'/-- A standalone entrypoint fixture. -/\npublic def main : IO UInt32 := pure {number}\n')
        (self.work / 'lakefile.toml').write_text(
            '[[lean_exe]]\nname="first"\nroot="scripts.First"\n'
            '[[lean_exe]]\nname="second"\nroot="scripts.Second"\n')
        context = compiled_inputs(modules, self.search)
        groups = plan(modules, context, self.work)
        self.assertEqual(groups, [[modules[0]], [modules[1]]])
        streams = []
        for index, group in enumerate(groups):
            selected = group_inputs(context, group)
            verify_inputs(selected, self.search)
            stream, inventory, _ = self.export(group, f'owner-{index}')
            roots = json.loads(inventory.read_text())
            validate_roots(roots, authoritative_roots(group, self.search))
            self.assertIn({'name': 'main', 'scanned_module': group[0],
                           'owner': group[0], 'phase': 'kernel'}, roots['roots'])
            self.check(stream)
            streams.append(stream)
        self.assertNotEqual(digest(streams[0]), digest(streams[1]))

    def test_bootstrap_change_fails_closed(self):
        with self.assertRaisesRegex(ValueError, 'bootstrap no longer matches'):
            initialize_meta_entrypoint('changed compiler main')


if __name__ == '__main__':
    unittest.main()
