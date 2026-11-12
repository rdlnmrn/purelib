"""Reject producer root omissions, duplicate declarations and damaged cache records."""

import json
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest import mock

from scripts.nanoda.artifact_inputs import digest
from scripts.nanoda.export_cache import atomic_json, export_group, prepare_native, prepare_roots, reload_group, validate_coverage
from scripts.nanoda.root_inventory import validate_roots


class ExportValidationTests(unittest.TestCase):
    """Coverage is derived from stream declarations and independently selected identities."""

    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.folder = Path(self.temp.name)
        self.roots = {'schema': 2, 'selected_modules': ['Fixture'],
                      'roots': [{'scanned_module': 'Fixture', 'owner': 'Fixture',
                                 'name': 'required', 'phase': 'kernel'}]}
        self.records = [{'meta': {}}, {'in': 1, 'str': {'pre': 0, 'str': 'required'}},
                        {'ie': 0, 'sort': 0},
                        {'def': {'name': 1, 'levelParams': [], 'type': 0, 'value': 0,
                                 'hints': 'opaque', 'safety': 'safe', 'all': []}}]
        self.stream = self.folder / 'stream.ndjson'

    def prepared_context(self):
        """Bind fake artifact bytes for cache-protocol tests, without claiming Lean validity."""
        library = self.folder / 'library'
        library.mkdir()
        files = []
        for suffix in ('.olean', '.olean.server', '.olean.private'):
            path = library / ('Fixture' + suffix)
            path.write_text('fixture ' + suffix)
            files.append(str(path))
        context = {'schema': 2, 'selected_modules': ['Fixture'],
                   'inventory': {'schema': 1, 'roots': ['Fixture'],
                                 'modules': [{'name': 'Fixture', 'imports': [], 'files': files}]},
                   'files': {path: digest(path) for path in files}}
        return context, [library]

    def write_stream(self, records):
        self.stream.write_text(''.join(json.dumps(row) + '\n' for row in records))

    def test_actual_stream_coverage_rejects_missing_or_repeated_declarations(self):
        self.write_stream(self.records)
        self.assertEqual(validate_coverage(self.stream, self.roots),
                         {'roots': 1, 'declarations': 1, 'expressions': 1})
        self.write_stream(self.records[:-1])
        with self.assertRaisesRegex(ValueError, 'omits selected roots'):
            validate_coverage(self.stream, self.roots)
        self.write_stream([*self.records, self.records[-1]])
        with self.assertRaisesRegex(ValueError, 'duplicate emitted declaration'):
            validate_coverage(self.stream, self.roots)

    def test_wrong_owner_phase_and_scanned_identity_cannot_match_independent_roots(self):
        for field in ('scanned_module', 'owner', 'name', 'phase'):
            candidate = json.loads(json.dumps(self.roots))
            candidate['roots'][0][field] = 'wrong'
            with self.subTest(field=field), self.assertRaisesRegex(ValueError, 'inventory differs'):
                validate_roots(candidate, self.roots)
        candidate = dict(self.roots, roots=[])
        with self.assertRaises(ValueError):
            validate_roots(candidate, self.roots)

    def test_saved_bytes_roots_and_coverage_must_all_agree(self):
        self.write_stream(self.records)
        for name in ('roots.json', 'expected-roots.json'):
            atomic_json(self.folder / name, self.roots)
        binding = {'fixture': 'only a cache validator unit control'}
        files = {name: {'sha256': digest(self.folder / name), 'bytes': (self.folder / name).stat().st_size}
                 for name in ('stream.ndjson', 'roots.json', 'expected-roots.json')}
        receipt = {'schema': 2, 'binding': binding, 'files': files,
                   'coverage': validate_coverage(self.stream, self.roots)}
        marker = self.folder / 'complete.json'
        atomic_json(marker, receipt)
        self.assertEqual(reload_group(self.folder, binding), receipt)
        self.stream.write_bytes(self.stream.read_bytes()[:-1])
        with self.assertRaisesRegex(ValueError, 'corrupt completed'):
            reload_group(self.folder, binding)
        self.write_stream(self.records)
        receipt['coverage']['roots'] = 2
        atomic_json(marker, receipt)
        with self.assertRaisesRegex(ValueError, 'inconsistent cached root coverage'):
            reload_group(self.folder, binding)
        marker.unlink()
        self.assertIsNone(reload_group(self.folder, binding))

    def test_root_preparation_reuses_exact_inputs_and_invalidates_private_changes(self):
        context, search = self.prepared_context()
        with mock.patch('scripts.nanoda.export_cache.authoritative_roots', return_value=self.roots) as select:
            first, expected, hit = prepare_roots(['Fixture'], context, self.folder, search)
            self.assertFalse(hit)
            self.assertEqual(expected, self.roots)
            self.assertEqual(prepare_roots(['Fixture'], context, self.folder, search), (first, expected, True))
            select.assert_called_once()
            private = search[0] / 'Fixture.olean.private'
            private.write_text('changed private fixture')
            with self.assertRaisesRegex(ValueError, 'compiled input changed'):
                prepare_roots(['Fixture'], context, self.folder, search)
            context['files'][str(private)] = digest(private)
            second, _, hit = prepare_roots(['Fixture'], context, self.folder, search)
            self.assertFalse(hit)
            self.assertNotEqual(first, second)
            self.assertEqual(select.call_count, 2)

    def test_root_preparation_rejects_corruption_and_inconsistent_coverage(self):
        context, search = self.prepared_context()
        with mock.patch('scripts.nanoda.export_cache.authoritative_roots', return_value=self.roots):
            folder, _, _ = prepare_roots(['Fixture'], context, self.folder, search)
        inventory, marker = folder / 'roots.json', folder / 'complete.json'
        original = inventory.read_bytes()
        inventory.write_bytes(original[:-1])
        with self.assertRaisesRegex(ValueError, 'corrupt prepared root inventory'):
            prepare_roots(['Fixture'], context, self.folder, search)
        inventory.write_bytes(original)
        receipt = json.loads(marker.read_text())
        receipt['roots'] += 1
        atomic_json(marker, receipt)
        with self.assertRaisesRegex(ValueError, 'inconsistent prepared root coverage'):
            prepare_roots(['Fixture'], context, self.folder, search)

    def test_root_preparation_policy_and_selected_inventory_are_bound(self):
        context, search = self.prepared_context()
        with mock.patch('scripts.nanoda.export_cache.authoritative_roots', return_value=self.roots) as select:
            with mock.patch('scripts.nanoda.export_cache.root_validation_policy', return_value={'reader': 'first'}):
                first, _, _ = prepare_roots(['Fixture'], context, self.folder, search)
            with mock.patch('scripts.nanoda.export_cache.root_validation_policy', return_value={'reader': 'second'}):
                second, _, hit = prepare_roots(['Fixture'], context, self.folder, search)
            self.assertFalse(hit)
            self.assertNotEqual(first, second)
            self.assertEqual(select.call_count, 2)
        with self.assertRaisesRegex(ValueError, 'exact selected module inventory'):
            prepare_roots(['Other'], context, self.folder, search)

    def test_failed_export_retains_independent_preparation_for_retry(self):
        context, search = self.prepared_context()
        binary = self.folder / 'producer'
        binary.write_text('cache-protocol fixture only')
        with mock.patch('scripts.nanoda.export_cache.authoritative_roots', return_value=self.roots) as select:
            with mock.patch('scripts.nanoda.export_cache.subprocess.run', side_effect=RuntimeError('interrupted export')):
                with self.assertRaisesRegex(RuntimeError, 'interrupted export'):
                    export_group(['Fixture'], context, binary, self.folder, search, 'fixture')
            _, expected, hit = prepare_roots(['Fixture'], context, self.folder, search)
            self.assertTrue(hit)
            self.assertEqual(expected, self.roots)
            select.assert_called_once()
        self.assertEqual(list(self.folder.glob('*/complete.json')), [])

    def test_failed_preparation_and_mid_read_artifact_change_do_not_publish_receipts(self):
        context, search = self.prepared_context()
        with mock.patch('scripts.nanoda.export_cache.authoritative_roots', side_effect=RuntimeError('interrupted selection')):
            with self.assertRaisesRegex(RuntimeError, 'interrupted selection'):
                prepare_roots(['Fixture'], context, self.folder, search)
        self.assertEqual(list(self.folder.glob('root-inventories/*/complete.json')), [])
        def replace_private(*_args):
            (search[0] / 'Fixture.olean.private').write_text('changed during selection')
            return self.roots
        with mock.patch('scripts.nanoda.export_cache.authoritative_roots', side_effect=replace_private):
            with self.assertRaisesRegex(ValueError, 'compiled input changed'):
                prepare_roots(['Fixture'], context, self.folder, search)
        self.assertEqual(list(self.folder.glob('root-inventories/*/complete.json')), [])

    def test_coverage_interruption_reuses_native_output_and_keeps_cache_bytes_independent(self):
        context, search = self.prepared_context()
        binary = self.folder / 'producer'
        binary.write_text('cache-protocol fixture only')
        encoded = ''.join(json.dumps(row) + '\n' for row in self.records).encode()
        def produce(command, stdout):
            stdout.write(encoded)
            Path(command[-1]).write_text(json.dumps(self.roots))
            return subprocess.CompletedProcess(command, 0)
        with mock.patch('scripts.nanoda.export_cache.authoritative_roots', return_value=self.roots):
            with mock.patch('scripts.nanoda.export_cache.subprocess.run', side_effect=produce) as execute:
                with mock.patch('scripts.nanoda.export_cache.validate_coverage', side_effect=RuntimeError('interrupted coverage')):
                    with self.assertRaisesRegex(RuntimeError, 'interrupted coverage'):
                        export_group(['Fixture'], context, binary, self.folder, search, 'fixture')
                native, _, _, hit = prepare_native(['Fixture'], context, binary, self.folder, search, 'fixture')
                self.assertTrue(hit)
                group, _, _ = export_group(['Fixture'], context, binary, self.folder, search, 'fixture')
                (group / 'complete.json').unlink()
                (group / 'stream.ndjson').write_bytes(b'interrupted group')
                self.assertEqual((native / 'stream.ndjson').read_bytes(), encoded)
                export_group(['Fixture'], context, binary, self.folder, search, 'fixture')
                self.assertEqual((group / 'stream.ndjson').read_bytes(), encoded)
                execute.assert_called_once()

    def test_failed_native_exit_is_retained_and_never_accepted(self):
        context, search = self.prepared_context()
        binary = self.folder / 'producer'
        binary.write_text('cache-protocol fixture only')
        with mock.patch('scripts.nanoda.export_cache.authoritative_roots', return_value=self.roots):
            with mock.patch('scripts.nanoda.export_cache.subprocess.run', return_value=subprocess.CompletedProcess([], 7)):
                with self.assertRaises(subprocess.CalledProcessError):
                    prepare_native(['Fixture'], context, binary, self.folder, search, 'fixture')
        self.assertEqual(list(self.folder.glob('native-outputs/*/complete.json')), [])
        exits = list(self.folder.glob('native-outputs/*/pending-*/exit.json'))
        self.assertEqual(len(exits), 1)
        self.assertEqual(json.loads(exits[0].read_text())['raw_exit_code'], 7)


if __name__ == '__main__':
    unittest.main()
