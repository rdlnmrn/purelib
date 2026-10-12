"""Reject producer root omissions, duplicate declarations and damaged cache records."""

import json
from pathlib import Path
import tempfile
import unittest

from scripts.nanoda.artifact_inputs import digest
from scripts.nanoda.export_cache import atomic_json, reload_group, validate_coverage
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


if __name__ == '__main__':
    unittest.main()
