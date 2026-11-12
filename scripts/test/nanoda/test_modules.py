"""Check real shared-graph scheduling, exact ownership and complete module coverage."""

import json
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest import mock

from scripts.nanoda.check_stream import check, module_results
from scripts.nanoda.module_owners import name_key, prepare
from scripts.paths import ROOT
from scripts.test.nanoda.test_compare_exports import write_stream


class ModuleChecks(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.checker = Path(subprocess.check_output(
            ['bash', str(ROOT / 'scripts/build-nanoda-module-checker.sh')], text=True).strip())

    def test_structural_names_distinguish_quoted_dots_and_numerals(self):
        self.assertNotEqual(name_key(((1, 'a.b'),)), name_key(((1, 'a'), (1, 'b'))))
        self.assertNotEqual(name_key(((1, '1'),)), name_key(((2, 1),)))
        self.assertEqual(name_key(((1, 'é'), (2, 7))), 'sc3a9;n7;')

    def test_missing_repeated_slow_and_incomplete_module_timings_fail(self):
        for report in ('', 'nanoda module\tA\t30000000\t1\n',
                       'nanoda module\tA\t1\t1\nnanoda module\tA\t1\t1\n',
                       'nanoda module\tA\t1\t2\n'):
            with self.subTest(report=report), self.assertRaises(ValueError):
                module_results(report, 1)

    def test_compiled_owner_receipt_reuses_only_unchanged_inputs_and_bytes(self):
        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary)
            library = folder / 'lib'
            library.mkdir()
            compiled = library / 'Fixture.olean'
            compiled.write_text('bound cache-protocol fixture; not a valid Lean artifact')
            from scripts.nanoda.artifact_inputs import digest
            context = {'selected_modules': ['Fixture'], 'inventory': {'modules': [
                {'name': 'Fixture', 'files': [str(compiled)]}]}, 'files': {str(compiled): digest(compiled)}}
            name = 42, ((1, 'actual.name'),)
            observation = mock.Mock(by_name={name: object()}, owners={name: 'Original.Owner'})
            with mock.patch('scripts.nanoda.module_owners.AuditObservation', return_value=observation) as reader:
                output = prepare(context, folder, [library])
                self.assertEqual(output.read_text(), 'Original.Owner\ts61637475616c2e6e616d65;\n')
                self.assertEqual(prepare(context, folder, [library]), output)
                reader.assert_called_once()
                original = output.read_bytes()
                output.write_text('damaged')
                with self.assertRaisesRegex(ValueError, 'ownership receipt'):
                    prepare(context, folder, [library])
                output.write_bytes(original)
                compiled.write_text('changed compiled fixture')
                with self.assertRaisesRegex(ValueError, 'compiled input changed'):
                    prepare(context, folder, [library])

    def test_real_shared_graph_checks_distinct_actual_owners(self):
        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary)
            source, owners, config = (folder / name for name in ('source.ndjson', 'owners.tsv', 'config.json'))
            write_stream(source, name='first')
            records = [json.loads(line) for line in source.read_text().splitlines()]
            records += [{'in': 2, 'str': {'pre': 0, 'str': 'second'}},
                        {'def': dict(records[-1]['def'], name=2, all=[2])}]
            source.write_text(''.join(json.dumps(record) + '\n' for record in records))
            settings = json.loads((ROOT / 'scripts/nanoda/config.json').read_text())
            settings['num_threads'] = 2
            config.write_text(json.dumps(settings))
            owners.write_text('Original.One\t' + name_key(((1, 'first'),)) + '\n' +
                              'Original.Two\t' + name_key(((1, 'second'),)) + '\n')
            checked, _ = check(source, self.checker, config, folder / 'checked', 2, owners=owners)
            self.assertEqual({owner: row['declarations'] for owner, row in checked['modules'].items()},
                             {'Original.One': 1, 'Original.Two': 1})

    def test_real_checker_checks_each_owner_once_and_binds_map_on_reload(self):
        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary)
            source, owners, config = (folder / name for name in ('source.ndjson', 'owners.tsv', 'config.json'))
            write_stream(source, name='a.b')
            settings = json.loads((ROOT / 'scripts/nanoda/config.json').read_text())
            settings['num_threads'] = 2
            config.write_text(json.dumps(settings))
            owners.write_text('ActualOwner\t' + name_key(((1, 'a.b'),)) + '\n')
            checked, retained = check(source, self.checker, config, folder / 'checked', 1, owners=owners)
            self.assertFalse(retained)
            self.assertEqual(checked['modules']['ActualOwner']['declarations'], 1)
            self.assertEqual(check(source, self.checker, config, folder / 'checked', 1, owners=owners),
                             (checked, True))
            owners.write_text('IncorrectOwner\t' + name_key(((1, 'a'), (1, 'b'))) + '\n')
            with self.assertRaisesRegex(RuntimeError, 'no compiled owner'):
                check(source, self.checker, config, folder / 'checked', 1, owners=owners)
            failed = list((folder / 'checked').glob('nanoda-check-*'))
            self.assertEqual(len(failed), 1)
            self.assertNotEqual(json.loads((failed[0] / 'exit.json').read_text())['raw_exit_code'], 0)

    def test_real_checker_rejects_invalid_kernel_body(self):
        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary)
            source, owners, config = (folder / name for name in ('source.ndjson', 'owners.tsv', 'config.json'))
            write_stream(source, value=1)
            settings = json.loads((ROOT / 'scripts/nanoda/config.json').read_text())
            settings['num_threads'] = 2
            config.write_text(json.dumps(settings))
            owners.write_text('Fixture\t' + name_key(((1, 'Fixture'),)) + '\n')
            with self.assertRaises(RuntimeError):
                check(source, self.checker, config, folder / 'checked', 1, owners=owners)
            self.assertEqual(list((folder / 'checked').glob('*.json')), [])
