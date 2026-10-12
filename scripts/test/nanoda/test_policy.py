#!/usr/bin/env python3
"""Exercise empty-axiom policy with the real pinned independent checker.

These minimal NDJSON fixtures exercise checker policy and kernel rejection;
they do not establish project export provenance or source coverage.
"""
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest


from scripts.paths import ROOT
CHECKER = Path(os.environ.get('NANODA_BIN',
    str(ROOT / '.external/nanoda/target/release/nanoda_bin')))
CONFIG = ROOT / 'scripts/nanoda/config.json'
from scripts.nanoda import check_stream as checked_stream


def stream(path, name='PolicyPositive', *, axiom=False, invalid=False):
    """Encode `def PolicyPositive : Type := Prop`, or an axiom with type Type."""
    records = [{'meta': {'exporter': {'name': 'lean4export', 'version': '3.1.0'},
                         'format': {'version': '3.1.0'},
                         'lean': {'githash': 'policy-fixture', 'version': '4.32.2'}}}]
    parent = 0
    for index, part in enumerate(name.split('.'), 1):
        records.append({'in': index, 'str': {'pre': parent, 'str': part}})
        parent = index
    records.extend([{'il': 1, 'succ': 0}, {'ie': 0, 'sort': 0}, {'ie': 1, 'sort': 1}])
    declaration = {'name': parent, 'levelParams': [], 'type': 1}
    if axiom:
        declaration['isUnsafe'] = False
    else:
        declaration.update(value=1 if invalid else 0, hints='opaque', safety='safe')
    records.append({'axiom' if axiom else 'def': declaration})
    path.write_text(''.join(json.dumps(record) + '\n' for record in records))


class PolicyTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        if not CHECKER.is_file() or not os.access(CHECKER, os.X_OK):
            raise RuntimeError('set NANODA_BIN to the built CI-pinned independent checker')

    def test_axiom_free_definition_and_exact_receipt_reuse(self):
        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary)
            source = folder / 'positive.ndjson'
            stream(source)
            result, hit = checked_stream.check(source, CHECKER, CONFIG, folder / 'cache')
            self.assertEqual(result['declarations'], 1)
            self.assertEqual(result['axioms'], [])
            self.assertFalse(hit)
            self.assertEqual(checked_stream.check(source, CHECKER, CONFIG, folder / 'cache'),
                             (result, True))

    def test_every_exported_axiom_is_a_hard_error(self):
        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary)
            source = folder / 'forbidden.ndjson'
            cache = folder / 'cache'
            for name in ['propext', 'Classical.choice', 'Quot.sound', 'sorryAx',
                         'Lean.ofReduceBool', 'OtherAxiom']:
                with self.subTest(name=name):
                    stream(source, name, axiom=True)
                    with self.assertRaisesRegex(RuntimeError, 'unpermitted axiom') as error:
                        checked_stream.check(source, CHECKER, CONFIG, cache)
                    self.assertIn(name, str(error.exception))
                    self.assertEqual(list(cache.glob('*.json')), [])

    def test_skipped_axiom_stream_cannot_report_accepted_success(self):
        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary)
            source = folder / 'skipped.ndjson'
            stream(source, 'propext', axiom=True)
            settings = json.loads(CONFIG.read_text())
            settings['unpermitted_axiom_hard_error'] = False
            config = folder / 'skip-config.json'
            config.write_text(json.dumps(settings))
            with source.open('rb') as data:
                process = subprocess.run([str(CHECKER), str(config)], stdin=data,
                                         stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
            self.assertIn('skipping exported', process.stdout)
            with self.assertRaises(ValueError):
                checked_stream.result(process.stdout)

    def test_invalid_definition_is_not_cached(self):
        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary)
            source = folder / 'invalid.ndjson'
            stream(source, invalid=True)
            with self.assertRaises(RuntimeError):
                checked_stream.check(source, CHECKER, CONFIG, folder / 'cache')
            self.assertEqual(list((folder / 'cache').glob('*.json')), [])


if __name__ == '__main__':
    unittest.main()
