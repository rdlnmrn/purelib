"""Require exact declaration counts and explicit independent empty-scope validation."""

import json
import os
from pathlib import Path
import tempfile
import unittest

from scripts.nanoda.check_stream import check, result


from scripts.paths import ROOT
CHECKER = Path(os.environ.get('NANODA_BIN', ROOT / '.external/nanoda/target/release/nanoda_bin'))
CONFIG = ROOT / 'scripts/nanoda/config.json'


class CheckStreamTests(unittest.TestCase):
    """A producer success marker cannot substitute for complete real checker success."""

    def test_wrong_counts_and_unbound_empty_reports_fail(self):
        with self.assertRaisesRegex(ValueError, 'expected 2'):
            result('Checked 1 declarations with no errors\n', 2)
        with self.assertRaisesRegex(ValueError, 'independently validated'):
            result('Checked 0 declarations with no errors\n')
        self.assertEqual(result('Checked 0 declarations with no errors\n', 0)['declarations'], 0)
        for report in ('Checked 1 declarations with no errors\naxiom propext\n',
                       'Checked 1 declarations with no errors\nskipping exported axiom\n',
                       'Checked 1 declarations with no errors\nChecked 1 declarations with no errors\n'):
            with self.assertRaises(ValueError):
                result(report, 1)

    def test_real_empty_stream_requires_bound_zero_and_retains_success(self):
        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary)
            source = folder / 'empty.ndjson'
            source.write_text(json.dumps({'meta': {'exporter': {'name': 'lean4export', 'version': '3.1.0'},
                                                  'format': {'version': '3.1.0'},
                                                  'lean': {'version': '4.32.2', 'githash': 'fixture'}}}) + '\n')
            with self.assertRaises(ValueError):
                check(source, CHECKER, CONFIG, folder / 'checked')
            self.assertEqual(list((folder / 'checked').glob('*.json')), [])
            checked, hit = check(source, CHECKER, CONFIG, folder / 'checked', 0)
            self.assertEqual(checked['declarations'], 0)
            self.assertFalse(hit)
            self.assertEqual(check(source, CHECKER, CONFIG, folder / 'checked', 0), (checked, True))
            with self.assertRaises(ValueError):
                check(source, CHECKER, CONFIG, folder / 'checked', 1)


if __name__ == '__main__':
    unittest.main()
