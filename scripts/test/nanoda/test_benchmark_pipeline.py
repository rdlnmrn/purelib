"""Check benchmark ancestry accounting and stream-local identifier resolution."""

import json
from pathlib import Path
import tempfile
import unittest

from scripts.nanoda.benchmark_pipeline import descendants, stream_inventory


class BenchmarkTests(unittest.TestCase):
    """Exercise observations that determine the reported performance comparison."""

    def test_detached_descendants_remain_owned_but_reused_pids_do_not(self):
        known = {}
        table = {10: {'parent': 1, 'started': 100}, 11: {'parent': 10, 'started': 110},
                 12: {'parent': 11, 'started': 120}, 99: {'parent': 1, 'started': 990}}
        self.assertEqual(descendants(table, 10, known), {10, 11, 12})
        table.pop(10)
        table[11]['parent'] = 1
        self.assertEqual(descendants(table, 10, known), {11, 12})
        table[11]['started'] = 111
        table[12]['parent'] = 1
        self.assertEqual(descendants(table, 10, known), {12})

    def test_counts_mutual_groups_with_stream_local_and_numeric_names(self):
        with tempfile.TemporaryDirectory() as temporary:
            cache = Path(temporary)
            streams = cache / 'nanoda-native'
            streams.mkdir()
            records = [
                {'in': 1, 'str': {'pre': 0, 'str': 'T'}},
                {'in': 2, 'num': {'pre': 1, 'i': 3}},
                {'in': 3, 'str': {'pre': 1, 'str': 'rec'}},
                {'inductive': {'types': [{'name': 1}], 'ctors': [{'name': 2}], 'recs': [{'name': 3}]}},
            ]
            (streams / 'first').mkdir()
            (streams / 'second').mkdir()
            (streams / 'first/stream.ndjson').write_text(''.join(json.dumps(r) + '\n' for r in records))
            (streams / 'second/stream.ndjson').write_text(
                json.dumps({'in': 1, 'str': {'pre': 0, 'str': 'other'}}) + '\n' +
                json.dumps({'in': 2, 'str': {'pre': 0, 'str': 'T'}}) + '\n' +
                json.dumps({'def': {'name': 1}}) + '\n' + json.dumps({'thm': {'name': 2}}) + '\n')
            result = stream_inventory(cache)
            self.assertEqual(result['declaration_occurrences'], 5)
            self.assertEqual(result['distinct_declaration_names'], 4)
            self.assertEqual(result['repeated_declaration_names'], 1)
            self.assertEqual(result['total_bytes'], sum(p.stat().st_size for p in streams.glob('*/stream.ndjson')))

    def test_empty_or_unresolved_stream_is_not_a_measurement(self):
        with tempfile.TemporaryDirectory() as temporary:
            cache = Path(temporary)
            with self.assertRaisesRegex(ValueError, 'no streams'):
                stream_inventory(cache)
            streams = cache / 'nanoda-native'
            streams.mkdir()
            (streams / 'bad').mkdir()
            (streams / 'bad/stream.ndjson').write_text(json.dumps({'def': {'name': 1}}) + '\n')
            with self.assertRaises(KeyError):
                stream_inventory(cache)


if __name__ == '__main__':
    unittest.main()
