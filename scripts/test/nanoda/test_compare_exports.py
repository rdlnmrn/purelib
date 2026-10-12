"""Ensure exporter comparisons retain complete bodies and declaration metadata."""

import json
from pathlib import Path
import tempfile
import unittest

from scripts.nanoda.compare_exports import compare


def write_stream(path, *, name_id=1, expression_id=0, level_id=1, value=None, hints='opaque',
                 extra=None, name='Fixture'):
    """Write a small complete definition with configurable stream identifiers."""
    records = [{'in': name_id, 'str': {'pre': 0, 'str': name}},
               {'il': level_id, 'succ': 0},
               {'ie': expression_id, 'sort': 0},
               {'ie': expression_id + 1, 'sort': level_id}]
    definition = {'name': name_id, 'levelParams': [], 'type': expression_id + 1,
                  'value': expression_id if value is None else value,
                  'hints': hints, 'safety': 'safe', 'all': [name_id]}
    definition.update(extra or {})
    records.append({'def': definition})
    path.write_text(''.join(json.dumps(record) + '\n' for record in records))


class ComparisonTests(unittest.TestCase):
    """Exercise differences hidden by name-only or compact statement comparisons."""

    def test_independently_numbered_complete_streams_agree(self):
        with tempfile.TemporaryDirectory() as temporary:
            a, b = (Path(temporary) / name for name in ('a.ndjson', 'b.ndjson'))
            write_stream(a)
            write_stream(b, name_id=9, expression_id=40, level_id=80)
            self.assertEqual(compare([a], [b]), 1)

    def test_changed_body_opacity_safety_and_all_are_detected(self):
        with tempfile.TemporaryDirectory() as temporary:
            a, b = (Path(temporary) / name for name in ('a.ndjson', 'b.ndjson'))
            write_stream(a)
            cases = [dict(value=1), dict(hints={'regular': 2}),
                     dict(extra={'safety': 'partial'}), dict(extra={'all': []}),
                     dict(extra={'additionalMetadata': True})]
            for case in cases:
                with self.subTest(case=case):
                    write_stream(b, **case)
                    with self.assertRaisesRegex(ValueError, 'complete declaration records differ'):
                        compare([a], [b])

    def test_universe_and_coverage_changes_are_detected(self):
        with tempfile.TemporaryDirectory() as temporary:
            a, b = (Path(temporary) / name for name in ('a.ndjson', 'b.ndjson'))
            write_stream(a)
            write_stream(b, name='Different')
            with self.assertRaisesRegex(ValueError, 'coverage differs'):
                compare([a], [b])
            write_stream(b)
            records = [json.loads(line) for line in b.read_text().splitlines()]
            records.insert(2, {'il': 2, 'succ': 1})
            records[-2]['sort'] = 2
            b.write_text(''.join(json.dumps(record) + '\n' for record in records))
            with self.assertRaisesRegex(ValueError, 'complete declaration records differ'):
                compare([a], [b])

    def test_repetition_requires_exact_records_and_missing_references_fail(self):
        with tempfile.TemporaryDirectory() as temporary:
            a, b = (Path(temporary) / name for name in ('a.ndjson', 'b.ndjson'))
            write_stream(a)
            write_stream(b, value=1)
            with self.assertRaisesRegex(ValueError, 'inconsistent repeated declaration'):
                compare([a, b], [a])
            write_stream(b, value=99)
            with self.assertRaises(KeyError):
                compare([a], [b])


if __name__ == '__main__':
    unittest.main()
