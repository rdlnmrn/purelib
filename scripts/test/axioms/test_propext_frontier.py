#!/usr/bin/env python3
"""Check provider ordering, atomic grouping, and complete audit edge handling."""
import json
from pathlib import Path
import tempfile
import unittest

from scripts.axioms import propext_frontier as frontier


class FrontierTests(unittest.TestCase):
    def test_empty_worker_preserves_other_roots_and_dirty_edges(self):
        with tempfile.TemporaryDirectory() as temp:
            empty = Path(temp) / 'empty.jsonl'
            empty.write_text('\n')
            populated = Path(temp) / 'populated.jsonl'
            rows = [
                dict(kind='root', name='clean', owner='Purelib.Fixture',
                     canonical=False, axioms=[]),
                dict(kind='root', name='contaminated', owner='Purelib.Fixture',
                     canonical=False, axioms=['propext']),
                dict(kind='dirty', name='contaminated', owner='Purelib.Fixture',
                     dependencies=['propext'], external=['propext']),
            ]
            populated.write_text('\n'.join(map(json.dumps, rows)) + '\n')
            roots, dirty = frontier.audit_records([empty, populated])
            self.assertEqual(set(roots), {('Purelib.Fixture', 'clean'), ('Purelib.Fixture', 'contaminated')})
            self.assertEqual(set(dirty), {'contaminated'})
            self.assertEqual(dirty['contaminated']['dependencies'], ['propext'])

    def test_same_basename_retains_each_scanned_module(self):
        with tempfile.TemporaryDirectory() as temp:
            path = Path(temp) / 'closures.jsonl'
            rows = [dict(kind='root', name='main', owner='scripts.First',
                         scanned_module='scripts.First', canonical=False, axioms=[]),
                    dict(kind='root', name='main', owner='scripts.Second',
                         scanned_module='scripts.Second', canonical=False, axioms=['propext']),
                    dict(kind='dirty', name='main', owner='scripts.Second',
                         dependencies=['propext'], external=['propext'])]
            path.write_text('\n'.join(map(json.dumps, rows)))
            roots, _ = frontier.audit_records([path])
            self.assertEqual(len(roots), 2)
            self.assertEqual(roots[('scripts.First', 'main')]['axioms'], [])
            self.assertEqual(roots[('scripts.Second', 'main')]['axioms'], ['propext'])

    def test_conflicting_same_record_is_rejected(self):
        with tempfile.TemporaryDirectory() as temp:
            path = Path(temp) / 'closures.jsonl'
            clean = dict(kind='root', name='main', owner='scripts.First',
                         scanned_module='scripts.First', canonical=False, axioms=[])
            path.write_text(json.dumps(clean) + '\n' +
                            json.dumps(dict(clean, axioms=['propext'])))
            with self.assertRaisesRegex(ValueError, 'inconsistent audit roots'):
                frontier.audit_records([path])

    def test_nonempty_malformed_report_is_rejected(self):
        with tempfile.TemporaryDirectory() as temp:
            path = Path(temp) / 'malformed.jsonl'
            path.write_text('{\n')
            with self.assertRaises(json.JSONDecodeError):
                frontier.audit_records([path])

    def test_layers_keep_atomic_members_and_all_dirty_routes(self):
        def row(name, dependencies, external=()):
            return dict(name=name, owner='Purelib.Fixture', dependencies=list(dependencies), external=list(external))
        dirty = {
            'foundation': row('foundation', ['propext'], ['propext']),
            'inductive': row('inductive', ['foundation']),
            'constructor': row('constructor', []),
            'consumer': row('consumer', ['inductive', 'other']),
            'other': row('other', ['external'], ['external']),
        }
        result = frontier.schedule(dirty, {'inductive': ['constructor'], 'constructor': ['inductive']})
        groups = {r['name']: r for r in result}
        self.assertEqual(groups['foundation']['layer'], 0)
        self.assertEqual(groups['constructor']['members'], ['constructor', 'inductive'])
        self.assertEqual(groups['constructor']['layer'], 1)
        self.assertEqual(groups['consumer']['layer'], 2)
        self.assertEqual(groups['consumer']['providers'], ['constructor', 'other'])
        self.assertEqual(groups['other']['status'], 'ready')

    def test_missing_dirty_prerequisite_cannot_be_accepted(self):
        with tempfile.TemporaryDirectory() as temp:
            path = Path(temp) / 'closures.jsonl'
            path.write_text(json.dumps(dict(kind='dirty', name='consumer', owner='Purelib.Fixture',
                                            dependencies=['missing'], external=[])) + '\n')
            with self.assertRaisesRegex(ValueError, 'missing dirty project prerequisite'):
                frontier.audit_records([path])

    def test_lazy_equation_variants_retain_both_actual_paths(self):
        with tempfile.TemporaryDirectory() as temp:
            paths = []
            for index, helper in enumerate(['left', 'right']):
                path = Path(temp) / str(index)
                rows = [dict(kind='dirty', name='equation', owner=f'Purelib.Consumer{index}',
                             dependencies=[helper], external=[]),
                        dict(kind='dirty', name=helper, owner='Purelib.Fixture',
                             dependencies=['propext'], external=['propext'])]
                path.write_text('\n'.join(map(json.dumps, rows)))
                paths.append(path)
            _, dirty = frontier.audit_records(paths)
            self.assertEqual(dirty['equation']['dependencies'], ['left', 'right'])
            self.assertEqual(len(dirty['equation']['variants']), 2)


if __name__ == '__main__':
    unittest.main()
