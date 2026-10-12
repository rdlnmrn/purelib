#!/usr/bin/env python3
"""Regressions for public import reachability and checked plan lineage."""
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from scripts.module_style import core as style

from scripts.module_style import public_imports


class PublicImportsTests(unittest.TestCase):
    def test_triangle(self):
        graph = {'A': {'B', 'C'}, 'B': {'C'}, 'C': set()}
        reduced, witnesses = public_imports.reduce_graph(graph, {'A', 'B', 'C'})
        self.assertEqual(reduced['A'], {'B'})
        self.assertEqual(witnesses, {'A': {'C': ['A', 'B', 'C']}})

    def test_diamond_simultaneous_reduction(self):
        graph = {'A': {'B', 'C', 'D', 'E'}, 'B': {'D', 'E'}, 'C': {'D'}, 'D': {'E'}, 'E': set()}
        reduced, witnesses = public_imports.reduce_graph(graph, set(graph))
        self.assertEqual(reduced['A'], {'B', 'C'})
        self.assertEqual(reduced['B'], {'D'})
        self.assertEqual(witnesses['A']['E'], ['A', 'B', 'D', 'E'])
        self.assertEqual(public_imports.reachable(graph), public_imports.reachable(reduced))
        for node, removed in witnesses.items():
            for target, route in removed.items():
                self.assertEqual((route[0], route[-1]), (node, target))
                self.assertTrue(all(b in reduced[a] for a, b in zip(route, route[1:])))

    def test_disconnected_and_unselected_nodes(self):
        graph = {'A': {'B', 'C'}, 'B': {'C'}, 'C': set(), 'D': {'E', 'F'}, 'E': {'F'}, 'F': set()}
        reduced, witnesses = public_imports.reduce_graph(graph, {'A'})
        self.assertEqual(reduced['D'], graph['D'])
        self.assertEqual(set(witnesses), {'A'})
        self.assertEqual(public_imports.reduce_graph(reduced, set(graph))[0]['A'], {'B'})

    def test_phases_and_import_all_never_witness(self):
        source = 'module\npublic import B\npublic meta import C\npublic import all D\nmeta import E\nimport F\n'
        rows = public_imports.header_imports(source)
        self.assertEqual(rows, [('public import', 'B'), ('public meta import', 'C'),
                                ('public import all', 'D'), ('meta import', 'E'), ('import', 'F')])
        graph = {'A': {owner for mode, owner in rows if mode == 'public import'},
                 'B': set(), 'C': {'B'}, 'D': {'B'}}
        reduced, witnesses = public_imports.reduce_graph(graph, {'A'})
        self.assertEqual(reduced['A'], {'B'})
        self.assertFalse(witnesses)

    def test_comments_strings_and_body_are_not_imports(self):
        source = '''module
/- outer /- public import Wrong -/ nested -/
public import B -- real
/-- Documentation mentioning public import Wrong. -/
def exampleText := "public import Wrong"
public import NotInHeader
'''
        self.assertEqual(public_imports.header_imports(source), [('public import', 'B')])

    def test_cycle_rejected(self):
        with self.assertRaisesRegex(ValueError, 'cycle'):
            public_imports.reduce_graph({'A': {'B'}, 'B': {'A'}}, {'A'})

    def test_applied_and_pending_lineage(self):
        original = 'module\npublic import A\npublic import B\n'
        plan, current = style.prepare(dict(schema=1, path='Test/Fixture.lean',
            source_sha256=style.digest(original), imports=[dict(module=x, mode='public import', reason='API') for x in ['A', 'B']],
            opens=[], rewrites=[], docstrings={}, review='Test checked original lineage.'), original)
        with tempfile.TemporaryDirectory() as directory:
            history = Path(directory)
            recovered, result, prior = public_imports.reviewed_state(plan, current, history)
            self.assertEqual((recovered, result), (original, current))
            public_imports.immutable_json(history / 'Test/Fixture' / (style.digest(current) + '.json'), prior)
            changed = dict(plan, imports=[dict(module='A', mode='public import', reason='API'),
                                          dict(module='B', mode='import', reason='Retained public route through A.')])
            changed, after = style.prepare(changed, original)
            recovered, result, retained = public_imports.reviewed_state(changed, current, history)
            self.assertEqual((recovered, result, retained), (original, after, prior))
            self.assertEqual(public_imports.reviewed_state(changed, current, history), (original, after, prior))
            self.assertEqual(public_imports.reviewed_state(changed, after, history)[:2], (original, after))
            with self.assertRaisesRegex(ValueError, 'no checked prior'):
                public_imports.reviewed_state(changed, current + '\n', history)

    def test_changed_source_withholds_application_manifest(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / 'Source.lean'
            source.write_text('module\n')
            run = root / 'run'
            public_imports.immutable_json(run / 'plans' / 'Source.json', {'staged': True})
            evidence = dict(sources={str(source): {'source_sha256': style.digest(source.read_text())}},
                            inputs={}, tool_sha256=style.digest(Path(public_imports.__file__).read_text()))
            source.write_text('module\nimport Other\n')
            with self.assertRaisesRegex(ValueError, 'source changed during preparation'):
                public_imports.publish_checked(run, evidence, [])
            self.assertTrue((run / 'plans' / 'Source.json').exists())
            self.assertFalse((run / 'graph.json').exists())
            self.assertFalse((run / 'manifest.json').exists())

    def test_changed_plan_withholds_manifest_and_matching_inputs_reuse(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            plan = root / 'Plan.json'
            plan.write_text('{}\n')
            original = plan.read_text()
            evidence = dict(sources={}, inputs={str(plan): style.digest(original)},
                            tool_sha256=style.digest(Path(public_imports.__file__).read_text()))
            plan.write_text('{"changed": true}\n')
            run = root / 'run'
            with self.assertRaisesRegex(ValueError, 'review input changed during preparation'):
                public_imports.publish_checked(run, evidence, [])
            self.assertFalse((run / 'manifest.json').exists())
            plan.write_text(original)
            public_imports.publish_checked(run, evidence, [])
            first = (run / 'manifest.json').read_bytes()
            public_imports.publish_checked(run, evidence, [])
            self.assertEqual(first, (run / 'manifest.json').read_bytes())

    def test_immutable_prior_cannot_be_overwritten(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'prior.json'
            public_imports.immutable_json(path, {'old': 1})
            public_imports.immutable_json(path, {'old': 1})
            with self.assertRaisesRegex(ValueError, 'conflicting immutable'):
                public_imports.immutable_json(path, {'old': 2})

    def test_competing_immutable_publisher_cannot_be_overwritten(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'prior.json'
            link = public_imports.os.link
            winner = style.encoded({'winner': True})
            def compete(source, destination):
                path.write_text(winner)
                link(source, destination)
            with patch.object(public_imports.os, 'link', side_effect=compete):
                with self.assertRaisesRegex(ValueError, 'conflicting immutable'):
                    public_imports.immutable_json(path, {'loser': True})
            self.assertEqual(path.read_text(), winner)
            self.assertEqual(list(path.parent.iterdir()), [path])

    def test_json_digest_binds_parsed_bytes_and_rejects_duplicates(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'plan.json'
            text = '{"version": 1}\n'
            path.write_text(text)
            inputs = {}
            read = Path.read_text
            def change_after_read(file, *args, **kwargs):
                result = read(file, *args, **kwargs)
                if file == path:
                    file.write_text('{"version": 2}\n')
                return result
            with patch.object(Path, 'read_text', change_after_read):
                self.assertEqual(public_imports.checked_json(path, inputs), {'version': 1})
            self.assertEqual(inputs[str(path)], style.digest(text))
            self.assertNotEqual(inputs[str(path)], style.digest(path.read_text()))
            path.write_text('{"version": 1, "version": 2}')
            with self.assertRaisesRegex(ValueError, 'duplicate JSON key'):
                public_imports.checked_json(path, {})

    def test_selected_source_change_between_review_and_graph_is_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / '.lake/packages').mkdir(parents=True)
            (root / 'scripts').mkdir()
            (root / 'scripts/run-lake.sh').write_text('fixture')
            (root / 'lean-toolchain').write_text('fixture')
            (root / 'Test').mkdir()
            source = root / 'Test/Fixture.lean'
            original = 'module\npublic import A\n'
            plan, current = style.prepare(dict(schema=1, path='Test/Fixture.lean',
                source_sha256=style.digest(original),
                imports=[dict(module='A', mode='public import', reason='API')],
                opens=[], rewrites=[], docstrings={}, review='Original source race fixture.'), original)
            source.write_text(current)
            plan_file = root / 'plan.json'
            plan_file.write_text(style.encoded(plan))
            manifest = root / 'manifest.json'
            manifest.write_text(style.encoded({'files': [dict(path='Test/Fixture.lean',
                module='Test.Fixture', classification='authored')]}))
            read = Path.read_text
            count = 0
            def change_second_read(file, *args, **kwargs):
                nonlocal count
                if file == source:
                    count += 1
                    if count == 2:
                        file.write_text(current + '\n')
                return read(file, *args, **kwargs)
            with patch.object(public_imports, 'ROOT', root), patch.object(style, 'ROOT', root), \
                 patch.object(style, 'source_path', return_value=source), \
                 patch.object(public_imports.subprocess, 'check_output', return_value=str(root)), \
                 patch.object(Path, 'read_text', change_second_read):
                with self.assertRaisesRegex(ValueError, 'source changed during preparation'):
                    public_imports.main(['--manifest', str(manifest), '--plan', str(plan_file),
                                         '--output', str(root / 'output')])
            self.assertFalse((root / 'output').exists())


if __name__ == '__main__':
    unittest.main()
