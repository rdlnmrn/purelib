"""Check compatible graph sharing and scanned-owner isolation."""

from pathlib import Path
import copy
import json
import tempfile
import unittest

from scripts.nanoda.planning import group_inputs, plan, retained_inputs, reusable_inputs
from scripts.nanoda.artifact_inputs import identity


class PlanningTests(unittest.TestCase):
    """Keep standalone names distinct and retain complete dependency input bindings."""

    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        (self.root / 'lakefile.toml').write_text(
            '[[lean_exe]]\nname="first"\nroot="scripts.First"\n'
            '[[lean_exe]]\nname="second"\nroot="scripts.Second"\n')
        imports = {'Init': [], 'Math.A': ['Init'], 'Math.B': ['Math.A'],
                   'scripts.First': ['Math.A'], 'scripts.Second': ['Math.B'],
                   'Math.Client': ['scripts.First']}
        self.modules = ['Math.A', 'scripts.First', 'Math.B', 'scripts.Second', 'Math.Client']
        nodes = [{'name': name, 'imports': values, 'files': [str(self.root / f'{name}.olean')]}
                 for name, values in imports.items()]
        self.context = {'schema': 2, 'selected_modules': self.modules,
                        'inventory': {'schema': 1, 'roots': self.modules, 'modules': nodes},
                        'files': {node['files'][0]: node['name'] for node in nodes}}

    def test_one_ordinary_graph_and_each_standalone_consumer_separate(self):
        self.assertEqual(plan(self.modules, self.context, self.root),
                         [['Math.A', 'Math.B'], ['scripts.First'], ['scripts.Second'], ['Math.Client']])

    def test_group_inputs_retain_only_complete_import_closure(self):
        group = group_inputs(self.context, ['scripts.First'])
        self.assertEqual({node['name'] for node in group['inventory']['modules']},
                         {'Init', 'Math.A', 'scripts.First'})
        self.assertEqual(set(group['files'].values()), {'Init', 'Math.A', 'scripts.First'})
        self.assertEqual(group['selected_modules'], ['scripts.First'])

    def test_invalid_inventories_and_missing_private_bindings_fail(self):
        with self.assertRaises(ValueError):
            plan([], self.context, self.root)
        with self.assertRaises(ValueError):
            plan(['Math.A'], self.context, self.root)
        self.context['inventory']['modules'][1]['imports'].append('Missing')
        with self.assertRaisesRegex(ValueError, 'missing compiled import inventory'):
            plan(self.modules, self.context, self.root)
        with self.assertRaisesRegex(ValueError, 'missing compiled group dependency'):
            group_inputs(self.context, ['Math.A'])

    def test_modern_group_requires_its_private_server_and_ir_parts(self):
        node = self.context['inventory']['modules'][1]
        node['files'].extend([node['files'][0] + '.server', node['files'][0] + '.private'])
        with self.assertRaisesRegex(ValueError, 'omits emitted artifacts'):
            group_inputs(self.context, ['Math.A'])

    def test_group_inventory_is_independent_of_unrelated_global_node_order(self):
        first = group_inputs(self.context, ['scripts.First'])
        self.context['inventory']['modules'].reverse()
        self.assertEqual(group_inputs(self.context, ['scripts.First']), first)

    def test_checked_adoption_preserves_old_protocol_and_rejects_changed_inputs(self):
        incoming = group_inputs(self.context, ['scripts.First'])
        old = copy.deepcopy(incoming)
        old['inventory']['modules'].reverse()
        directory = self.root / 'inputs'
        directory.mkdir()
        receipt = directory / (identity(old) + '.json')
        receipt.write_text(json.dumps(old))
        retained = retained_inputs(directory)
        self.assertEqual(reusable_inputs(incoming, retained), old)
        for field in ('files', 'imports', 'roots'):
            changed = copy.deepcopy(incoming)
            if field == 'files': changed['files'][next(iter(changed['files']))] = 'changed private artifact'
            if field == 'imports': changed['inventory']['modules'][0]['imports'].append('Other')
            if field == 'roots':
                changed['selected_modules'].reverse()
                changed['inventory']['roots'] = ['Other']
            self.assertEqual(reusable_inputs(changed, retained), changed)
        receipt.write_text(json.dumps(incoming))
        with self.assertRaisesRegex(ValueError, 'corrupt compiled input receipt'):
            retained_inputs(directory)


if __name__ == '__main__':
    unittest.main()
