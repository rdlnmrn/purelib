#!/usr/bin/env python3
"""Check host-reader contracts without invoking a Lean reader or build.

Compiler artifact comparisons use immutable installed toolchain parts. The current kernel replay controls compile isolated fixtures.
"""
import hashlib
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
from scripts.lean_module_data.compact import InvalidArtifact, Region, inventory
from scripts.lean_module_data.contracts import capture, dumps
from scripts.lean_module_data.paths import find_olean, parse_name, render_name, search_path


class HostPathTests(unittest.TestCase):
    def test_literal_names_and_deep_components(self):
        value = 'Root.«embedded.dot».γ.x' + '.tail' * 2048
        parsed = parse_name(value)
        self.assertEqual(render_name(parsed), value)
        self.assertEqual(parsed[1], (1, 'embedded.dot'))
        self.assertEqual(parse_name('Root.123'), ((1, 'Root'), (2, 123)))
        for value in ('', 'Root.', '.Root', 'Root..Child', 'Root.«missing', 'Root.bad-name'):
            self.assertEqual(parse_name(value), ())

    def test_package_root_is_selected_before_descendant(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary); first = root / 'first'; second = root / 'second'
            (first / 'Root').mkdir(parents=True); (second / 'Root').mkdir(parents=True)
            (second / 'Root/Child.olean').write_bytes(b'other artifact')
            self.assertEqual(find_olean('Root.Child', [first, second]), first / 'Root/Child.olean')
            with self.assertRaises(FileNotFoundError): Region(find_olean('Root.Child', [first, second]))
            self.assertEqual(find_olean('Root.«embedded.dot»', [first]), first / 'Root/embedded.dot.olean')
            with self.assertRaisesRegex(InvalidArtifact, 'numeric module'):
                find_olean('Root.123', [first])

    def test_sysroot_and_search_order(self):
        with patch.dict(os.environ, {'LEAN_PATH': '/first:/second', 'LEAN_SYSROOT': '/pinned'}, clear=True), \
             patch('subprocess.run', side_effect=AssertionError('no compiler query needed')):
            self.assertEqual(search_path(), [Path('/first'), Path('/second'), Path('/pinned/lib/lean')])

    def test_empty_search_entries_retain_current_directory(self):
        with patch.dict(os.environ, {'LEAN_PATH': ':/first::', 'LEAN_SYSROOT': '/pinned'}, clear=True):
            self.assertEqual(search_path(), [Path('.'), Path('/first'), Path('.'),
                                             Path('.'), Path('/pinned/lib/lean')])

    def test_empty_inventory_rejected(self):
        with self.assertRaisesRegex(InvalidArtifact, 'no roots'): inventory([], [])


class HostRecordTests(unittest.TestCase):
    def setUp(self):
        self.root = next((path for path in search_path() if (path / 'Lean/Expr.olean').is_file()), None)
        if self.root is None: self.fail('pinned Lean.Expr artifact unavailable')

    def test_missing_private_part_cannot_fall_back(self):
        with tempfile.TemporaryDirectory() as temporary:
            target = Path(temporary) / 'Expr.olean'
            target.write_bytes((self.root / 'Lean/Expr.olean').read_bytes())
            with self.assertRaises(FileNotFoundError): capture('Lean.Expr', target)

    def test_exact_header_and_saved_pointer_validation(self):
        source = (self.root / 'Lean/Expr.olean').read_bytes()
        with tempfile.TemporaryDirectory() as temporary:
            target = Path(temporary) / 'bad.olean'
            for label, offset, value in [('version', 5, 3), ('GMP', 6, 0), ('revision', 40, 0)]:
                with self.subTest(label=label):
                    data = bytearray(source); data[offset] = value; target.write_bytes(data)
                    with self.assertRaises(InvalidArtifact): Region(target)

    def test_complete_records_and_module_metadata(self):
        schema, private, public = capture('Lean.Expr', self.root / 'Lean/Expr.olean')
        records = list(schema.records('Lean.Expr', private, public))
        self.assertEqual(records[0]['declaration_count'], len(records) - 1)
        self.assertTrue(all(row['module_system'] for row in records))
        self.assertEqual(len({row['declaration']['name'] for row in records[1:]}), len(records) - 1)
        self.assertTrue(any(row['declaration']['private'] for row in records[1:]))
        self.assertTrue(any(row['declaration']['exported'] and row['declaration']['exposed']
                            for row in records[1:]))

    def test_json_original_control_escape_and_large_natural(self):
        value = {'tab': '\t', 'nul': '\x00', 'nat': 1 << 16384}
        encoded = dumps(value)
        self.assertIn('\\u0009', encoded); self.assertIn('\\u0000', encoded)
        def decimal(text):
            result = 0
            for char in text: result = result * 10 + ord(char) - 48
            return result
        self.assertEqual(json.loads(encoded, parse_int=decimal), value)


class HostNameObservationTests(unittest.TestCase):
    def test_hash_and_private_header_observe_pinned_names(self):
        from scripts.lean_module_data.observations import name_hash, name_observer, is_private_name
        from scripts.lean_module_data.render import Renderer
        root = next(path for path in search_path() if (path / 'Lean/Expr.olean').is_file())
        schema, private, public = capture('Lean.Expr', root / 'Lean/Expr.olean')
        d = schema.d; renderer = Renderer(d)
        count = 0; private_header = None
        for i, node in enumerate(d.nodes):
            if node['kind'] != 'Name': continue
            components = tuple(renderer.components(i))
            self.assertEqual(name_observer(d, i)[0], name_hash(components))
            count += 1
            if components == ((1, '_private'),): private_header = i
        self.assertGreater(count, 100)
        self.assertIsNotNone(private_header)
        self.assertTrue(is_private_name(d, private_header))
        original = d.nodes[private_header]['scalars']
        try:
            d.nodes[private_header]['scalars'] = (int.from_bytes(original, 'little') ^ 1).to_bytes(8, 'little')
            self.assertFalse(is_private_name(d, private_header))
        finally:
            d.nodes[private_header]['scalars'] = original

    def test_name_order_is_not_lexical_string_order(self):
        from scripts.lean_module_data.observations import query_observer, name_cmp, quick_cmp
        self.assertLess(name_cmp(query_observer('Z.1'), query_observer('A.x')), 0)
        a, b = (3, ((1,'root'), (1,'last'))), (3, ((1,'other'), (1,'last')))
        self.assertGreater(quick_cmp(a,b),0)
        self.assertLess(name_cmp(query_observer('A'),query_observer('A.child')),0)


if __name__ == '__main__': unittest.main()
