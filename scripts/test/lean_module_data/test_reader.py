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
import struct
from unittest.mock import patch
from scripts.lean_module_data.compact import InvalidArtifact, Region, inventory
from scripts.lean_module_data.contracts import capture, dumps
from scripts.lean_module_data.paths import find_olean, parse_name, render_name, search_path


class BoundedRegionTests(unittest.TestCase):
    """Synthetic header bytes exercise storage, not mathematical validity."""

    def fixture(self, path, size=4096):
        from scripts.lean_module_data.compact import PIN, VERSION
        data = (b'olean\x02\x01' + VERSION.ljust(33, b'\0') + PIN +
                struct.pack('<QQ', 65536, 65632))
        data += bytes(i % 251 for i in range(size - len(data)))
        path.write_bytes(data)
        return data

    def test_bounded_eviction_retains_exact_slices_and_original_hash(self):
        from scripts.lean_module_data import compact
        with tempfile.TemporaryDirectory() as temporary, \
                patch.object(compact, 'PAGE_BYTES', 128), \
                patch.object(compact, 'PAGE_CACHE_BYTES', 256), \
                patch.object(compact, '_pages', compact.OrderedDict()), \
                patch.object(compact, '_page_bytes', 0):
            path = Path(temporary) / 'fixture.olean'
            expected = self.fixture(path)
            region = Region(path)
            self.assertNotIsInstance(region.data, bytes)
            self.assertEqual(region.sha256, hashlib.sha256(expected).hexdigest())
            for start in range(97, len(expected) - 180, 113):
                self.assertEqual(region.bytes(start, 180), expected[start:start + 180])
                self.assertLessEqual(compact._page_bytes, 256)
            self.assertEqual(region.data[-1], expected[-1])
            self.assertEqual(region.data[::-71], expected[::-71])
            with self.assertRaises(InvalidArtifact): region.bytes(-1, 1)
            with self.assertRaises(InvalidArtifact): region.bytes(len(expected), 1)

    def test_evicted_page_cannot_be_replaced_by_changed_or_missing_bytes(self):
        from scripts.lean_module_data import compact
        for change in ('replace', 'truncate', 'remove'):
            with self.subTest(change=change), tempfile.TemporaryDirectory() as temporary, \
                    patch.object(compact, 'PAGE_BYTES', 128), \
                    patch.object(compact, 'PAGE_CACHE_BYTES', 128), \
                    patch.object(compact, '_pages', compact.OrderedDict()), \
                    patch.object(compact, '_page_bytes', 0):
                path = Path(temporary) / 'fixture.olean'
                expected = self.fixture(path)
                region = Region(path)
                self.assertEqual(region.bytes(512, 8), expected[512:520])
                region.bytes(1024, 8)
                if change == 'remove': path.unlink()
                elif change == 'truncate': path.write_bytes(expected[:512])
                else:
                    replacement = path.with_suffix('.replacement')
                    replacement.write_bytes(expected)
                    replacement.replace(path)
                with self.assertRaises(InvalidArtifact): region.bytes(512, 8)

    def test_many_regions_fit_a_process_smaller_than_their_serialized_inputs(self):
        import subprocess
        import sys
        code = '''import json, resource, struct, tempfile
from pathlib import Path
from scripts.lean_module_data.compact import Region, VERSION, PIN
resource.setrlimit(resource.RLIMIT_AS, (96 * 1024**2, 96 * 1024**2))
header = b'olean\\x02\\x01' + VERSION.ljust(33,b'\\0') + PIN + struct.pack('<QQ',65536,65632)
with tempfile.TemporaryDirectory() as directory:
    regions = []
    for index in range(24):
        path = Path(directory) / str(index)
        with path.open('wb') as stream:
            stream.write(header)
            stream.truncate(8 * 1024**2)
        regions.append(Region(path))
    assert all(region.bytes(0,96) == header for region in regions)
    print(json.dumps({'regions':len(regions),'input_bytes':sum(len(r.data) for r in regions)}))
'''
        completed = subprocess.run([sys.executable, '-c', code], capture_output=True,
                                   text=True, timeout=30)
        self.assertEqual(completed.returncode, 0, completed.stderr)
        self.assertEqual(json.loads(completed.stdout), {'regions': 24, 'input_bytes': 192 * 1024**2})


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

    def test_graph_shares_decoded_nodes_without_changing_complete_records(self):
        from scripts.lean_module_data.contracts import Schema2
        from scripts.lean_module_data.importer import Module
        from scripts.lean_module_data.typed import TypedDecoder
        pool = TypedDecoder([])
        for name in ('Lean.Expr', 'Init.Data.Nat.Basic'):
            path = self.root.joinpath(*name.split('.')).with_suffix('.olean')
            expected_schema, private, public = capture(name, path)
            expected = list(expected_schema.records(name, private, public))
            first = Module(name, path, pool.eq_identities, pool.name_payloads, nodes=pool)
            def records(module):
                return list(Schema2(module.d).records(name, module.d.module(module.roots[-1]),
                                                     module.d.module(module.roots[0])))
            self.assertEqual(records(first), expected)
            count = len(pool.nodes)
            second = Module(name, path, pool.eq_identities, pool.name_payloads, nodes=pool)
            self.assertEqual(records(second), expected)
            self.assertEqual(len(pool.nodes), count)
            self.assertIs(first.d.nodes, second.d.nodes)
            self.assertIsNot(first.d.cache, second.d.cache)

    def test_shared_storage_preserves_scalar_bytes_ignored_by_expression_equality(self):
        from scripts.lean_module_data.typed import TypedDecoder
        # Descriptor-only storage control; this does not certify a kernel term.
        class Decoder(TypedDecoder):
            def descriptor(self, kind, ptr):
                if kind == 'Expr':
                    return 0, (('Nat', 1),), (17 + (ptr << 32)).to_bytes(8, 'little'), None
                return super().descriptor(kind, ptr)
        pool = TypedDecoder([])
        first, second = Decoder([], shared=pool), Decoder([], shared=pool)
        left, right = first.decode('Expr', 2), second.decode('Expr', 4)
        self.assertNotEqual(left, right)
        self.assertEqual(first.eq_ids[left], second.eq_ids[right])
        self.assertNotEqual(first.nodes[left]['scalars'], second.nodes[right]['scalars'])


class HostNameObservationTests(unittest.TestCase):
    def test_audit_projects_exact_ordered_edges_without_retaining_expressions(self):
        from scripts.lean_module_data.audit import AuditObservation
        from scripts.lean_module_data.importer import Module
        from scripts.lean_module_data.observations import Observations, name_observer
        root = next(path for path in search_path() if (path / 'Lean/Expr.olean').is_file())
        kinds = set()
        for module in ('Lean.Expr', 'Init.Prelude'):
            path = root.joinpath(*module.split('.')).with_suffix('.olean')
            original = Module(module, path, {}, {})
            projected = Module(module, path, {}, {})
            refs = [ref for _, ref, _ in projected.entries(True)]
            obs = AuditObservation.__new__(AuditObservation)
            obs.by_name = {name_observer(ref.d, ref.name): ref for ref in refs}
            obs.names = {ref.key: name for name, ref in obs.by_name.items()}
            obs.dependency_projections = {}
            retained = len(projected.d.nodes)
            for (_, expected, _), actual in zip(original.entries(True), refs, strict=True):
                kinds.add(actual.kind)
                self.assertEqual(obs.axiom_dependencies(actual),
                                 tuple(Observations.axiom_dependencies(obs, expected)))
                self.assertEqual(obs.used(actual), Observations.used(obs, expected))
                self.assertIs(obs.axiom_dependencies(actual), obs.axiom_dependencies(actual))
            self.assertEqual(len(projected.d.nodes), retained)
            self.assertGreater(len(original.d.nodes), retained)
        self.assertTrue({1, 2, 5, 6, 7} <= kinds, kinds)

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
