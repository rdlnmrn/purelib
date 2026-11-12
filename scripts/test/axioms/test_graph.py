"""Immutable-view protocol controls; synthetic graphs establish no Lean proof pass."""
import hashlib
import fcntl
import mmap
import os
from pathlib import Path
import tempfile
from types import SimpleNamespace
import unittest
from scripts.lean_module_data import audit_graph
from scripts.lean_module_data.observations import Observations, name_hash, query_observer

class Shape(Observations):
    """A finite dependency shape for ordering, sharing and sentinel comparisons."""

    def __init__(self):
        self.labels = {label: query_observer(label) for label in ('Group.left', 'Group.right', 'Group.alias', 'Axiom.x', 'Axiom.y', 'Cached.empty', 'Cached.axes')}
        self.big = ((1, 'Group'), (1, 'γ\x00name'), (2, 1 << 20000))
        big = (name_hash(self.big), self.big)
        self.labels['large'] = big
        n = self.labels
        self.by_name = {name: SimpleNamespace(name=name, kind=0 if label.startswith('Axiom.') or label == 'large' else 1) for label, name in n.items()}
        self.owners = {name: 'Original.Owner' for name in n.values()}
        self.edges = {n['Group.left']: [n['Group.right'], n['Axiom.x']], n['Group.right']: [n['Group.left'], n['Axiom.y']], n['Group.alias']: [n['Group.right'], n['Axiom.x']]}
        self.cached = {n['Cached.empty']: [], n['Cached.axes']: [n['Axiom.y'], n['Axiom.x']]}

    def persisted_axioms(self, name):
        return self.cached.get(name)

    def axiom_dependencies(self, ref):
        return self.edges.get(ref.name, [])

class ImmutableGraphTests(unittest.TestCase):

    def test_read_only_buffers_preserve_names_owners_cycles_and_cached_order(self):
        obs = Shape()
        queries = list(obs.by_name)
        with tempfile.TemporaryDirectory() as temporary:
            binding, names, roots = audit_graph.build(obs, queries)
            graph = audit_graph.Graph(binding)
            try:
                self.assertEqual([[names[i] for i in graph.axioms(root)] for root in roots], [obs.axioms(name) for name in queries])
                self.assertEqual([graph.name(i) for i in range(len(names))], names)
                self.assertTrue(all((graph.owner(i) == 'Original.Owner' for i in range(len(names)))))
                with self.assertRaises(TypeError):
                    graph.data[graph.blob] = 0
                ids = {name: i for i, name in enumerate(names)}
                left = graph.node(ids[obs.labels['Group.left']])
                alias = graph.node(ids[obs.labels['Group.alias']])
                self.assertEqual(left[3:5], alias[3:5])
                right = graph.node(ids[obs.labels['Group.right']])
                parent = lambda row: audit_graph.PREFIX.unpack_from(graph.data, graph.prefixes + row[1] * audit_graph.PREFIX.size)[0]
                self.assertEqual(parent(left), parent(right))
                with self.assertRaises(PermissionError):
                    os.write(binding[0], b'bad')
                with self.assertRaises(PermissionError):
                    os.ftruncate(binding[0], 0)
                graph.verify()
            finally:
                graph.close()
                os.close(binding[0])

    def test_checksum_layout_prefix_cycles_and_invalid_edges_are_rejected(self):
        obs = Shape()
        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary)
            binding, _, _ = audit_graph.build(obs, list(obs.by_name))
            with mmap.mmap(binding[0], 0, access=mmap.ACCESS_READ) as data:
                original = bytes(data)

            def changed(mutator):
                data = bytearray(original)
                mutator(data)
                descriptor = os.memfd_create('bad-audit-view', os.MFD_CLOEXEC | os.MFD_ALLOW_SEALING)
                with os.fdopen(os.dup(descriptor), 'wb') as output:
                    output.write(data)
                fcntl.fcntl(descriptor, audit_graph.ADD_SEALS, audit_graph.SEALS)
                digest = hashlib.sha256(data).hexdigest()
                return (descriptor, digest)
            header = audit_graph.HEADER.unpack_from(original)
            controls = [lambda data: data.__setitem__(0, 0), lambda data: audit_graph.U32.pack_into(data, header[2] + audit_graph.PREFIX.size, 1), lambda data: audit_graph.U32.pack_into(data, header[4], header[1])]
            for mutate in controls:
                damaged = changed(mutate)
                try:
                    with self.subTest(mutate=mutate), self.assertRaises(ValueError):
                        audit_graph.Graph(damaged)
                finally:
                    os.close(damaged[0])
            invalid = (binding[0], '0' * 64)
            with self.assertRaisesRegex(ValueError, 'checksum'):
                audit_graph.Graph(invalid)
            os.close(binding[0])
