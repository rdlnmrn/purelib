"""Checked immutable dependency view with structurally shared name prefixes.

This transient view preserves the original resolved import environment. Readers
map its buffers read-only; mutable traversal state is local to each query.
"""
from collections import OrderedDict
import fcntl
import hashlib
import mmap
import os
import struct
from types import SimpleNamespace
from .compact import InvalidArtifact
from .observations import Observations, name_cmp
HEADER = struct.Struct('<8s6Q')
# Node: cached name hash, prefix, first owner, direct span, cached span, flags, reserved.
NODE = struct.Struct('<Q8I')
# Prefix: parent prefix, component tag, payload byte offset and length.
PREFIX = struct.Struct('<IB3xQI')
U32 = struct.Struct('<I')
MAGIC = b'AXDAG01\x00'
CACHED = 1
AXIOM = 2
REFERENCE = 4
# Linux UAPI values; some Python builds omit the fcntl names.
ADD_SEALS = getattr(fcntl, 'F_ADD_SEALS', 1033)
GET_SEALS = getattr(fcntl, 'F_GET_SEALS', 1034)
SEALS = 1 | 2 | 4 | 8

class Graph(Observations):
    """Read-only names, first owners, cached closures and ordered dependency edges."""

    def __init__(self, binding):
        descriptor, expected = binding
        self.fd = os.dup(descriptor)
        self.data = None
        try:
            if fcntl.fcntl(self.fd, GET_SEALS) & SEALS != SEALS:
                raise InvalidArtifact('audit graph is not sealed immutable data')
            self.data = mmap.mmap(self.fd, 0, access=mmap.ACCESS_READ)
            if hashlib.sha256(self.data).hexdigest() != expected:
                raise InvalidArtifact('immutable audit graph checksum changed')
            stat = os.fstat(self.fd)
            self.identity = (stat.st_dev, stat.st_ino, stat.st_size)
            self.by_name = self
            self.names_cache = OrderedDict()
            magic, self.count, prefixes, owners, edges, blob, self.edge_count = HEADER.unpack_from(self.data)
            if magic != MAGIC or prefixes != HEADER.size + self.count * NODE.size or (not prefixes <= owners <= edges <= blob <= len(self.data)) or (owners - prefixes) % PREFIX.size or (edges - owners) % 8 or (blob - edges != self.edge_count * 4):
                raise InvalidArtifact('invalid immutable audit graph layout')
            self.prefixes, self.owners, self.edges, self.blob = (prefixes, owners, edges, blob)
            self.prefix_count = (owners - prefixes) // PREFIX.size
            self.owner_count = (edges - owners) // 8
            for index in range(self.prefix_count):
                parent, tag, offset, size = PREFIX.unpack_from(self.data, prefixes + index * PREFIX.size)
                if index == 0 and (parent or tag or size) or (index > 0 and (parent >= index or tag not in (1, 2))) or offset + size > len(self.data) - blob:
                    raise InvalidArtifact('invalid shared name prefix')
                value = self.data[blob + offset:blob + offset + size]
                if tag == 1:
                    value.decode('utf8')
                elif tag == 2 and value and (value[-1] == 0):
                    raise InvalidArtifact('noncanonical shared name numeral')
            for index in range(self.owner_count):
                offset, size = struct.unpack_from('<II', self.data, owners + index * 8)
                if offset + size > len(self.data) - blob:
                    raise InvalidArtifact('invalid immutable module owner')
                self.data[blob + offset:blob + offset + size].decode('utf8')
            for index in range(self.count):
                _, prefix, owner, start, size, cached_start, cached_size, flags, reserved = self.node(index)
                if prefix >= self.prefix_count or owner >= self.owner_count or reserved or flags & ~7 or (start + size > self.edge_count) or (cached_start + cached_size > self.edge_count):
                    raise InvalidArtifact('invalid immutable declaration row')
            for index in range(self.edge_count):
                if U32.unpack_from(self.data, edges + index * 4)[0] >= self.count:
                    raise InvalidArtifact('invalid immutable dependency index')
            self.verify()
        except BaseException:
            if self.data is not None:
                self.data.close()
            os.close(self.fd)
            raise

    def verify(self):
        """Reject changes to a mapped view before accepting its observations."""
        stat = os.fstat(self.fd)
        if (stat.st_dev, stat.st_ino, stat.st_size) != self.identity or fcntl.fcntl(self.fd, GET_SEALS) & SEALS != SEALS:
            raise InvalidArtifact('immutable audit graph changed during checking')

    def close(self):
        """Release this reader's mapping."""
        self.data.close()
        os.close(self.fd)

    def node(self, index):
        """Read one bounded declaration record."""
        if not 0 <= index < self.count:
            raise InvalidArtifact('invalid immutable declaration index')
        return NODE.unpack_from(self.data, HEADER.size + index * NODE.size)

    def edge_list(self, start, size):
        """Read a retained ordered edge list."""
        return [U32.unpack_from(self.data, self.edges + (start + i) * 4)[0] for i in range(size)]

    def name(self, index):
        """Decode a name observation from its shared prefix chain."""
        if index not in self.names_cache:
            row = self.node(index)
            prefix = row[1]
            components = []
            while prefix:
                parent, tag, offset, size = PREFIX.unpack_from(self.data, self.prefixes + prefix * PREFIX.size)
                value = self.data[self.blob + offset:self.blob + offset + size]
                components.append((tag, value.decode('utf8') if tag == 1 else int.from_bytes(value, 'little')))
                prefix = parent
            self.names_cache[index] = (row[0], tuple(reversed(components)))
            if len(self.names_cache) > 1024:
                self.names_cache.popitem(last=False)
        self.names_cache.move_to_end(index)
        return self.names_cache[index]

    def owner(self, index):
        """Read the original resolved module owner, including absent ownership."""
        owner = self.node(index)[2]
        if owner == 0:
            return None
        offset, size = struct.unpack_from('<II', self.data, self.owners + owner * 8)
        if offset + size > len(self.data) - self.blob:
            raise InvalidArtifact('invalid immutable module owner')
        return self.data[self.blob + offset:self.blob + offset + size].decode('utf8')

    def get(self, index):
        """Supply the original collectAxioms branch discriminator."""
        flags = self.node(index)[7]
        return SimpleNamespace(index=index, kind=0 if flags & AXIOM else 1) if flags & REFERENCE else None

    def persisted_axioms(self, index):
        """Keep absent and present-empty imported entries distinct."""
        row = self.node(index)
        return self.edge_list(row[5], row[6]) if row[7] & CACHED else None

    def axiom_dependencies(self, ref):
        """Observe the original ordered direct dependencies."""
        row = self.node(ref.index)
        return self.edge_list(row[3], row[4])

    def axiom_name_cmp(self, left, right):
        """Apply the pinned name ordering to indexed observations."""
        return name_cmp(self.name(left), self.name(right))

def build(observation, queries):
    """Build and check a finite immutable view against the original observations.

    The caller owns the sealed descriptor in the returned binding and closes it
    after all readers exit. Names and root indices retain the original observations.
    """
    names = []
    indices = {}
    rows = []
    edges = []
    spans = {}

    def index(name):
        if name not in indices:
            indices[name] = len(names)
            names.append(name)
        return indices[name]
    roots = [index(name) for name in queries]

    def span(values):
        value = tuple((index(n) for n in values))
        if value not in spans:
            spans[value] = (len(edges), len(value))
            edges.extend(value)
        return spans[value]
    cursor = 0
    while cursor < len(names):
        name = names[cursor]
        cursor += 1
        cached = observation.persisted_axioms(name)
        ref = observation.by_name.get(name)
        deps = observation.axiom_dependencies(ref) if cached is None and ref is not None else ()
        start, size = span(deps)
        cached_start, cached_size = span(cached) if cached is not None else (0, 0)
        flags = (CACHED if cached is not None else 0) | (REFERENCE if ref is not None else 0) | (AXIOM if ref is not None and ref.kind == 0 else 0)
        rows.append((start, size, cached_start, cached_size, flags))
    blob = bytearray()
    payloads = {}
    prefixes = [(0, 0, 0, 0)]
    prefix_ids = {}
    owners = [(0, 0)]
    owner_ids = {None: 0}
    nodes = []

    def payload(value):
        if value not in payloads:
            payloads[value] = (len(blob), len(value))
            blob.extend(value)
        return payloads[value]
    for name, row in zip(names, rows, strict=True):
        prefix = 0
        for tag, value in name[1]:
            key = (prefix, tag, value)
            if key not in prefix_ids:
                encoded = value.encode('utf8') if tag == 1 else value.to_bytes((value.bit_length() + 7) // 8, 'little')
                prefix_ids[key] = len(prefixes)
                prefixes.append((prefix, tag, *payload(encoded)))
            prefix = prefix_ids[key]
        owner = observation.owners.get(name)
        if owner not in owner_ids:
            owner_ids[owner] = len(owners)
            owners.append(payload(owner.encode('utf8')))
        nodes.append((name[0], prefix, owner_ids[owner], *row, 0))
    prefix_offset = HEADER.size + len(nodes) * NODE.size
    owner_offset = prefix_offset + len(prefixes) * PREFIX.size
    edge_offset = owner_offset + len(owners) * 8
    blob_offset = edge_offset + len(edges) * 4
    descriptor = os.memfd_create('purelib-axiom-graph', os.MFD_CLOEXEC | os.MFD_ALLOW_SEALING)
    try:
        with os.fdopen(os.dup(descriptor), 'wb') as output:
            output.write(HEADER.pack(MAGIC, len(nodes), prefix_offset, owner_offset, edge_offset, blob_offset, len(edges)))
            for row in nodes:
                output.write(NODE.pack(*row))
            for row in prefixes:
                output.write(PREFIX.pack(*row))
            for row in owners:
                output.write(struct.pack('<II', *row))
            for edge in edges:
                output.write(U32.pack(edge))
            output.write(blob)
        fcntl.fcntl(descriptor, ADD_SEALS, SEALS)
        with mmap.mmap(descriptor, 0, access=mmap.ACCESS_READ) as data:
            digest = hashlib.sha256(data).hexdigest()
        binding = (descriptor, digest)
        graph = Graph(binding)
        try:
            if graph.count != len(names):
                raise InvalidArtifact('immutable graph omitted declarations')
            for i, name in enumerate(names):
                if graph.name(i) != name or graph.owner(i) != observation.owners.get(name):
                    raise InvalidArtifact('immutable graph changed name or import ownership')
                cached = observation.persisted_axioms(name)
                actual = graph.persisted_axioms(i)
                if (None if actual is None else [names[n] for n in actual]) != cached:
                    raise InvalidArtifact('immutable graph changed a persisted axiom entry')
                ref = observation.by_name.get(name)
                row = graph.node(i)
                expected = observation.axiom_dependencies(ref) if cached is None and ref is not None else ()
                if [names[n] for n in graph.edge_list(row[3], row[4])] != list(expected):
                    raise InvalidArtifact('immutable graph changed direct dependency order')
                if bool(row[7] & REFERENCE) != (ref is not None) or bool(row[7] & AXIOM) != (ref is not None and ref.kind == 0):
                    raise InvalidArtifact('immutable graph changed a declaration kind')
            graph.verify()
        finally:
            graph.close()
        return (binding, names, roots)
    except BaseException:
        os.close(descriptor)
        raise
