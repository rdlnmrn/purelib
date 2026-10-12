#!/usr/bin/env python3
"""Private, commit-pinned import-inventory prototype; no Lean process or pointer dereference."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import struct

PIN = b'f3b06c705e6c85f5314019d5d3baab0fec5b580c'
VERSION = b'4.32.2'

class InvalidArtifact(ValueError):
    pass

class Region:
    def __init__(self, path):
        self.path = Path(path)
        with self.path.open('rb') as f:
            before = os.fstat(f.fileno())
            self.data = f.read()
            after = os.fstat(f.fileno())
        if (before.st_dev, before.st_ino, before.st_size, before.st_mtime_ns) != (
                after.st_dev, after.st_ino, after.st_size, after.st_mtime_ns):
            raise InvalidArtifact(f'changed while reading: {path}')
        if len(self.data) < 96 or self.data[:7] != b'olean\x02\x01':
            raise InvalidArtifact(f'not pinned v2/GMP ModuleData: {path}')
        if self.data[7:40] != VERSION.ljust(33, b'\0') or self.data[40:80] != PIN:
            raise InvalidArtifact(f'compiler revision mismatch: {path}')
        self.base = self.u64(80)
        if self.base % 65536 or len(self.data) > (1 << 64) - self.base:
            raise InvalidArtifact(f'invalid region bounds: {path}')
        self.root = self.u64(88)
        self.sha256 = hashlib.sha256(self.data).hexdigest()

    def bytes(self, off, size):
        if off < 0 or size < 0 or off > len(self.data) - size:
            raise InvalidArtifact(f'out-of-bounds bytes in {self.path}: {off}+{size}')
        return self.data[off:off+size]

    def u64(self, off):
        return struct.unpack('<Q', self.bytes(off, 8))[0]

class ModuleParts:
    def __init__(self):
        self.regions = []
        self.names = {}
        self.active_names = set()

    def add(self, path):
        region = Region(path)
        for old in self.regions:
            if region.base < old.base + len(old.data) and old.base < region.base + len(region.data):
                raise InvalidArtifact('overlapping saved region addresses')
        self.regions.append(region)
        return region

    def locate(self, ptr):
        if ptr & 1 or ptr % 8:
            raise InvalidArtifact(f'expected aligned object pointer: {ptr:#x}')
        for region in self.regions:
            off = ptr - region.base
            if 96 <= off <= len(region.data) - 8:
                return region, off
        raise InvalidArtifact(f'unresolved saved pointer: {ptr:#x}')

    def ctor(self, ptr, tag, count, scalar_size):
        region, off = self.locate(ptr)
        rc, size, fields, actual_tag = struct.unpack('<IHBB', region.bytes(off, 8))
        expected_size = (8 + 8 * count + scalar_size + 7) // 8 * 8
        if rc != 0 or size != expected_size or fields != count or tag != actual_tag:
            raise InvalidArtifact(f'wrong constructor shape at {region.path}:{off}')
        region.bytes(off, size)
        fields = tuple(region.u64(off + 8 + i * 8) for i in range(count))
        return region, off + 8 + count * 8, fields

    def array(self, ptr):
        region, off = self.locate(ptr)
        if region.bytes(off, 8) != b'\0\0\0\0\x01\0\0\xf6':
            raise InvalidArtifact('wrong array object header')
        size, capacity = region.u64(off+8), region.u64(off+16)
        if capacity != size:
            raise InvalidArtifact('compacted array capacity mismatch')
        region.bytes(off+24, size*8)
        return tuple(region.u64(off+24+i*8) for i in range(size))

    def string(self, ptr):
        region, off = self.locate(ptr)
        if region.bytes(off, 8) != b'\0\0\0\0\x01\0\0\xf9':
            raise InvalidArtifact('wrong string object header')
        size, capacity, length = (region.u64(off+i) for i in (8,16,24))
        if not size or capacity != size:
            raise InvalidArtifact('compacted string size/capacity mismatch')
        raw = region.bytes(off+32, size)
        if raw[-1:] != b'\0' or b'\0' in raw[:-1]:
            raise InvalidArtifact('invalid import-name string terminator')
        text = raw[:-1].decode('utf-8', errors='strict')
        if len(text) != length:
            raise InvalidArtifact('string UTF-8 length mismatch')
        return text

    def name(self, ptr):
        """Read finite prefix components iteratively, retaining each stored hash."""
        if ptr == 1: return ((), 1723)
        pending = []; active = set(); current = ptr
        while current != 1 and current not in self.names:
            if current in active: raise InvalidArtifact('cyclic import name')
            active.add(current)
            region, scalars, fields = self.ctor(current, 1, 2, 8)
            pending.append((current, self.string(fields[1]), region.u64(scalars)))
            current = fields[0]
        prefix, _ = self.names[current] if current != 1 else ((), 1723)
        for key, text, stored_hash in reversed(pending):
            prefix = prefix + ((1, text),)
            self.names[key] = prefix, stored_hash
        return self.names[ptr]

    def projection(self, region):
        region, scalar, fields = self.ctor(region.root, 0, 5, 1)
        is_module = region.bytes(scalar, 1)[0]
        if is_module not in (0, 1):
            raise InvalidArtifact('invalid ModuleData.isModule')
        imports = []
        for ptr in self.array(fields[0]):
            owner, scalar, imp_fields = self.ctor(ptr, 0, 1, 3)
            flags = owner.bytes(scalar, 3)
            if any(flag not in (0, 1) for flag in flags):
                raise InvalidArtifact('invalid import flags')
            components, hash_value = self.name(imp_fields[0])
            if not components:
                raise InvalidArtifact('anonymous module import')
            imports.append((components, hash_value, tuple(flags)))
        return bool(is_module), imports

def inventory(roots, search_path):
    if not roots:
        raise InvalidArtifact('axiom input inventory has no roots')
    from .paths import find_olean, parse_name, render_name
    queue = [(name, parse_name(name)) for name in roots]
    seen = set()
    records = []
    pins = []
    index = 0
    while index < len(queue):
        module, module_components = queue[index]
        index += 1
        if module_components in seen:
            continue
        seen.add(module_components)
        path = find_olean(module_components, search_path)
        parts = ModuleParts()
        first = parts.add(path)
        is_module, imports = parts.projection(first)
        paths = [path]
        if is_module:
            for suffix in ('.server', '.private'):
                part_path = Path(str(path)+suffix)
                part = parts.add(part_path)
                part_is_module, part_imports = parts.projection(part)
                if not part_is_module:
                    raise InvalidArtifact('modern/legacy part disagreement')
                paths.append(part_path)
                imports.extend(part_imports)
        dependencies = {}
        for components, hash_value, _ in imports:
            old = dependencies.setdefault(components, hash_value)
            if old != hash_value:
                raise InvalidArtifact('inconsistent computed name hash')
        ordered = sorted(dependencies, key=lambda n: (dependencies[n], tuple(reversed(n))))
        names = [render_name(n) for n in ordered]
        queue.extend(zip(names, ordered))
        records.append({'name':render_name(module_components), 'imports':names, 'files':[str(p) for p in paths]})
        pins.extend({'path':str(r.path),'sha256':r.sha256,'size':len(r.data)} for r in parts.regions)
    return {'schema':1,'roots':[render_name(parse_name(name)) for name in roots],'modules':records}, pins
