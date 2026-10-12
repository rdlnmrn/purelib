"""Bind complete compiled inputs without executing target code or extensions."""

import hashlib
import json
from pathlib import Path

from scripts.lean_module_data.compact import inventory
from scripts.lean_module_data.paths import find_olean


def digest(path):
    """Hash retained bytes while detecting replacement during the read."""
    path = Path(path)
    before = path.stat()
    with path.open('rb') as source:
        value = hashlib.file_digest(source, 'sha256').hexdigest()
    after = path.stat()
    signature = lambda s: (s.st_dev, s.st_ino, s.st_size, s.st_mtime_ns, s.st_ctime_ns)
    if signature(before) != signature(after):
        raise ValueError(f'compiled input changed while hashing: {path}')
    return value


def identity(value):
    """Bind structured protocol data with deterministic JSON encoding."""
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def compiled_inputs(modules, search):
    """Read pinned headers and hash private, server, public and required IR parts."""
    if not modules or len(set(modules)) != len(modules):
        raise ValueError('empty or duplicate selected modules')
    data, pins = inventory(modules, search)
    files = {str(Path(pin['path']).resolve()): pin['sha256'] for pin in pins}
    for module in data['modules']:
        resolved = find_olean(module['name'], search).resolve()
        if resolved != Path(module['files'][0]).resolve():
            raise ValueError(f'compiled module resolution changed: {module["name"]}')
        if len(module['files']) == 3:
            ir = resolved.with_suffix('.ir')
            if not ir.is_file():
                raise ValueError(f'missing private import IR data: {module["name"]}: {ir}')
            files[str(ir)] = digest(ir)
    return {'schema': 2, 'selected_modules': modules, 'inventory': data, 'files': files}


def verify_inputs(context, search):
    """Fail if any retained bytes or module resolution changed after preflight."""
    for node in context['inventory']['modules']:
        if find_olean(node['name'], search).resolve() != Path(node['files'][0]).resolve():
            raise ValueError(f'compiled module resolution changed: {node["name"]}')
    for path, expected in context['files'].items():
        if digest(path) != expected:
            raise ValueError(f'compiled input changed: {path}')
