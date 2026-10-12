"""Publish and reload complete native streams under exact compiled input bindings."""

import fcntl
import json
import os
from pathlib import Path
import subprocess
import tempfile

from scripts.lean_module_data.paths import render_name
from .artifact_inputs import digest, identity, verify_inputs
from .root_inventory import authoritative_roots, validate_roots


from scripts.paths import ROOT


def validation_policy():
    """Bind the independent root reader and complete export validation implementation."""
    files = [Path(__file__), Path(__file__).with_name('artifact_inputs.py'),
             Path(__file__).with_name('root_inventory.py'),
             *sorted((ROOT / 'scripts/lean_module_data').glob('*.py'))]
    return {str(path.relative_to(ROOT)): digest(path) for path in files}


def atomic_json(path, value):
    """Commit protocol data only after its complete bytes have been written."""
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(mode='w', dir=path.parent, delete=False) as pending:
        json.dump(value, pending, sort_keys=True)
        pending.write('\n')
        pending.flush()
        os.fsync(pending.fileno())
    os.replace(pending.name, path)


def declaration_inventory(path):
    """Resolve stream-local names and reject repeated or missing root declarations."""
    names, declared, expressions = {0: ()}, set(), 0
    with Path(path).open() as source:
        for line in source:
            record = json.loads(line)
            if 'in' in record:
                tag = 'str' if 'str' in record else 'num'
                data = record[tag]
                number = record['in']
                if number in names:
                    raise ValueError(f'duplicate stream name identifier: {number}')
                component = (1, data['str']) if tag == 'str' else (2, data['i'])
                names[number] = (*names[data['pre']], component)
            elif 'ie' in record:
                expressions += 1
            elif 'inductive' in record:
                values = [item for tag in ('types', 'ctors', 'recs') for item in record['inductive'][tag]]
                for item in values:
                    name = render_name(names[item['name']])
                    if name in declared:
                        raise ValueError(f'duplicate emitted declaration: {name}')
                    declared.add(name)
            else:
                for tag in ('axiom', 'def', 'thm', 'opaque', 'quot'):
                    if tag in record:
                        name = render_name(names[record[tag]['name']])
                        if name in declared:
                            raise ValueError(f'duplicate emitted declaration: {name}')
                        declared.add(name)
    return declared, expressions


def validate_coverage(path, roots):
    """Require every independently selected root to appear in the actual stream."""
    declarations, expressions = declaration_inventory(path)
    missing = {row['name'] for row in roots['roots']} - declarations
    if missing:
        raise ValueError(f'native stream omits selected roots: {sorted(missing)}')
    return {'declarations': len(declarations), 'expressions': expressions,
            'roots': len(roots['roots'])}


def reload_group(directory, binding):
    """Validate every completed artifact before accepting a saved export."""
    directory = Path(directory)
    marker = directory / 'complete.json'
    if not marker.exists():
        return None
    receipt = json.loads(marker.read_text())
    if receipt.get('schema') != 2 or receipt.get('binding') != binding:
        raise ValueError(f'corrupt native export binding: {marker}')
    for name in ('stream.ndjson', 'roots.json', 'expected-roots.json'):
        path = directory / name
        if path.stat().st_size != receipt['files'][name]['bytes'] or digest(path) != receipt['files'][name]['sha256']:
            raise ValueError(f'corrupt completed native export: {path}')
    roots = json.loads((directory / 'roots.json').read_text())
    expected = json.loads((directory / 'expected-roots.json').read_text())
    validate_roots(roots, expected)
    if receipt['coverage']['roots'] != len(expected['roots']):
        raise ValueError(f'inconsistent cached root coverage: {marker}')
    return receipt


def export_group(modules, context, binary, directory, search, policy):
    """Reuse one complete compatible stream, or produce and validate it atomically."""
    directory = Path(directory)
    binding = {'modules': modules, 'compiled_inputs': context, 'producer_sha256': digest(binary),
               'policy': policy, 'validation': validation_policy(),
               'root_predicate': 'authoritative-safe-source-and-global-csimp-v1'}
    key = identity(binding)
    folder = directory / key
    folder.mkdir(parents=True, exist_ok=True)
    with (folder / 'export.lock').open('w') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        verify_inputs(context, search)
        cached = reload_group(folder, binding)
        if cached is not None:
            return folder, cached, True
        expected = authoritative_roots(modules, search)
        with tempfile.TemporaryDirectory(prefix='pending-', dir=folder) as temporary:
            pending = Path(temporary)
            manifest = pending / 'modules.txt'
            manifest.write_text('\n'.join(modules) + '\n')
            stream = pending / 'stream.ndjson'
            roots_path = pending / 'roots.json'
            with stream.open('wb') as output:
                subprocess.run([str(binary), '--export', str(manifest), str(roots_path)],
                               stdout=output, check=True)
            roots = json.loads(roots_path.read_text())
            validate_roots(roots, expected)
            metrics = validate_coverage(stream, expected)
            verify_inputs(context, search)
            if digest(binary) != binding['producer_sha256']:
                raise ValueError('native producer changed during export')
            atomic_json(pending / 'expected-roots.json', expected)
            files = {name: {'sha256': digest(pending / name), 'bytes': (pending / name).stat().st_size}
                     for name in ('stream.ndjson', 'roots.json', 'expected-roots.json')}
            receipt = {'schema': 2, 'binding': binding, 'files': files, 'coverage': metrics}
            for name in files:
                os.replace(pending / name, folder / name)
            atomic_json(folder / 'complete.json', receipt)
        return folder, receipt, False
