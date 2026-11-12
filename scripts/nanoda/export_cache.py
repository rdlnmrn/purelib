"""Publish and reload complete native streams under exact compiled input bindings."""

import fcntl
import hashlib
import inspect
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
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


def _checkpoint_policy(functions, files):
    """Bind one preparation phase without invalidating it for unrelated later phases."""
    return {'python': digest(sys.executable),
            'functions': {function.__name__: hashlib.sha256(inspect.getsource(function).encode()).hexdigest()
                          for function in (_checkpoint_policy, *functions)},
            'files': {str(path): digest(path) for path in files}}


def root_validation_policy():
    """Bind the complete independent selector and its checkpoint/reload implementation."""
    files = [Path(__file__).with_name('artifact_inputs.py'), Path(__file__).with_name('root_inventory.py'),
             *sorted((ROOT / 'scripts/lean_module_data').glob('*.py'))]
    return _checkpoint_policy((root_validation_policy, prepare_roots, atomic_json), files)


def prepare_roots(modules, context, directory, search):
    """Checkpoint independent root selection under complete compiled input bindings.

    This receipt covers preparation only. Native export still compares its
    actual roots with this inventory, and the independent checker still checks
    the complete emitted stream.
    """
    if (not modules or len(modules) != len(set(modules)) or
            context['selected_modules'] != modules or context['inventory']['roots'] != modules):
        raise ValueError('root preparation requires the exact selected module inventory')
    binding = {'schema': 1, 'modules': modules, 'compiled_inputs': context,
               'validation': root_validation_policy(),
               'root_predicate': 'authoritative-safe-source-and-global-csimp-v1'}
    folder = Path(directory) / 'root-inventories' / identity(binding)
    folder.mkdir(parents=True, exist_ok=True)
    with (folder / 'prepare.lock').open('w') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        verify_inputs(context, search)
        marker, inventory = folder / 'complete.json', folder / 'roots.json'
        if marker.exists():
            receipt = json.loads(marker.read_text())
            if receipt.get('schema') != 1 or receipt.get('binding') != binding:
                raise ValueError(f'corrupt prepared root binding: {marker}')
            if (inventory.stat().st_size != receipt['bytes'] or
                    digest(inventory) != receipt['sha256']):
                raise ValueError(f'corrupt prepared root inventory: {inventory}')
            expected = json.loads(inventory.read_text())
            if (expected.get('schema') != 2 or expected.get('selected_modules') != modules or
                    not isinstance(expected.get('roots'), list) or
                    len(expected['roots']) != receipt['roots']):
                raise ValueError(f'inconsistent prepared root coverage: {marker}')
            return folder, expected, True
        expected = authoritative_roots(modules, search)
        verify_inputs(context, search)
        atomic_json(inventory, expected)
        atomic_json(marker, {'schema': 1, 'binding': binding, 'sha256': digest(inventory),
                             'bytes': inventory.stat().st_size, 'roots': len(expected['roots'])})
        return folder, expected, False


def native_validation_policy():
    """Bind native request execution separately from subsequent stream coverage checking."""
    return _checkpoint_policy((native_validation_policy, prepare_native, reload_native, atomic_json),
                              [Path(__file__).with_name('artifact_inputs.py')])


def reload_native(directory, binding):
    """Reload exact native bytes only after a recorded successful producer exit."""
    directory = Path(directory)
    marker = directory / 'complete.json'
    if not marker.exists():
        return None
    receipt = json.loads(marker.read_text())
    names = ('stream.ndjson', 'roots.json', 'exit.json', 'modules.txt')
    if (receipt.get('schema') != 1 or receipt.get('binding') != binding or
            set(receipt.get('files', {})) != set(names)):
        raise ValueError(f'corrupt native preparation binding: {marker}')
    for name in names:
        path = directory / name
        if path.stat().st_size != receipt['files'][name]['bytes'] or digest(path) != receipt['files'][name]['sha256']:
            raise ValueError(f'corrupt prepared native output: {path}')
    if json.loads((directory / 'exit.json').read_text()).get('raw_exit_code') != 0:
        raise ValueError(f'native preparation has no successful producer exit: {marker}')
    return receipt


def prepare_native(modules, context, binary, directory, search, policy):
    """Checkpoint one completed native export before expensive coverage validation.

    The original producer, request and complete compiled inputs remain bound.
    These bytes are still untrusted: export_group validates their full coverage
    and the independent checker verifies the complete stream afterward.
    """
    root_folder, expected, _ = prepare_roots(modules, context, directory, search)
    root_marker = root_folder / 'complete.json'
    binding = {'schema': 1, 'modules': modules,
               'prepared_roots': {'receipt': str(root_marker.resolve()), 'sha256': digest(root_marker)},
               'producer_sha256': digest(binary), 'policy': policy, 'validation': native_validation_policy()}
    folder = Path(directory) / 'native-outputs' / identity(binding)
    folder.mkdir(parents=True, exist_ok=True)
    with (folder / 'prepare.lock').open('w') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        verify_inputs(context, search)
        cached = reload_native(folder, binding)
        if cached is not None:
            validate_roots(json.loads((folder / 'roots.json').read_text()), expected)
            return folder, cached, expected, True
        # Incomplete attempts retain their inputs, diagnostics and any raw exit.
        # They cannot be adopted without the final content-bound marker.
        pending = Path(tempfile.mkdtemp(prefix='pending-', dir=folder))
        manifest = pending / 'modules.txt'
        manifest.write_text('\n'.join(modules) + '\n')
        atomic_json(pending / 'request.json', binding)
        stream, roots = pending / 'stream.ndjson', pending / 'roots.json'
        with stream.open('wb') as output:
            result = subprocess.run([str(binary), '--export', str(manifest), str(roots)], stdout=output)
            atomic_json(pending / 'exit.json', {'raw_exit_code': result.returncode})
            result.check_returncode()
        validate_roots(json.loads(roots.read_text()), expected)
        verify_inputs(context, search)
        if digest(binary) != binding['producer_sha256'] or digest(root_marker) != binding['prepared_roots']['sha256']:
            raise ValueError('native preparation inputs changed during execution')
        names = ('stream.ndjson', 'roots.json', 'exit.json', 'modules.txt')
        files = {name: {'sha256': digest(pending / name), 'bytes': (pending / name).stat().st_size}
                 for name in names}
        for name in names:
            os.replace(pending / name, folder / name)
        receipt = {'schema': 1, 'binding': binding, 'files': files}
        atomic_json(folder / 'complete.json', receipt)
        return folder, receipt, expected, False


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
        native, native_receipt, expected, _ = prepare_native(modules, context, binary, directory, search, policy)
        metrics = validate_coverage(native / 'stream.ndjson', expected)
        with tempfile.TemporaryDirectory(prefix='pending-', dir=folder) as temporary:
            pending = Path(temporary)
            stream = pending / 'stream.ndjson'
            roots_path = pending / 'roots.json'
            # Keep the validated group independently recoverable if either
            # cache's bytes are later damaged; neither file is a mutable alias.
            shutil.copyfile(native / 'stream.ndjson', stream)
            shutil.copyfile(native / 'roots.json', roots_path)
            roots = json.loads(roots_path.read_text())
            validate_roots(roots, expected)
            verify_inputs(context, search)
            if digest(binary) != binding['producer_sha256']:
                raise ValueError('native producer changed during export')
            atomic_json(pending / 'expected-roots.json', expected)
            files = {name: {'sha256': digest(pending / name), 'bytes': (pending / name).stat().st_size}
                     for name in ('stream.ndjson', 'roots.json', 'expected-roots.json')}
            if any(files[name] != native_receipt['files'][name] for name in ('stream.ndjson', 'roots.json')):
                raise ValueError('prepared native bytes changed during coverage validation')
            receipt = {'schema': 2, 'binding': binding, 'files': files, 'coverage': metrics}
            for name in files:
                os.replace(pending / name, folder / name)
            atomic_json(folder / 'complete.json', receipt)
        return folder, receipt, False
