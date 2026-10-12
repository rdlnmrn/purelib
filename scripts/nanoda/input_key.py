#!/usr/bin/env python3
"""Fingerprint selected compiled modules and their transitive import inputs.

The host artifact reader reads imports from compiled module data, including private
parts. Cached inventories are reusable only while every recorded input and
module resolution remains unchanged. Unrelated files are not inputs.
"""
import argparse
import fcntl
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile
import time


def digest(path):
    with Path(path).open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def identity(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True).encode()).hexdigest()


def atomic_json(path, value):
    temporary = path.with_suffix(path.suffix + '.partial')
    temporary.write_text(json.dumps(value, sort_keys=True) + '\n')
    os.replace(temporary, path)


def resolve(name, search):
    relative = Path(*name.split('.')).with_suffix('.olean')
    for base in search:
        candidate = base / relative
        if candidate.is_file():
            return candidate.resolve()
    raise ValueError(f'cannot resolve compiled module: {name}')


def validate_inventory(data, roots, search):
    if data.get('schema') != 1 or data.get('roots') != roots:
        raise ValueError('module inventory root/schema mismatch')
    nodes = {node['name']: node for node in data['modules']}
    if len(nodes) != len(data['modules']):
        raise ValueError('duplicate compiled module inventory node')
    reached, pending = set(), list(roots)
    while pending:
        name = pending.pop()
        if name in reached:
            continue
        if name not in nodes:
            raise ValueError(f'missing compiled module dependency: {name}')
        reached.add(name)
        pending.extend(nodes[name]['imports'])
    if reached != set(nodes):
        raise ValueError('unreachable compiled module inventory nodes')
    files = []
    for name in sorted(nodes):
        main = resolve(name, search)
        paths = [Path(p).resolve() for p in nodes[name]['files']]
        if paths not in ([main], [main, Path(str(main) + '.server'), Path(str(main) + '.private')]):
            raise ValueError(f'compiled module resolution/parts changed: {name}')
        files.extend(paths)
        # Private import finalization also observes interpreter metadata. Keep
        # the original three-part inventory schema; bind present consumed IR
        # independently so changing/removing it invalidates reuse. The export
        # importer retains its original explicit missing-IR failure.
        ir=main.with_suffix('.ir')
        if len(paths)==3 and ir.is_file():files.append(ir)
    return files


def fingerprint(paths, started=None):
    result = {}
    for path in paths:
        before = path.stat()
        value = digest(path)
        after = path.stat()
        signature = lambda s: (s.st_ino, s.st_size, s.st_mtime_ns, s.st_ctime_ns)
        if signature(before) != signature(after) or (started is not None and after.st_mtime_ns > started):
            raise ValueError(f'compiled input changed during inventory: {path}')
        result[str(path)] = value
    return result


def module_keys(data, hashes):
    # Merkle identities retain one copy of each direct edge, rather than
    # repeatedly materializing every module's transitive file list.
    from graphlib import TopologicalSorter
    nodes = {node['name']: node for node in data['modules']}
    keys = {}
    for name in TopologicalSorter({n: node['imports'] for n, node in nodes.items()}).static_order():
        node = nodes[name]
        keys[name] = identity({'name': name,
                              'files': {str(Path(p).resolve()): hashes[str(Path(p).resolve())]
                                        for p in node['files']},
                              'execution': {str(Path(node['files'][0]).resolve().with_suffix('.ir')):hashes[str(Path(node['files'][0]).resolve().with_suffix('.ir'))]} if len(node['files'])==3 and str(Path(node['files'][0]).resolve().with_suffix('.ir')) in hashes else {},
                              'imports': {n: keys[n] for n in node['imports']}})
    return keys


def producer_identity(command):
    if not isinstance(command,list) or not command or not all(isinstance(x,str) and x for x in command):
        raise ValueError('nonempty exporter command argument array required')
    import shutil
    executable=shutil.which(command[0])
    if executable is None:raise FileNotFoundError(command[0])
    files={str(Path(executable).resolve()):digest(executable)}
    for argument in command[1:]:
        path=Path(argument)
        if path.is_file():files[str(path.resolve())]=digest(path)
    # The reader is one coherent source owner; every selected implementation
    # part binds cache identity rather than only its small dispatch script.
    reader=(Path(__file__).resolve().parents[1] / 'project-module-data.py').resolve()
    if str(reader) in files or command[1:3] == ['-m', 'scripts.nanoda.graph_data']:
        graph_reader = Path(__file__).with_name('graph_data.py')
        files[str(graph_reader.resolve())] = digest(graph_reader)
        for part in sorted(reader.with_name('lean_module_data').glob('*.py')):
            files[str(part.resolve())]=digest(part)
    return {'command':command,'files':files}


def input_key(manifest, driver, cache, search, policy):
    roots = [line.strip() for line in manifest.read_text().splitlines() if line.strip()]
    if not roots or len(set(roots)) != len(roots):
        raise ValueError('empty or duplicate module roots')
    producer = producer_identity(driver)
    search = [p.resolve() for p in search]
    namespace = identity({'roots': roots, 'producer': producer,
                          'search': list(map(str, search)), 'implementation': digest(__file__)})
    directory = cache / namespace
    directory.mkdir(parents=True, exist_ok=True)
    with (directory / 'lock').open('w') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        pointer = directory / 'current.json'
        saved = json.loads(pointer.read_text()) if pointer.exists() else None
        reusable = False
        if saved:
            inventory = directory / saved['inventory']
            if digest(inventory) != saved['inventory_sha256']:
                raise ValueError('corrupt cached compiled module inventory')
            data = json.loads(inventory.read_text())
            try:
                paths = validate_inventory(data, roots, search)
                hashes = fingerprint(paths)
                reusable = hashes == saved['files']
            except (FileNotFoundError, ValueError):
                reusable = False
        if not reusable:
            with tempfile.TemporaryDirectory(prefix='inventory-', dir=directory) as temporary:
                output = Path(temporary) / 'inputs.json'
                started = time.time_ns()
                subprocess.run([*driver, '--module-inputs', str(manifest.resolve()), str(output)], check=True)
                data = json.loads(output.read_text())
                paths = validate_inventory(data, roots, search)
                hashes = fingerprint(paths, started)
                if producer_identity(driver)!=producer:raise ValueError('export producer changed during inventory')
                sha = digest(output)
                inventory = directory / (sha + '.json')
                os.replace(output, inventory)
                saved = {'inventory': inventory.name, 'inventory_sha256': sha, 'files': hashes}
                atomic_json(pointer, saved)
        if producer_identity(driver)!=producer:raise ValueError('export producer changed during inventory')
        key = identity({'schema': 1, 'producer': namespace, 'roots': roots, 'files': hashes, 'policy': policy})
        receipt = directory / (key + '.provenance.json')
        atomic_json(receipt, {'schema': 1, 'key': key, 'roots': roots, 'files': hashes,
                              'policy': policy, 'module_keys': module_keys(data, hashes),
                              'inventory': str(inventory),
                              'inventory_sha256': saved['inventory_sha256']})
        return key, receipt, reusable


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--driver-command', required=True, type=json.loads, help='nonempty JSON argument array')
    parser.add_argument('--cache', required=True, type=Path)
    parser.add_argument('--sysroot', required=True, type=Path)
    parser.add_argument('--policy-key', required=True)
    parser.add_argument('--context', type=Path)
    parser.add_argument('manifest', type=Path)
    args = parser.parse_args()
    search = [Path(p) for p in os.environ.get('LEAN_PATH', '').split(os.pathsep) if p]
    search.append(args.sysroot / 'lib/lean')
    key, receipt, reused = input_key(args.manifest, args.driver_command, args.cache, search, args.policy_key)
    if args.context:
        provenance = json.loads(receipt.read_text())
        atomic_json(args.context, {'module_keys': provenance['module_keys'],
                                   'roots': provenance['roots'],
                                   'inventory': provenance['inventory'],
                                   'inventory_sha256': provenance['inventory_sha256']})
    import sys
    print(f'nanoda inputs: {"retained" if reused else "refreshed"} {receipt}', file=sys.stderr)
    print(key)


if __name__ == '__main__':
    main()
