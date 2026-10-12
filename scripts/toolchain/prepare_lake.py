"""Install the pinned native Lake scheduler fix without changing the Core epoch.

The warm path checks file identities and metadata. Changed metadata triggers full
hash validation; changed bytes trigger a rebuild. No installed toolchain is edited.
"""
from __future__ import annotations

import argparse
import fcntl
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
PARTS = ('.olean', '.ir', '.olean.server', '.olean.private')


def sha(path):
    digest = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b''):
            digest.update(chunk)
    return digest.hexdigest()


def signature(path):
    path = Path(path)
    stat = path.stat()
    return [str(path.resolve()), stat.st_dev, stat.st_ino, stat.st_size,
            stat.st_mtime_ns, stat.st_ctime_ns]


def bind(path):
    return {'path': str(path), 'sha256': sha(path), 'signature': signature(path)}


def put(path, value):
    tmp = Path(str(path) + '.tmp')
    tmp.write_text(json.dumps(value, sort_keys=True) + '\n')
    tmp.replace(path)


def valid(rows):
    """Use metadata as a hash memo, never accept changed bytes on a slow check."""
    try:
        for row in rows:
            current = signature(row['path'])
            if current != row['signature']:
                if sha(row['path']) != row['sha256']:
                    return False
                row['signature'] = current
        return True
    except (OSError, KeyError, TypeError):
        return False


def run(args, cwd, env, label):
    log = cwd / (label + '.log')
    print(f'Lake patch: {label} (log: {log})', file=sys.stderr, flush=True)
    with log.open('wb') as stream:
        stream.write((json.dumps(list(map(str, args))) + '\n').encode())
        stream.flush()
        result = subprocess.run(list(map(str, args)), cwd=cwd, env=env,
                                stdout=stream, stderr=subprocess.STDOUT)
    if result.returncode:
        raise RuntimeError(f'{label} failed ({result.returncode}); see {log}')


def package(base, module):
    from scripts.lean_module_data.typed import TypedDecoder
    from scripts.lean_module_data.render import Renderer
    decoder = TypedDecoder([])
    renderer = Renderer(decoder)
    region = decoder.parts.add(base / 'lib/lean' / (module.replace('.', '/') + '.olean'))
    fields = decoder.parts.ctor(region.root, 0, 5, 1)[2]
    for ptr in decoder.parts.array(fields[4]):
        fs = decoder.parts.ctor(ptr, 0, 2, 0)[2]
        name = renderer.name_string(decoder.decode('Name', fs[0]))
        if name == '_private.Lean.Compiler.ModPkgExt.0.Lean.modPkgExt':
            values = decoder.parts.array(fs[1])
            if len(values) != 1:
                raise ValueError('ambiguous module package')
            z = values[0]
            return None if z == 1 else decoder.parts.string(decoder.parts.ctor(z, 1, 1, 0)[2][0])
    raise ValueError('missing module package')


def overlay(prefix, target, base, archive, shared):
    """Use the accepted Core compiler with a separately linked Lake driver."""
    for directory in (target, target / 'bin', target / 'lib', target / 'lib/lean'):
        directory.mkdir(parents=True, exist_ok=True)
    for owner, dest, excluded in ((prefix, target, {'bin', 'lib'}),
                                  (prefix / 'bin', target / 'bin', {'lake'}),
                                  (prefix / 'lib', target / 'lib', {'lean'}),
                                  (prefix / 'lib/lean', target / 'lib/lean', {'libLake.a', 'libLake_shared.so'})):
        for entry in owner.iterdir():
            if entry.name not in excluded:
                (dest / entry.name).symlink_to(entry)
    shutil.copy2(base / 'bin/lake', target / 'bin/lake')
    shutil.copy2(archive, target / 'lib/lean/libLake.a')
    shutil.copy2(shared, target / 'lib/lean/libLake_shared.so')


def links(target):
    return {str(p): os.readlink(p) for p in target.rglob('*') if p.is_symlink()}


def prepare(prefix, cache, config_path=HERE / 'lake-patch.json'):
    prefix, cache, config_path = map(lambda p: Path(p).absolute(), (prefix, cache, config_path))
    cfg = json.loads(config_path.read_text())
    if cfg['schema'] != 1:
        raise ValueError('unsupported Lake patch schema')
    patch = config_path.parent / cfg['patch']
    if sha(patch) != cfg['patch_sha256']:
        raise ValueError('Lake patch hash mismatch')
    base = Path(json.loads((prefix / 'CORE-PREFIX.json').read_text())['base_sysroot'])
    key = hashlib.sha256(json.dumps([str(prefix), str(base), sha(config_path),
                                    sha(Path(__file__)), sha(patch)], sort_keys=True).encode()).hexdigest()
    cache.mkdir(parents=True, exist_ok=True)
    with (cache / 'install.lock').open('a') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        receipt_path = cache / (key + '.json')
        if receipt_path.is_file():
            try:
                receipt = json.loads(receipt_path.read_text())
            except (ValueError, OSError):
                receipt = {}
            before = json.dumps(receipt, sort_keys=True)
            if (receipt.get('key') == key and isinstance(receipt.get('links'), dict)
                    and isinstance(receipt.get('lake'), str)
                    and valid(receipt.get('inputs')) and valid(receipt.get('outputs'))
                    and all(Path(p).is_symlink() and os.readlink(p) == value
                            for p, value in receipt['links'].items())):
                if json.dumps(receipt, sort_keys=True) != before:
                    put(receipt_path, receipt)
                return Path(receipt['lake'])
        # All generated stages are isolated; a failed attempt cannot be selected.
        stage = cache / (key + '.building')
        stage.mkdir(exist_ok=True)
        env = os.environ.copy()
        for name in ('LEAN_SYSROOT', 'LEAN_PATH', 'LEAN_GITHASH', 'LAKE_OVERRIDE_LEAN'):
            env.pop(name, None)
        source = base / cfg['source']
        if sha(source) != cfg['source_sha256']:
            raise ValueError('unsupported upstream Lake source')
        inputs = [bind(config_path), bind(patch), bind(Path(__file__)), bind(source)]
        for relative, expected in cfg['native_inputs'].items():
            row = bind(base / relative)
            if row['sha256'] != expected:
                raise ValueError('unsupported upstream native input: ' + relative)
            inputs.append(row)
        from scripts.lean_module_data.compact import inventory
        data, _ = inventory([cfg['module']], [base / 'lib/lean'])
        arts = {}
        for row in data['modules']:
            paths = [base / 'lib/lean' / (row['name'].replace('.', '/') + suffix) for suffix in PARTS]
            inputs.extend(bind(p) for p in paths)
            if row['name'] != cfg['module']:
                arts[row['name']] = list(map(str, paths))
        # Also bind the decoder implementation used to reconstruct the import setup.
        for name in ('compact.py', 'typed.py', 'render.py'):
            inputs.append(bind(HERE.parent / 'lean_module_data' / name))
        for directory in ('include', 'lib/clang', 'lib/glibc'):
            inputs.extend(bind(p) for p in sorted((base / directory).rglob('*')) if p.is_file())
        inputs.extend(bind(p) for p in sorted((base / 'lib/lean').glob('*.so')) if p.is_file())
        inputs.append(bind(base / 'bin/ld.lld'))
        for name in ('ar', 'nm', 'patch'):
            tool = shutil.which(name)
            if not tool:
                raise ValueError('missing tool: ' + name)
            inputs.append(bind(Path(tool).resolve()))
        source_root = stage / 'source'
        dst = source_root / (cfg['module'].replace('.', '/') + '.lean')
        dst.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(source, dst)
        run(['patch', '--batch', '--forward', '-p1', '-i', patch], source_root, env, 'patch')
        if sha(dst) != cfg['patched_source_sha256']:
            raise ValueError('patched source hash mismatch')
        setup_path = stage / 'setup.json'
        put(setup_path, {'name': cfg['module'], 'package': package(base, cfg['module']),
                         'isModule': True, 'imports': None, 'importArts': arts,
                         'options': {}, 'dynlibs': [], 'plugins': []})
        emitted = stage / 'Module'
        # Reuse the expensive compile only when every complete input and output matches.
        compile_key = hashlib.sha256(json.dumps([(r['path'], r['sha256']) for r in inputs]).encode()).hexdigest()
        checkpoint = stage / 'compile.json'
        try:
            old = json.loads(checkpoint.read_text())
        except (ValueError, OSError):
            old = {}
        if not (old.get('key') == compile_key and valid(old.get('outputs'))):
            run([base / 'bin/lean', '-R', source_root, '--setup', setup_path,
                 '-DwarningAsError=true', dst, '-o', str(emitted) + '.olean',
                 '-i', str(emitted) + '.ilean', '-c', str(emitted) + '.c'], stage, env, 'compile')
            put(checkpoint, {'key': compile_key, 'outputs': [bind(str(emitted) + s) for s in (*PARTS, '.ilean', '.c')]})
        obj = stage / 'LakeBuildModule.o'
        run([base / 'bin/leanc', '-DLEAN_EXPORTING', '-O3', '-fPIC', '-c', str(emitted) + '.c', '-o', obj], stage, env, 'native-compile')
        archive = stage / 'libLake.a'
        shutil.copy2(base / 'lib/lean/libLake.a', archive)
        members = subprocess.check_output(['ar', 't', archive], text=True).splitlines()
        if members.count(cfg['archive_member']) != cfg['archive_member_count']:
            raise ValueError('unexpected archive member count')
        run(['ar', 'xN', cfg['archive_instance'], archive, cfg['archive_member']], stage, env, 'extract')
        symbols = subprocess.check_output(['nm', '--defined-only', stage / cfg['archive_member']], text=True)
        if not any(line.split()[-1:] == [cfg['initializer']] for line in symbols.splitlines()):
            raise ValueError('wrong archive member selected')
        run(['ar', 'dN', cfg['archive_instance'], archive, cfg['archive_member']], stage, env, 'remove')
        run(['ar', 'r', archive, obj], stage, env, 'replace')
        shared = stage / 'libLake_shared.so'
        run([base / 'bin/leanc', '-shared', '-o', shared, '-Wl,-soname,libLake_shared.so',
             '-Wl,-rpath,$ORIGIN', '-Wl,--whole-archive', archive, '-Wl,--no-whole-archive',
             '-L', base / 'lib/lean', '-lleanshared', '-lInit_shared'], stage, env, 'link')
        # Publish selection only after linking and smoke checks succeed. Old
        # installations remain valid for processes that already selected them.
        target = Path(tempfile.mkdtemp(prefix=key + '.', dir=cache))
        overlay(prefix, target, base, archive, shared)
        run([target / 'bin/lake', '--version'], stage, {**env, 'LEAN_SYSROOT': str(prefix), 'LAKE_OVERRIDE_LEAN': 'true'}, 'smoke')
        if not valid(inputs):
            raise ValueError('inputs changed during installation')
        outputs = [bind(target / p) for p in ('bin/lake', 'lib/lean/libLake.a', 'lib/lean/libLake_shared.so')]
        outputs.extend(json.loads(checkpoint.read_text())['outputs'])
        outputs.extend(bind(p) for p in (dst, setup_path))
        put(receipt_path, {'schema': 1, 'key': key, 'lake': str(target / 'bin/lake'),
                           'inputs': inputs, 'outputs': outputs, 'links': links(target)})
        return target / 'bin/lake'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--prefix', type=Path, required=True)
    parser.add_argument('--cache', type=Path, required=True)
    args = parser.parse_args()
    try:
        print(prepare(args.prefix, args.cache))
    except (OSError, ValueError, RuntimeError, subprocess.CalledProcessError) as error:
        parser.exit(1, f'Lake patch: {error}\n')


if __name__ == '__main__':
    main()
