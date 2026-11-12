"""Build the pinned frontend repairs over an accepted Core prefix.

Keep the original kernel and complete Core providers. Replace the two frontend
owners together with their sources, emitted artifacts, native archive and CLI.
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
import tempfile

from .prepare_lake import bind, links, package, put, sha, valid
from scripts.verification.module_process import MODULE_TIMEOUT, MODULE_TARGET, run as run_worker

HERE = Path(__file__).resolve().parent
PARTS = ('.olean', '.ir', '.olean.server', '.olean.private', '.ilean', '.c')


def valid_emission(rows, stem):
    """Accept only the complete six-part emission at its original paths."""
    return (isinstance(rows, list) and len(rows) == len(PARTS)
            and {row.get('path') for row in rows if isinstance(row, dict)}
            == {str(stem) + suffix for suffix in PARTS}
            and valid(rows))


def run(command, stage, env, label):
    log = stage / (label + '.log')
    with log.open('wb') as stream:
        stream.write((json.dumps(list(map(str, command))) + '\n').encode())
        stream.flush()
        compilation = any(str(arg).endswith('.lean') for arg in command)
        receipts = stage / 'process-receipts'
        receipt = receipts / (label + '.json')
        try:
            code = run_worker(list(map(str, command)), label, receipts, cwd=stage, env=env,
                              stdout=stream, receipt_path=receipt,
                              timeout=MODULE_TIMEOUT if compilation else 300,
                              performance_target=MODULE_TARGET if compilation else None)
        finally:
            if receipt.exists():
                put(stage / (label + '.exit.json'), {'raw_exit_code':
                    json.loads(receipt.read_text())['raw_exit_code']})
    if code:
        raise RuntimeError(f'frontend {label} failed ({code}); see {log}')


def overlay(prefix, target, replacements):
    """Copy replacements; link untouched branches without writing through links."""
    selected = set(replacements)

    def visit(owner, dest, relative):
        dest.mkdir(parents=True, exist_ok=True)
        for entry in owner.iterdir():
            path = relative / entry.name
            if path in selected:
                continue
            if any(path in chosen.parents for chosen in selected):
                if not entry.is_dir():
                    raise ValueError('replacement parent is not a directory: ' + str(entry))
                visit(entry, dest / entry.name, path)
            else:
                (dest / entry.name).symlink_to(entry.absolute())

    visit(prefix, target, Path())
    for relative, source in replacements.items():
        dest = target / relative
        dest.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(source, dest)


def prepare(prefix, cache, config_path=HERE / 'frontend-patches.json'):
    prefix, cache, config_path = map(lambda p: Path(p).absolute(), (prefix, cache, config_path))
    config = json.loads(config_path.read_text())
    if config['schema'] != 1 or not config['sources']:
        raise ValueError('unsupported or empty frontend configuration')
    parent = prefix / 'CORE-PREFIX.json'
    base = Path(json.loads(parent.read_text())['base_sysroot'])
    patches = [config_path.parent / row['patch'] for row in config['sources']]
    for row, patch in zip(config['sources'], patches):
        if sha(patch) != row['patch_sha256']:
            raise ValueError('frontend patch hash mismatch: ' + row['module'])
    producers = [Path(__file__), HERE / 'prepare_lake.py',
                 *sorted((HERE.parent / 'lean_module_data').glob('*.py'))]
    key = hashlib.sha256(json.dumps([
        str(prefix), sha(parent), sha(config_path),
        *[sha(p) for p in producers], *[sha(p) for p in patches],
    ]).encode()).hexdigest()
    cache.mkdir(parents=True, exist_ok=True)
    with (cache / 'install.lock').open('a') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        receipt_path = cache / (key + '.json')
        try:
            receipt = json.loads(receipt_path.read_text())
        except (OSError, ValueError):
            receipt = {}
        before = json.dumps(receipt, sort_keys=True)
        if (receipt.get('key') == key and isinstance(receipt.get('prefix'), str)
                and receipt.get('inputs') and receipt.get('outputs')
                and valid(receipt.get('inputs'))
                and valid(receipt.get('outputs'))
                and receipt.get('links')
                and links(Path(receipt['prefix'])) == receipt['links']):
            if json.dumps(receipt, sort_keys=True) != before:
                put(receipt_path, receipt)
            return Path(receipt['prefix'])
        stage = cache / (key + '.building')
        stage.mkdir(exist_ok=True)
        env = os.environ.copy()
        for name in ('LEAN_SYSROOT', 'LEAN_PATH', 'LEAN_GITHASH', 'LAKE_OVERRIDE_LEAN'):
            env.pop(name, None)
        env['LEAN_NUM_THREADS'] = '8'
        inputs = [bind(parent), bind(config_path), *map(bind, producers), *map(bind, patches)]
        inputs.extend(bind(prefix / p) for p in (
            'bin/lean', 'bin/leanc', 'bin/clang', 'bin/ld.lld',
            'lib/lean/libLean.a', 'lib/lean/libInit.a', 'lib/lean/libStd.a',
            'lib/lean/libleancpp.a', 'lib/lean/libleanrt.a'))
        for directory in ('include', 'lib/clang', 'lib/glibc'):
            inputs.extend(bind(p) for p in sorted((prefix / directory).rglob('*')) if p.is_file())
        inputs.extend(bind(p) for p in sorted((prefix / 'lib/lean').glob('*.so')) if p.is_file())
        for name in ('ar', 'nm', 'patch'):
            executable = shutil.which(name)
            if not executable:
                raise ValueError('missing tool: ' + name)
            inputs.append(bind(Path(executable).resolve()))
        from scripts.lean_module_data.compact import inventory
        modules = [row['module'] for row in config['sources']]
        if len(set(modules)) != len(modules):
            raise ValueError('duplicate frontend owner')
        cli_data, _ = inventory(['Lean.Shell', 'Lean.Elab.Frontend'], [prefix / 'lib/lean'])
        cli_arts = {}
        for owner in cli_data['modules']:
            paths = [prefix / 'lib/lean' / (owner['name'].replace('.', '/') + suffix)
                     for suffix in PARTS[:4]]
            inputs.extend(map(bind, paths))
            cli_arts[owner['name']] = list(map(str, paths))
        source_root = stage / 'source'
        replacements = {}
        objects = []
        for index, row in enumerate(config['sources']):
            module = row['module']
            original = base / row['source']
            if sha(original) != row['original_source_sha256']:
                raise ValueError('unsupported frontend source: ' + module)
            if sha(prefix / row['source']) != row['original_source_sha256']:
                raise ValueError('frontend owner already has another source repair: ' + module)
            inputs.append(bind(original))
            relative = Path(module.replace('.', '/') + '.lean')
            source = source_root / relative
            source.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(original, source)
            run(['patch', '--batch', '--fuzz=0', '-p1', '-i', patches[index]],
                source_root, env, f'patch-{index}')
            if sha(source) != row['candidate_source_sha256']:
                raise ValueError('patched frontend source mismatch: ' + module)
            data, _ = inventory([module], [prefix / 'lib/lean'])
            arts = {}
            for owner in data['modules']:
                paths = [prefix / 'lib/lean' / (owner['name'].replace('.', '/') + suffix)
                         for suffix in PARTS[:4]]
                inputs.extend(map(bind, paths))
                if owner['name'] != module:
                    arts[owner['name']] = list(map(str, paths))
            setup = stage / f'setup-{index}.json'
            put(setup, {'name': module, 'package': package(prefix, module), 'isModule': True,
                        'imports': None, 'importArts': arts, 'options': {}, 'dynlibs': [], 'plugins': []})
            emitted = stage / f'Module-{index}'
            checkpoint = stage / f'compile-{index}.json'
            compile_key = hashlib.sha256(json.dumps([
                [(r['path'], r['sha256']) for r in inputs],
                {'path': str(source), 'sha256': sha(source)},
                {'path': str(setup), 'sha256': sha(setup)},
                env['LEAN_NUM_THREADS'],
            ], sort_keys=True).encode()).hexdigest()
            try:
                previous = json.loads(checkpoint.read_text())
            except (OSError, ValueError):
                previous = {}
            if not (previous.get('key') == compile_key
                    and valid_emission(previous.get('outputs'), emitted)):
                run([prefix / 'bin/lean', '-R', source_root, '--setup', setup,
                     '-DwarningAsError=true', source, '-o', str(emitted) + '.olean',
                     '-i', str(emitted) + '.ilean', '-c', str(emitted) + '.c'],
                    stage, env, f'compile-{index}')
                put(checkpoint, {'key': compile_key, 'outputs': [bind(str(emitted) + s) for s in PARTS]})
            obj = stage / f'Frontend-{index}.o'
            run([prefix / 'bin/leanc', '-DLEAN_EXPORTING', '-O3', '-c',
                 str(emitted) + '.c', '-o', obj], stage, env, f'native-{index}')
            objects.append(obj)
            replacements[Path(row['source'])] = source
            for suffix in PARTS:
                replacements[Path('lib/lean') / (module.replace('.', '/') + suffix)] = Path(str(emitted) + suffix)
        archive = stage / 'libLean.a'
        shutil.copy2(prefix / 'lib/lean/libLean.a', archive)
        for index, row in enumerate(config['sources']):
            member = row['archive_member']
            members = subprocess.check_output(['ar', 't', archive], text=True).splitlines()
            if members.count(member) != row['archive_member_count']:
                raise ValueError('unexpected frontend archive member count')
            run(['ar', 'xN', row['archive_instance'], archive, member], stage, env, f'extract-{index}')
            if sha(stage / member) != row['original_member_sha256']:
                raise ValueError('unsupported native frontend member: ' + row['module'])
            symbols = subprocess.check_output(['nm', '--defined-only', stage / member], text=True)
            if not any(line.split()[-1:] == [row['initializer']] for line in symbols.splitlines()):
                raise ValueError('wrong frontend archive member selected')
            run(['ar', 'dN', row['archive_instance'], archive, member], stage, env, f'remove-{index}')
        run(['ar', 'rcs', archive, *objects], stage, env, 'archive')
        driver = config_path.parent / config['driver']
        if sha(driver) != config['driver_sha256']:
            raise ValueError('frontend CLI source mismatch')
        inputs.append(bind(driver))
        cli = source_root / 'PrivateLeanCLI.lean'
        shutil.copy2(driver, cli)
        setup = stage / 'cli-setup.json'
        put(setup, {'name': 'PrivateLeanCLI', 'package': None, 'isModule': True,
                    'imports': None, 'importArts': cli_arts, 'options': {}, 'dynlibs': [], 'plugins': []})
        run([prefix / 'bin/lean', '-R', source_root, '--setup', setup, cli,
             '-c', stage / 'CLI.c'], stage, {**env, 'LEAN_PATH': str(prefix / 'lib/lean')}, 'cli')
        entry = stage / 'CLI.c'
        content = entry.read_text()
        old = 'res = runtime_initialize_PrivateLeanCLI(1 /* builtin */);'
        if content.count(old) != 1:
            raise ValueError('frontend CLI entry shape changed')
        entry.write_text(content.replace(old, 'res = initialize_PrivateLeanCLI(1 /* builtin */);'))
        host = stage / 'lean'
        run([prefix / 'bin/leanc', '-O3', '-Wl,--export-dynamic', '-o', host, entry,
             '-Wl,--whole-archive', archive,
             *[prefix / 'lib/lean' / name for name in ('libInit.a', 'libStd.a', 'libleancpp.a', 'libleanrt.a')],
             '-Wl,--no-whole-archive'], stage, env, 'link')
        replacements[Path('bin/lean')] = host
        replacements[Path('lib/lean/libLean.a')] = archive
        target = Path(tempfile.mkdtemp(prefix=key + '.', dir=cache))
        overlay(prefix, target, replacements)
        outputs = [bind(target / p) for p in replacements]
        outputs.extend(map(bind, [entry, cli, setup, *objects]))
        outputs.extend(bind(p) for p in stage.glob('*.exit.json'))
        for option, expected in (('--print-prefix', target), ('--print-libdir', target / 'lib/lean')):
            actual = subprocess.check_output([target / 'bin/lean', option], env=env, text=True).strip()
            if actual != str(expected):
                raise ValueError('frontend selected the wrong detached prefix')
        if not valid(inputs):
            raise ValueError('frontend inputs changed during installation')
        put(receipt_path, {'schema': 1, 'key': key, 'prefix': str(target), 'inputs': inputs,
                           'outputs': outputs, 'links': links(target)})
        return target


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--prefix', type=Path, required=True)
    parser.add_argument('--cache', type=Path, required=True)
    parser.add_argument('--selection', action='store_true', help='print prefix followed by its content key')
    args = parser.parse_args()
    try:
        prefix = prepare(args.prefix, args.cache)
        print(prefix)
        if args.selection:
            print(prefix.name.split('.')[0])
    except (OSError, ValueError, RuntimeError, subprocess.CalledProcessError) as error:
        parser.exit(1, f'Frontend patch: {error}\n')


if __name__ == '__main__':
    main()
