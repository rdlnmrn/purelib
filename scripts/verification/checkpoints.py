"""Content-bound completed checks, shared by the suite and tooling workers.

These are local execution records, not proof or producer certificates. Consumers
must supply complete input bindings and validate them again before recording a
success. Reusing a test result does not create a new live producer witness.
"""

from __future__ import annotations

import ast
import json
import os
from pathlib import Path
import re
import shlex
import shutil
import stat
import subprocess
import sys
import tempfile

from scripts.nanoda.artifact_inputs import digest, identity
from scripts.profiling.build_costs import Digests


def execution_environment(environment, *, isolated_case=False):
    """Remove launcher diagnostics before execution and input binding.

    Isolated cases own their fixture budgets; the suite's tooling/lint pool
    settings and changing memory headroom remain in their supervisors only.
    Other configuration, compiler selections and runtime limits are retained.
    """
    excluded = {'INVOCATION_ID', 'SYSTEMD_EXEC_PID', 'MEMORY_PRESSURE_WATCH',
                'MEMORY_PRESSURE_WRITE', 'JOURNAL_STREAM'}
    if isolated_case:
        excluded.update(('CCL_CHECK_MEMORY_BYTES', 'CCL_TOOLING_JOBS', 'CCL_LINT_JOBS'))
    return {key: value for key, value in environment.items() if key not in excluded}


def atomic_json(path, value):
    """Replace one complete record atomically, flushing bytes before publication."""
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(mode='w', dir=path.parent, delete=False) as output:
        pending = Path(output.name)
        try:
            json.dump(value, output, sort_keys=True)
            output.write('\n')
            output.flush()
            os.fsync(output.fileno())
            os.replace(pending, path)
        finally:
            pending.unlink(missing_ok=True)


def source_snapshot(root, hash_file=digest):
    """Bind tracked and unignored new files without relying on a commit ID."""
    root = Path(root)
    names = subprocess.check_output(
        ['git', 'ls-files', '-z', '--cached', '--others', '--exclude-standard'], cwd=root)
    result = {}
    for raw in set(names.split(b'\0')) - {b''}:
        name = os.fsdecode(raw)
        path = root / name
        if path.is_symlink():
            result[name] = 'symlink:' + os.readlink(path)
            if path.is_file():
                result[name] += ':' + hash_file(path)
        elif path.exists():
            result[name] = hash_file(path)
        else:
            result[name] = 'missing'
    return result


class Inputs:
    """Bind source, executable and complete compiled parts for one frozen run.

    The filesystem census is repeated on validation; digest caching only avoids
    rereading files whose complete stat identity has not changed. Native Rust
    tooling is a separate input group so repairing it does not invalidate a
    completed Horner check.
    """

    def __init__(self, root, environment, store=None):
        self.root = Path(root).resolve()
        self.environment = dict(environment)
        self.digests = Digests()
        self.store = store
        self.linked_inputs = {}
        self.tree_cache = {}
        self.source_groups = {}

    @staticmethod
    def stamp(path):
        """Observe replacements, symlink retargets and in-place writes cheaply."""
        try:
            before = path.lstat()
            values = (before.st_dev, before.st_ino, before.st_size, before.st_mtime_ns, before.st_ctime_ns)
            if stat.S_ISLNK(before.st_mode):
                try:
                    target = path.stat()
                    values += (target.st_dev, target.st_ino, target.st_size, target.st_mtime_ns, target.st_ctime_ns)
                except FileNotFoundError:
                    values += ('missing target',)
            return values
        except FileNotFoundError:
            return None

    def pin(self, path):
        path = Path(path)
        before = self.stamp(path)
        if not path.exists():
            return {'missing': True}
        result = {'path': str(path.resolve()), 'sha256': self.digests.sha(path),
                  'executable': bool(path.stat().st_mode & 0o111)}
        if self.stamp(path) != before:
            raise ValueError('input changed while binding: ' + str(path))
        return result

    def tree(self, roots, suffixes=None):
        """Retain directory resolution and every matching input, including new files."""
        roots = [Path(root) if Path(root).is_absolute() else self.root / root for root in roots]
        key = tuple(map(str, roots)), suffixes
        old = self.tree_cache.get(key)
        if old is not None and all(self.stamp(path) == stamp for path, stamp in old[1].items()):
            return old[0]
        result = {}
        stamps = {}
        seen = set()
        for root in roots:
            stamps[root] = self.stamp(root)
            result[str(root)] = {'directory': str(root.resolve()), 'exists': root.is_dir()}
            for directory, children, files in os.walk(root, followlinks=True):
                stamps[Path(directory)] = self.stamp(Path(directory))
                resolved = Path(directory).resolve()
                if resolved in seen:
                    children[:] = []
                    continue
                seen.add(resolved)
                for name in files:
                    path = Path(directory) / name
                    if suffixes is None or name.endswith(suffixes):
                        stamps[path] = self.stamp(path)
                        result[str(path)] = self.pin(path)
        if any(self.stamp(path) != stamp for path, stamp in stamps.items()):
            raise ValueError('input tree changed while binding')
        self.tree_cache[key] = result, stamps
        return result

    def executable(self, path):
        """Bind the selected executable, its interpreter and dynamic libraries."""
        path = Path(path)
        result = {'file': self.pin(path)}
        if not path.is_file():
            return result
        key = str(path.resolve()), self.digests.sha(path)
        if key not in self.linked_inputs:
            with path.open('rb') as source:
                header = source.read(4096)
            dependencies = []
            if header.startswith(b'\x7fELF'):
                linked = subprocess.run(['ldd', str(path)], env=self.environment, text=True,
                                        capture_output=True, timeout=30)
                if linked.returncode and 'not a dynamic executable' not in linked.stderr + linked.stdout:
                    raise ValueError('cannot identify executable libraries: ' + str(path))
                if 'not found' in linked.stdout:
                    raise ValueError('missing executable library: ' + linked.stdout.strip())
                dependencies = re.findall(r'(?:^|\s)(/[^\s()]+)', linked.stdout)
            elif header.startswith(b'#!'):
                interpreter = shlex.split(header.splitlines()[0][2:].decode())
                if interpreter:
                    dependencies.append(interpreter[0])
                    if Path(interpreter[0]).name == 'env' and len(interpreter) > 1:
                        selected = shutil.which(interpreter[1], path=self.environment.get('PATH'))
                        if selected is None:
                            raise ValueError('missing script interpreter: ' + interpreter[1])
                        dependencies.append(selected)
            self.linked_inputs[key] = dependencies, header.startswith(b'#!')
        dependencies, scripts = self.linked_inputs[key]
        result['libraries'] = {name: self.executable(name) if scripts else self.pin(name)
                               for name in dependencies}
        return result

    def compiled(self):
        """Bind public, private, server and IR bytes plus the executable SDK."""
        roots = [self.root / '.lake/build/lib/lean']
        if 'LEAN_PATH' in self.environment:
            roots += [Path(p or '.') for p in self.environment['LEAN_PATH'].split(os.pathsep)]
        sdks = set(filter(None, (self.environment.get(key) for key in
                                ('LEAN_SYSROOT', 'CCL_CORE_PREFIX', 'CCL_TEST_CORE_PREFIX'))))
        sdks.add(str(self.root / '.lake/core-toolchain'))
        roots.extend(Path(sdk) / 'lib/lean' for sdk in sorted(sdks))
        result = self.tree(roots, ('.olean', '.olean.private', '.olean.server', '.ir', '.so', '.a'))
        for sdk in sorted(sdks):
            result.update(self.tree([Path(sdk) / 'bin', Path(sdk) / 'include', Path(sdk) / 'src']))
        return result

    def native(self):
        """Bind the actual nanoda binaries and library, including compiler selection."""
        release = self.root / '.external/nanoda/target/release'
        result = self.tree([release], ('.rlib', '.so'))
        for path in [release / 'nanoda_bin', self.environment.get('NANODA_BIN', '')]:
            if path:
                result[str(path)] = self.pin(path)
        compiler = self.environment.get('RUSTC') or shutil.which('rustc', path=self.environment.get('PATH'))
        if not compiler:
            candidate = Path(self.environment.get('CARGO_HOME', Path.home() / '.cargo')) / 'bin/rustc'
            compiler = str(candidate) if candidate.is_file() else None
        if compiler:
            result['rustc'] = subprocess.check_output(
                [compiler, '--version', '--verbose'], env=self.environment, text=True, timeout=30)
            result['rustc_executable'] = self.pin(compiler)
        else:
            result['rustc'] = 'missing'
        return result

    def sources(self, name, command):
        """Keep test implementation dependencies separate from unrelated Python tools.

        Package owners and statically imported helpers are included together.
        Dynamic Python loading falls back to all Python sources. Compiled-case
        inputs conservatively retain all mathematical sources and fixtures.
        """
        snapshot = source_snapshot(self.root, self.digests.sha)
        native_stage = str(command[0]).startswith('.lake/build/bin/')
        if not name.startswith('scripts.test.') and not native_stage:
            return snapshot
        selected = set()
        pending = ['scripts.verification.checkpoints', 'scripts.verification.tooling' if not native_stage
                   else 'scripts.verification.completion']
        if name.startswith('scripts.test.'):
            components = name.split('.')
            for stop in range(len(components), 0, -1):
                candidate = '/'.join(components[:stop]) + '.py'
                if candidate in snapshot:
                    pending.append('.'.join(components[:stop]))
                    group_name = candidate
                    break
            else:
                return snapshot
        else:
            group_name = 'native-stage'
        group_key = group_name, identity(snapshot)
        if group_key in self.source_groups:
            return self.source_groups[group_key]
        if name.startswith('scripts.test.'):
            subject = components[2]
            selected.update(path for path in snapshot
                            if path.startswith(('scripts/' + subject + '/', 'scripts/test/' + subject + '/')))
            selected.update(path for path in snapshot if path.endswith('.lean') or path.startswith('test/fixtures/'))
            selected.update(path for path in snapshot if '/' not in path and
                            (path.endswith(('.json', '.toml')) or path == 'lean-toolchain'))
        seen = set()
        dynamic = False
        while pending:
            module = pending.pop()
            if module in seen:
                continue
            seen.add(module)
            pending.extend('.'.join(module.split('.')[:stop]) for stop in range(1, len(module.split('.'))))
            candidates = [module.replace('.', '/') + '.py', module.replace('.', '/') + '/__init__.py']
            path = next((p for p in candidates if p in snapshot), None)
            if path is None:
                continue
            selected.add(path)
            parent = Path(path).parent
            selected.update(p for p in snapshot if Path(p).parent == parent and not p.endswith('.py'))
            tree = ast.parse((self.root / path).read_text(), filename=path)
            package = module.split('.') if path.endswith('/__init__.py') else module.split('.')[:-1]
            for node in ast.walk(tree):
                if isinstance(node, ast.Import):
                    pending.extend(alias.name for alias in node.names)
                elif isinstance(node, ast.ImportFrom):
                    prefix = (package[:len(package) - node.level + 1] if node.level else [])
                    base = '.'.join(prefix + (node.module or '').split('.')).strip('.')
                    pending.append(base)
                    pending.extend(base + '.' + alias.name for alias in node.names)
                elif isinstance(node, ast.Constant) and isinstance(node.value, str):
                    value = node.value
                    if value in snapshot:
                        selected.add(value)
                    if value.endswith('.py'):
                        pending.extend(p[:-3].replace('/', '.') for p in snapshot if
                                       p.endswith('.py') and (p == value or Path(p).name == value))
                elif isinstance(node, ast.Call):
                    target = node.func
                    if isinstance(target, ast.Name) and target.id == '__import__':
                        # These absolute literal imports select the same owners
                        # as ordinary imports. Unknown arguments remain dynamic.
                        keywords = {item.arg: item.value for item in node.keywords}
                        try:
                            imported = ast.literal_eval(node.args[0]) if len(node.args) == 1 else None
                            members = ast.literal_eval(keywords['fromlist']) if 'fromlist' in keywords else ()
                        except (ValueError, TypeError):
                            imported, members = None, None
                        if (isinstance(imported, str) and imported and
                                all(part.isidentifier() for part in imported.split('.')) and
                                set(keywords) <= {'fromlist'} and
                                isinstance(members, (list, tuple)) and
                                all(isinstance(member, str) for member in members)):
                            pending.append(imported)
                            pending.extend(imported + '.' + member for member in members if member != '*')
                        else:
                            dynamic = True
                    elif (isinstance(target, ast.Name) and target.id in ('exec', 'eval') or
                            isinstance(target, ast.Attribute) and target.attr in
                            ('__import__', 'import_module', 'spec_from_file_location', 'run_path', 'run_module')):
                        dynamic = True
        if dynamic:
            selected.update(path for path in snapshot if path.endswith('.py'))
        if any(module.startswith('scripts.toolchain.') for module in seen):
            selected.update(path for path in snapshot if path.startswith('core-toolchain/'))
        result = {path: snapshot[path] for path in selected}
        self.source_groups[group_key] = result
        return result

    def request(self, name, command, *, compiled=None, native=False):
        """Bind the exact command and configuration without retaining secret env values."""
        volatile = {'CCL_COMPLETION_REPORT', 'CCL_CHECK_RESUME', 'FC_SUPPLIED_SESSION_PATH',
                    'FC_SUPPLIED_SESSION_FD', 'PWD', 'OLDPWD', 'SHLVL', '_'}
        env = {k: v for k, v in self.environment.items() if k not in volatile}
        executable = shutil.which(command[0], path=self.environment.get('PATH')) or command[0]
        if not Path(executable).is_absolute():
            executable = self.root / executable
        if compiled is None:
            compiled = not str(command[0]).startswith('.lake/build/bin/')
        groups = {'sources': self.sources(name, command),
                  'compiled': self.compiled() if compiled else None,
                  'native': self.native() if native else None}
        if self.store is not None:
            groups = {name: self.store.request_key(value) for name, value in groups.items()}
        arguments = {}
        for argument in command[1:]:
            if argument.startswith('-'):
                continue
            path = Path(argument)
            if not path.is_absolute():
                path = self.root / path
            if path.is_file():
                arguments[argument] = self.pin(path)
            elif path.is_dir():
                arguments[argument] = self.tree([path])
        return {'schema': 1, 'name': name, 'command': command, 'root': str(self.root),
                'bindings': groups, 'environment': identity(env),
                'arguments': arguments,
                'python_version': sys.version,
                'checkpoint_helper': self.pin(Path(__file__)),
                'affinity': sorted(os.sched_getaffinity(0)) if hasattr(os, 'sched_getaffinity') else None,
                'python': self.executable(sys.executable), 'executable': self.executable(executable),
                'binding_manifests': self.store is not None}


class Checkpoints:
    """Retain successes and immutable output logs independently of run summaries."""

    def __init__(self, directory):
        self.directory = Path(directory)
        self.manifest_stamps = {}
        self.reported_misses = set()

    def index_path(self, request):
        """Locate diagnostic history; this index never authorizes reuse."""
        key = identity([request.get('root'), request['name'], request['command']])
        return self.directory / 'latest' / (key + '.json')

    def explain_miss(self, request):
        """Identify changed input groups when an earlier success is invalidated."""
        current = identity(request)
        if current in self.reported_misses:
            return
        self.reported_misses.add(current)
        try:
            previous = json.loads(self.index_path(request).read_text())['request']
            if not isinstance(previous, str) or len(previous) != 64 or any(c not in '0123456789abcdef' for c in previous):
                raise ValueError('invalid diagnostic checkpoint key')
            old = json.loads((self.directory / 'inputs' / (previous + '.json')).read_text())
            changed = [key for key in request if key != 'bindings' and old.get(key) != request[key]]
            labels = {'sources': 'source dependencies', 'compiled': 'compiled artifacts or SDK',
                      'native': 'native tooling'}
            changed += [labels.get(key, key) for key, value in request.get('bindings', {}).items()
                        if old.get('bindings', {}).get(key) != value]
            if changed:
                print(f"Invalidating {request['name']}: {', '.join(changed)}", flush=True)
        except (OSError, ValueError, KeyError, TypeError):
            pass

    def request_key(self, request):
        """Store a shared immutable input manifest once and return its content key."""
        key = identity(request)
        path = self.directory / 'inputs' / (key + '.json')
        if not path.exists():
            atomic_json(path, request)
        elif self.manifest_stamps.get(key) != Digests.signature(path):
            try:
                valid = json.loads(path.read_text()) == request
            except (OSError, ValueError):
                valid = False
            if not valid:
                print(f'Rebuilding damaged input manifest: {path}', flush=True)
                atomic_json(path, request)
        self.manifest_stamps[key] = Digests.signature(path)
        return key

    def lookup(self, request):
        """Return only a completed success with the exact request and unchanged output."""
        key = identity(request)
        path = self.directory / 'checks' / (key + '.json')
        if not path.exists():
            self.explain_miss(request)
            return None
        try:
            saved = json.loads(path.read_text())
            inputs = self.directory / 'inputs' / (key + '.json')
            if saved['schema'] != 1 or saved['request'] != key or json.loads(inputs.read_text()) != request:
                raise ValueError('input manifest mismatch')
            self.verify_bindings(request)
            result = saved['result']
            if (result['name'] != request['name'] or result['command'] != request['command'] or
                    type(result['exit_code']) is not int or result['exit_code'] != 0 or
                    type(result['raw_exit_code']) is not int or result['raw_exit_code'] != 0 or
                    result['timed_out'] is not False or result.get('errors')):
                raise ValueError('checkpoint is not a completed success')
            if self.directory.resolve() not in Path(result['log']).resolve().parents:
                raise ValueError('output is outside the checkpoint store')
            if digest(result['log']) != saved['log_sha256']:
                raise ValueError('completed output changed')
            return dict(result, reused=True, checkpoint=str(path))
        except (OSError, ValueError, KeyError, TypeError) as error:
            print(f"Invalidating {request['name']}: {error}", flush=True)
            return None

    def verify_bindings(self, request):
        """Verify referenced input manifests without duplicating them per check."""
        if not request.get('binding_manifests'):
            return
        for key in request['bindings'].values():
            if not isinstance(key, str) or len(key) != 64 or any(c not in '0123456789abcdef' for c in key):
                raise ValueError('invalid input manifest key')
            path = self.directory / 'inputs' / (key + '.json')
            stamp = self.manifest_stamps.get(key)
            current = Digests.signature(path)
            if stamp != current:
                if identity(json.loads(path.read_text())) != key:
                    raise ValueError('changed input manifest')
                if current != Digests.signature(path):
                    raise ValueError('input manifest changed while reading')
                self.manifest_stamps[key] = current

    def save(self, request, result):
        """Publish a success only after its caller has validated inputs and cleanup."""
        if (result['name'] != request['name'] or result['command'] != request['command'] or
                type(result['exit_code']) is not int or result['exit_code'] != 0 or
                type(result['raw_exit_code']) is not int or result['raw_exit_code'] != 0 or
                result['timed_out'] is not False or result.get('errors')):
            raise ValueError('cannot checkpoint an unsuccessful or incomplete check')
        self.verify_bindings(request)
        key = self.request_key(request)
        source = Path(result['log'])
        log_digest = digest(source)
        target = self.directory / 'logs' / (log_digest + '.log')
        target.parent.mkdir(parents=True, exist_ok=True)
        with tempfile.NamedTemporaryFile(dir=target.parent, delete=False) as output:
            pending = Path(output.name)
            try:
                with source.open('rb') as input_file:
                    shutil.copyfileobj(input_file, output)
                output.flush()
                os.fsync(output.fileno())
                if digest(pending) != log_digest:
                    raise ValueError('output changed while checkpointing')
                os.replace(pending, target)
            finally:
                pending.unlink(missing_ok=True)
        value = dict(result, log=str(target.resolve()), reused=False)
        atomic_json(self.directory / 'checks' / (key + '.json'),
                    {'schema': 1, 'request': key, 'result': value, 'log_sha256': log_digest})
        atomic_json(self.index_path(request), {'request': key})
