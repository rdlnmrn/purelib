"""Check a compiled theorem body with the pinned official kernel adapter.

This bounded entry point accepts a module name and a theorem in its private
compiled records. It imports that module's dependencies and replays its local
declarations in the original checked environment before inserting the selected
body at its complete compiled type under a fresh name. The optional factory
selectors are controls, not a general expression parser.

Before native insertion, non-Core modules are freshly compiled in dependency
order and compared with the consumed parts. The pinned compiler, Core, plugins
and dynamic libraries are trusted inputs; their hashes are not a proof of
their production or correctness. No saved caller-authored receipt replaces
the live witnesses.

The result distinguishes the raw kernel outcome from provenance. Input hashes
and module resolution are checked before and after the invocation, including
the bytes decoded by the host reader. This is not a source-to-artifact build
certificate, complete environment identity, construction-policy admission, or
a termination proof. Consequently the overall result remains incomplete until
an independently checked provenance contract is supplied.
"""
import argparse
import hashlib
import heapq
import json
import os
from pathlib import Path
import select
import signal
import socket
import struct
import subprocess
import sys
import tempfile
import time

from .compact import InvalidArtifact
from .importer import Graph, Module
from .kernel import Bindings, KernelError, Native, Packets, SuppliedRejection, native_build
from .kernel_replay import replay, text
from .observations import query_observer, name_observer
from .paths import find_olean, render_name, search_path
from scripts.nanoda import artifact_inputs
from scripts.nanoda.artifact_inputs import compiled_inputs, verify_inputs
from scripts.paths import ROOT


def bind_module(binding, module, role):
    """Bind exactly the bytes decoded from each retained module region."""
    binding.module(module, role)
    for region in module.d.parts.regions:
        row = binding.rows[str(region.path.absolute())]
        if row['sha256'] != region.sha256:
            raise InvalidArtifact('decoded region changed before binding: ' + str(region.path))


def closure_producer_plan(inputs, toolchain):
    """Plan source witnesses in dependency order under the guarded Core boundary.

    Planning checks paths and completeness; it is not producer evidence. The
    caller must still run every witness and retain and recheck its inputs.
    """
    guard = Path(toolchain).resolve() / 'MODULE-GUARD.json'
    guard_data = json.loads(guard.read_text())
    core = (Path(guard_data['prefix']).resolve() / 'lib/lean').resolve()
    if not core.is_relative_to((ROOT / '.lake/lake-toolchain').resolve()):
        raise InvalidArtifact('Core is outside the task-local checked frontend')
    nodes = inputs['inventory']['modules']
    by_name = {node['name']: node for node in nodes}
    if len(by_name) != len(nodes) or not nodes:
        raise InvalidArtifact('empty or duplicate import closure')
    dependencies = {}
    consumers = {name: [] for name in by_name}
    project = {}
    core_names = []
    packages = (ROOT / '.lake/packages').resolve()
    for name, node in by_name.items():
        parts = name.split('.')
        if not all(part.isidentifier() for part in parts):
            raise InvalidArtifact('unsupported module name: ' + name)
        if not node['files']:
            raise InvalidArtifact('module has no artifact: ' + name)
        artifact = Path(node['files'][0]).resolve()
        deps = set(node['imports'])
        if not deps.issubset(by_name):
            raise InvalidArtifact('import closure is incomplete: ' + name)
        dependencies[name] = deps
        for dep in deps:
            consumers[dep].append(name)
        core_artifact = (core / Path(*parts)).with_suffix('.olean')
        if core_artifact.is_file() and artifact == core_artifact.resolve():
            core_names.append(name)
            continue
        relative = Path(*parts).with_suffix('.olean')
        suffix = Path('.lake/build/lib/lean') / relative
        roots = [ROOT.resolve(), *(p for p in packages.iterdir() if p.is_dir())]
        matches = [root for root in roots if (root / suffix).resolve() == artifact]
        if len(matches) != 1:
            raise InvalidArtifact('non-Core artifact is outside an owned package: ' + name)
        root = matches[0]
        source = (root / Path(*parts)).with_suffix('.lean')
        setup = (root / '.lake/build/ir' / Path(*parts)).with_suffix('.setup.json')
        if not source.is_file() or not setup.is_file():
            raise InvalidArtifact('missing source or compiler setup: ' + name)
        for path in (artifact, Path(str(artifact) + '.server'),
                     Path(str(artifact) + '.private'), artifact.with_suffix('.ir')):
            if str(path.resolve()) not in inputs['files']:
                raise InvalidArtifact('missing compiled module part: ' + str(path))
        project[name] = {'module': name, 'source': str(source), 'artifact': str(artifact),
                         'setup': str(setup), 'package_root': str(root)}
    ready = [name for name, deps in dependencies.items() if not deps]
    heapq.heapify(ready)
    ordered = []
    while ready:
        name = heapq.heappop(ready)
        if name in project:
            ordered.append(project[name])
        for consumer in consumers[name]:
            dependencies[consumer].remove(name)
            if not dependencies[consumer]:
                heapq.heappush(ready, consumer)
    if any(dependencies.values()) or len(ordered) != len(project):
        raise InvalidArtifact('cyclic import closure')
    return {'core_root': str(core), 'core_modules': sorted(core_names), 'modules': ordered}


def witness_selected(module_name, source, selected, toolchain, inputs, binding, attempt,
                     *, package_root=ROOT, scoped_inputs=None):
    """Freshly compile the selected source and compare its four kernel parts.

    The checked workspace's compiler, setup, plugins and imported artifacts
    remain trusted inputs. Their hashes are bound and rechecked, but this
    operation does not prove that the imported closure was built from source.
    """
    relative = Path(*module_name.split('.'))
    package_root = Path(package_root).resolve()
    package_area = (ROOT / '.lake/packages').resolve()
    if package_root != ROOT.resolve() and package_root.parent != package_area:
        raise InvalidArtifact('module package is outside the task-local workspace')
    expected = (package_root / '.lake/build/lib/lean' / relative).with_suffix('.olean').resolve()
    if selected != expected:
        raise InvalidArtifact('selected artifact is not the checked workspace output')
    setup = (package_root / '.lake/build/ir' / relative).with_suffix('.setup.json')
    binding.add(setup, 'selected-compiler-setup')
    spec = json.loads(setup.read_text())
    if spec.get('name') != module_name or spec.get('isModule') is not True:
        raise InvalidArtifact('compiler setup does not select the requested module')
    if Path(os.environ.get('LEAN_SYSROOT', '')).resolve() != toolchain:
        raise InvalidArtifact('toolchain differs from the selected checked sysroot')
    guard = toolchain / 'MODULE-GUARD.json'
    if not toolchain.is_relative_to((ROOT / '.lake/module-toolchain').resolve()) or not guard.is_file():
        raise InvalidArtifact('toolchain is not a task-local guarded compiler')
    binding.add(guard, 'compiler-guard-receipt')
    guard_data = json.loads(guard.read_text())
    if (not isinstance(guard_data, dict) or not isinstance(guard_data.get('prefix'), str)
            or not isinstance(guard_data.get('compiler'), str)
            or not isinstance(guard_data.get('helpers'), dict)):
        raise InvalidArtifact('invalid compiler guard receipt')
    compiler = Path(guard_data['prefix']).resolve() / 'bin/lean'
    if not compiler.is_relative_to((ROOT / '.lake/lake-toolchain').resolve()):
        raise InvalidArtifact('guard compiler is outside the task-local checked frontend')
    binding.add(compiler, 'guarded-compiler')
    if binding.rows[str(compiler.absolute())]['sha256'] != guard_data['compiler']:
        raise InvalidArtifact('guard compiler differs from its producer receipt')
    binding.add(toolchain / 'bin/lean', 'compiler-guard')
    for path, sha in guard_data['helpers'].items():
        binding.add(path, 'compiler-guard-helper')
        if binding.rows[str(Path(path).absolute())]['sha256'] != sha:
            raise InvalidArtifact('compiler guard helper changed: ' + path)
    for paths in spec.get('importArts', {}).values():
        for path in paths:
            if path is not None and str(Path(path).resolve()) not in inputs['files']:
                raise InvalidArtifact('compiler setup contains an unbound import: ' + path)
    for path in [*spec.get('dynlibs', []), *(p['path'] for p in spec.get('plugins', []))]:
        binding.add(path, 'compiler-plugin')
    def verify_scope():
        if scoped_inputs is None:
            verify_inputs(inputs, [Path(p) for p in attempt['search_path']])
            binding.verify()
            return
        for path in scoped_inputs:
            expected_sha = inputs['files'].get(path)
            if expected_sha is None or artifact_inputs.digest(path) != expected_sha:
                raise InvalidArtifact('changed producer input: ' + path)
        binding.add(source, 'producer-source')
        binding.add(setup, 'producer-setup')
        binding.add(guard, 'compiler-guard-receipt')
        binding.add(compiler, 'guarded-compiler')
        for path in [*spec.get('dynlibs', []), *(p['path'] for p in spec.get('plugins', []))]:
            binding.add(path, 'compiler-plugin')
    verify_scope()
    with tempfile.TemporaryDirectory(prefix='supplied-fresh-source-') as temporary:
        out = Path(temporary) / 'selected.olean'
        command = [str(toolchain / 'bin/lean'), str(source), '-DwarningAsError=true',
                   '--setup', str(setup), '-o', str(out), '-i', str(out.with_suffix('.ilean')),
                   '-c', str(out.with_suffix('.c'))]
        attempt['producer'] = {'command': command, 'exit': None, 'outputs': {}}
        env = {k: v for k, v in os.environ.items() if k not in ('LD_PRELOAD', 'LD_LIBRARY_PATH')}
        env['LEAN_PATH'] = os.pathsep.join(attempt['search_path'])
        process = subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                   env=env, start_new_session=True)
        try:
            stdout, stderr = process.communicate(timeout=120)
        except subprocess.TimeoutExpired:
            try:
                os.killpg(process.pid, signal.SIGTERM)
            except ProcessLookupError:
                pass
            try: stdout, stderr = process.communicate(timeout=15)
            except subprocess.TimeoutExpired:
                try:
                    os.killpg(process.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                stdout, stderr = process.communicate()
            attempt['producer'].update(exit=process.returncode, timeout=True,
                                       stdout=stdout.decode('utf8', 'replace'),
                                       stderr=stderr.decode('utf8', 'replace'))
            raise InvalidArtifact('selected source compiler exceeded its watchdog')
        except BaseException:
            try:
                os.killpg(process.pid, signal.SIGTERM)
            except ProcessLookupError:
                pass
            try:
                process.communicate(timeout=15)
            except subprocess.TimeoutExpired:
                try:
                    os.killpg(process.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                process.communicate()
            raise
        attempt['producer'].update(exit=process.returncode, timeout=False,
                                   stdout=stdout.decode('utf8', 'replace'),
                                   stderr=stderr.decode('utf8', 'replace'))
        if process.returncode or stderr:
            raise InvalidArtifact('fresh selected-source compilation failed')
        for suffix in ('', '.server', '.private', '.ir', '.ilean', '.c'):
            output = Path(str(out) + suffix) if suffix in ('', '.server', '.private') else out.with_suffix(suffix)
            if not output.is_file():
                raise InvalidArtifact('fresh selected source missing output: ' + suffix)
            sha = hashlib.sha256(output.read_bytes()).hexdigest()
            attempt['producer']['outputs'][suffix or '.olean'] = sha
            if suffix in ('', '.server', '.private', '.ir'):
                original = Path(str(selected) + suffix) if suffix != '.ir' else selected.with_suffix('.ir')
                if inputs['files'].get(str(original.resolve())) != sha:
                    raise InvalidArtifact('fresh selected-source output differs: ' + (suffix or '.olean'))
    verify_scope()


def producer_import_scope(item, nodes, ready):
    """Validate a producer setup against the already witnessed named imports."""
    name = item['module']
    node = nodes[name]
    if not set(node['imports']).issubset(ready):
        raise InvalidArtifact('producer dependency is not witnessed: ' + name)
    spec = json.loads(Path(item['setup']).read_text())
    mappings = spec.get('importArts')
    if not isinstance(mappings, dict):
        raise InvalidArtifact('invalid producer import mappings: ' + name)
    scoped = set()
    for imported, paths in mappings.items():
        if imported not in ready or imported not in nodes:
            raise InvalidArtifact('producer setup uses unwitnessed import: ' + imported)
        artifact = Path(nodes[imported]['files'][0]).resolve()
        expected = [artifact, artifact.with_suffix('.ir'), Path(str(artifact) + '.server')]
        if (not isinstance(paths, list) or len(paths) != len(expected)
                or any(not isinstance(path, str) or Path(path).resolve() != target
                       for path, target in zip(paths, expected))):
            raise InvalidArtifact('producer setup has mixed import parts: ' + imported)
        for path in (*expected, Path(str(artifact) + '.private')):
            scoped.add(str(path.resolve()))
    for path in node['files']:
        scoped.add(str(Path(path).resolve()))
    scoped.add(str(Path(item['artifact']).with_suffix('.ir').resolve()))
    return scoped


def witness_producer_sequence(items, core_names, toolchain, inputs, binding, attempt,
                              *, selected_name, selected_source):
    """Compile each supplied import in order, checking its actual setup mappings.

    This helper may witness a prefix for diagnostics. Only a full plan run by
    ``check`` precedes native loading; no saved or caller-authored receipt is
    accepted as a replacement. Core and compiler plugins are trusted inputs.
    """
    nodes = {node['name']: node for node in inputs['inventory']['modules']}
    ready = set(core_names)
    witnesses = attempt.setdefault('closure_witnesses', [])
    for index, item in enumerate(items):
        name = item['module']
        if index % 25 == 0:
            print('supplied producer witness {}/{}: {}'.format(index + 1, len(items), name),
                  file=sys.stderr, flush=True)
        setup = Path(item['setup'])
        binding.add(setup, 'closure-compiler-setup')
        scoped = producer_import_scope(item, nodes, ready)
        child = {'search_path': attempt['search_path']}
        witness = {'module': name, 'producer': None}
        witnesses.append(witness)
        try:
            witness_selected(name, selected_source if name == selected_name else Path(item['source']),
                             Path(item['artifact']), toolchain, inputs, binding, child,
                             package_root=item['package_root'], scoped_inputs=scoped)
        finally:
            witness['producer'] = child.get('producer')
            if name == selected_name:
                attempt['producer'] = witness['producer']
        ready.add(name)


def terminate_with_grace(process):
    """Terminate an owned native process, escalating after fifteen seconds."""
    if process.poll() is None:
        try:
            process.terminate()
        except ProcessLookupError:
            pass
        try:
            process.wait(timeout=15)
        except subprocess.TimeoutExpired:
            try:
                process.kill()
            except ProcessLookupError:
                pass
            process.wait()


def request_bodies(native, index, bodies, recheck, *, controls=None):
    """Check distinct bodies in one live environment, with a watchdog per body."""
    allowed = ('compiled', 'unresolved', 'metavariable', 'loose-index', 'wrong-type')
    if not bodies or any(body not in allowed for body in bodies):
        raise InvalidArtifact('unsupported supplied body selector')
    if len(set(bodies)) != len(bodies):
        raise InvalidArtifact('duplicate supplied body selector')
    if signal.getitimer(signal.ITIMER_REAL) != (0.0, 0.0):
        raise InvalidArtifact('cannot replace an active caller watchdog')
    if controls is None:
        controls = {}
    for body in bodies:
        start = time.monotonic()
        def expired(signum, frame):
            raise TimeoutError('supplied body control exceeded its watchdog: ' + body)
        old_handler = signal.signal(signal.SIGALRM, expired)
        signal.setitimer(signal.ITIMER_REAL, 300)
        try:
            recheck()
            try:
                native.supplied(index, body)
                outcome = {'status': 'accepted', 'raw': 'checked-insertion'}
            except SuppliedRejection as error:
                outcome = {'status': 'rejected', 'raw': str(error)}
            recheck()
            controls[body] = {**outcome, 'seconds': time.monotonic() - start}
        except TimeoutError:
            terminate_with_grace(native.process)
            raise
        finally:
            signal.setitimer(signal.ITIMER_REAL, 0)
            signal.signal(signal.SIGALRM, old_handler)
    return controls


def _send_session(sock, value):
    data = json.dumps(value).encode('utf8')
    if len(data) > 65536:
        raise InvalidArtifact('oversized supplied session frame')
    sock.sendall(struct.pack('<I', len(data)) + data)


def _receive_session(sock):
    def read(size):
        data = bytearray()
        while len(data) < size:
            part = sock.recv(size - len(data))
            if not part:
                raise InvalidArtifact('incomplete supplied session frame')
            data.extend(part)
        return data
    size = struct.unpack('<I', read(4))[0]
    if size > 65536:
        raise InvalidArtifact('oversized supplied session frame')
    return json.loads(read(size).decode('utf8'))


def session_request(fd, body):
    """Request one check from an already owned live producer session."""
    with socket.socket(fileno=os.dup(fd)) as sock:
        sock.settimeout(300)
        _send_session(sock, {'body': body})
        return _receive_session(sock)


def session_request_path(path, body, module, declaration):
    """Request one check through an owned local listening session."""
    with socket.socket(socket.AF_UNIX, socket.SOCK_STREAM) as sock:
        sock.settimeout(300)
        sock.connect(str(path))
        _send_session(sock, {'body': body, 'module': module, 'declaration': declaration})
        return _receive_session(sock)


def _session_step(sock, native_ref, index, recheck, controls, restart, identity=None):
    request = _receive_session(sock)
    keys = {'body'} if identity is None else {'body', 'module', 'declaration'}
    if not isinstance(request, dict) or set(request) != keys:
        raise InvalidArtifact('invalid supplied session request')
    if identity is not None and (request['module'], request['declaration']) != identity:
        raise InvalidArtifact('supplied session selects a different theorem')
    body = request['body']
    if body == 'stop':
        _send_session(sock, {'status': 'stopped'})
        return True
    try:
        if body == 'crash' and restart is not None:
            recheck()
            old = native_ref[0]
            pid = old.process.pid
            old.process.kill()
            try:
                old.supplied(index, 'compiled')
            except (InvalidArtifact, KernelError, BrokenPipeError, OSError) as error:
                reason = type(error).__name__ + ': ' + str(error)
            else:
                raise InvalidArtifact('killed native returned a kernel verdict')
            try:
                old.close()
            except (InvalidArtifact, KernelError, OSError):
                pass
            try:
                old.process.wait(timeout=15)
            except subprocess.TimeoutExpired as error:
                raise InvalidArtifact('killed native was not reaped') from error
            native_ref[0] = None
            recheck()
            native_ref[0] = restart()
            _send_session(sock, {'status': 'incomplete', 'kernel': None,
                                 'reason': reason, 'pid': pid, 'reaped': True})
            return False
        outcome = request_bodies(native_ref[0], index, [body], recheck)[body]
        controls[body] = outcome
        _send_session(sock, {'status': 'incomplete', 'kernel': outcome,
                             'reason': 'complete environment identity is not established'})
        return False
    except Exception as error:
        _send_session(sock, {'status': 'incomplete', 'kernel': None,
                             'reason': type(error).__name__ + ': ' + str(error)})
        raise


def serve_session(fd, native_ref, index, recheck, controls, *, restart=None):
    """Serve bounded checks on an inherited connected socket."""
    with socket.socket(fileno=fd) as sock:
        sock.settimeout(300)
        _send_session(sock, {'status': 'ready'})
        while not _session_step(sock, native_ref, index, recheck, controls, restart):
            pass
    return controls


def serve_listener(fd, ready_fd, native_ref, index, recheck, controls, *, identity, restart=None):
    """Serve serialized clients on an owned listening socket after live preparation."""
    with socket.socket(fileno=fd) as listener:
        if ready_fd is not None:
            os.write(ready_fd, b'R')
            os.close(ready_fd)
        while True:
            connection, _ = listener.accept()
            with connection:
                connection.settimeout(300)
                if _session_step(connection, native_ref, index, recheck, controls, restart, identity):
                    return controls


def check_many(module_name, declaration, source, toolchain, search, cache, bodies, attempt=None,
               *, session_fd=None, listener_fd=None, ready_fd=None, allow_control_crash=False):
    """Return raw kernel outcomes for bodies checked in one witnessed environment.

    Source/build correspondence is not established by hashing source and output
    together. Results therefore retain an incomplete overall status even when
    the kernel accepts or rejects the supplied expression.
    """
    bodies = list(bodies)
    allowed = ('compiled', 'unresolved', 'metavariable', 'loose-index', 'wrong-type')
    if not bodies or any(body not in allowed for body in bodies):
        raise InvalidArtifact('unsupported supplied body selector: ' + str(bodies))
    if len(set(bodies)) != len(bodies):
        raise InvalidArtifact('duplicate supplied body selector: ' + str(bodies))
    if session_fd is not None and listener_fd is not None:
        raise InvalidArtifact('cannot use two supplied session transports')
    if attempt is None:
        attempt = {}
    source = Path(source).resolve()
    toolchain = Path(toolchain).resolve()
    search = [Path(p).resolve() for p in search]
    attempt.update(module=module_name, declaration=declaration, bodies=bodies,
                   source=str(source), toolchain=str(toolchain),
                   search_path=[str(p) for p in search])
    if not source.is_file() or not search:
        raise InvalidArtifact('missing source or empty search path')
    binding = Bindings()
    attempt['bindings'] = binding.rows
    binding.add(source, 'selected-source')
    selected = find_olean(module_name, search).resolve()
    old = Module(module_name, selected, {}, {})
    entries = old.entries(True)
    key = query_observer(declaration)
    matches = [(index, ref) for index, (_, ref, _) in enumerate(entries)
               if name_observer(ref.d, ref.name) == key]
    if len(matches) != 1 or matches[0][1].kind != 2:
        raise InvalidArtifact('expected exactly one compiled theorem: ' + declaration)
    index, ref = matches[0]
    ref.info()  # Validate the entire selected typed record, including its body.
    inputs = compiled_inputs([module_name], search)
    attempt['compiled_inputs'] = inputs
    plan = closure_producer_plan(inputs, toolchain)
    attempt['closure_plan'] = plan
    for item in plan['modules']:
        binding.add(item['source'], 'closure-source')
        binding.add(item['setup'], 'closure-compiler-setup')
    selected_rows = [item for item in plan['modules'] if item['module'] == module_name]
    if len(selected_rows) != 1:
        raise InvalidArtifact('selected module is outside the source closure')
    planned_source = Path(selected_rows[0]['source']).resolve()
    if artifact_inputs.digest(source) != artifact_inputs.digest(planned_source):
        raise InvalidArtifact('selected source differs from the workspace source')
    binding.add(Path(sys.executable).resolve(), 'host-python')
    binding.add(Path(artifact_inputs.__file__).resolve(), 'compiled-input-reader')
    for path in Path(__file__).parent.glob('*.py'):
        binding.add(path, 'host-reader-source')
    binding.add(Path(__file__).with_name('kernel_native.c'), 'native-adapter-source')
    for path, sha in inputs['files'].items():
        binding.add(path, 'compiled-import')
        if binding.rows[str(Path(path).absolute())]['sha256'] != sha:
            raise InvalidArtifact('compiled input changed before binding: ' + path)
    verify_inputs(inputs, search)
    bind_module(binding, old, 'selected-module')
    graph = Graph(search)
    imports = [render_name(c) for c, _, _ in old.imports(True)]
    graph.imports(imports, True)
    for item in graph.modules.values():
        bind_module(binding, item, 'import-private')
    for item in graph.ir.values():
        if item is not None:
            bind_module(binding, item, 'import-ir')
    verify_inputs(inputs, search)
    binding.verify()
    witness_producer_sequence(plan['modules'], plan['core_modules'], toolchain, inputs,
                              binding, attempt, selected_name=module_name, selected_source=source)
    verify_inputs(inputs, search)
    binding.verify()
    # Do not launch even the adapter-build toolchain for a malformed selected
    # record or incomplete import inventory.  This validation is a necessary
    # precondition, not an attestation that arbitrary compact bytes are trusted.
    binary = native_build(toolchain, Path(cache), binding)
    result = {'schema': 1, 'status': 'incomplete', 'kernel': None,
              'reason': 'imported-closure provenance and complete environment identity are not established',
              'module': module_name, 'declaration': declaration, 'bodies': bodies,
              'search_path': [str(p) for p in search], 'source': str(source),
              'compiled_inputs': inputs, 'closure_plan': plan,
              'producer': attempt['producer'], 'closure_witnesses': attempt['closure_witnesses'],
              'inputs': None}
    native_ref = [None]
    try:
        with tempfile.TemporaryDirectory(prefix='supplied-proof-') as directory:
            env = {**os.environ, 'LEAN_PATH': os.pathsep.join(str(p) for p in search)}
            def open_native():
                native = Native(binary, selected, selected, toolchain, env)
                native_ref[0] = native
                native.call(2)
                packets = Packets(native, old.d.parts.regions[0].data[:96], Path(directory))
                writer = packets.begin()
                actions, groups, quotients = replay(old, writer)
                slot = packets.publish(writer, groups=groups, quotients=quotients)
                for kind, action_index, name in actions:
                    if kind == 'O': native.add(0, action_index, 0, name)
                    elif kind == 'G': native.add(slot + 2, action_index, 2, name)
                    elif kind == 'Q': native.add(slot + 2, action_index, 3, name)
                    else: native.compare(6 if kind == 'C' else 7, action_index, name)
                return native
            native_ref[0] = open_native()
            def recheck():
                verify_inputs(inputs, search)
                binding.verify()
            attempt['controls'] = {}
            if session_fd is None and listener_fd is None:
                result['controls'] = request_bodies(native_ref[0], index, bodies, recheck,
                                                    controls=attempt['controls'])
            elif session_fd is not None:
                result['controls'] = serve_session(session_fd, native_ref, index, recheck,
                                                   attempt['controls'],
                                                   restart=open_native if allow_control_crash else None)
            else:
                result['controls'] = serve_listener(listener_fd, ready_fd, native_ref, index, recheck,
                                                    attempt['controls'],
                                                    identity=(module_name, declaration),
                                                    restart=open_native if allow_control_crash else None)
    finally:
        primary = sys.exc_info()[1]
        cleanup_errors = []
        actions = ([native_ref[0].close] if native_ref[0] is not None else []) + [
            lambda: verify_inputs(inputs, search), binding.verify]
        for action in actions:
            try:
                action()
            except Exception as error:
                cleanup_errors.append(type(error).__name__ + ': ' + str(error))
        if cleanup_errors:
            attempt['cleanup_errors'] = cleanup_errors
            if primary is None:
                raise InvalidArtifact('cleanup/currentness failure: ' + '; '.join(cleanup_errors))
            primary.add_note('cleanup/currentness failures: ' + '; '.join(cleanup_errors))
    result['inputs'] = list(binding.rows.values())
    return result


def check(module_name, declaration, source, toolchain, search, cache, body='compiled', attempt=None):
    """Check one supplied body through the same live-witnessed operation."""
    result = check_many(module_name, declaration, source, toolchain, search, cache, [body], attempt)
    result['body'] = body
    result['kernel'] = result['controls'][body]
    return result


def supervise_session(module, declaration, source, toolchain, cache, receipt, command, *,
                      allow_control_crash=False, on_ready=None):
    """Run a command with one owned live session available to isolated children.

    The command receives a private socket path. The session always witnesses its
    own inputs; the existing receipt is output only and is never used as authority.
    """
    from scripts.verification.processes import live_owned, observe, process_record, process_table, stop_tree
    if not command:
        raise InvalidArtifact('empty supervised session command')
    children = []
    def track(process):
        record = process_record(process.pid)
        if record is None:
            if process.poll() is None:
                process.terminate()
                try:
                    process.wait(timeout=15)
                except subprocess.TimeoutExpired:
                    process.kill()
                    process.wait()
            raise InvalidArtifact('missing supervised process identity')
        known = {process.pid: record[0]}
        children.append((process, known))
        return known
    previous = signal.getsignal(signal.SIGTERM)
    def interrupted(signum, frame):
        raise KeyboardInterrupt('supervised session interrupted')
    signal.signal(signal.SIGTERM, interrupted)
    try:
        with tempfile.TemporaryDirectory(prefix='supplied-listener-') as directory:
            path = Path(directory) / 'session.sock'
            with socket.socket(socket.AF_UNIX, socket.SOCK_STREAM) as listener:
                listener.bind(str(path))
                os.chmod(path, 0o600)
                listener.listen(16)
                ready_read, ready_write = os.pipe()
                try:
                    argv = [sys.executable, '-m', 'scripts.lean_module_data.supplied', module, declaration,
                            '--source', str(source), '--toolchain', str(toolchain), '--cache', str(cache),
                            '--receipt', str(receipt), '--listen-fd', str(listener.fileno()),
                            '--ready-fd', str(ready_write)]
                    if allow_control_crash:
                        argv.append('--allow-control-crash')
                    server = subprocess.Popen(argv, pass_fds=(listener.fileno(), ready_write), start_new_session=True)
                    server_known = track(server)
                    os.close(ready_write)
                    ready_write = None
                    while True:
                        observe(server, server_known, process_table())
                        if select.select([ready_read], [], [], .25)[0]:
                            if os.read(ready_read, 1) != b'R':
                                raise InvalidArtifact('session producer exited before readiness')
                            break
                        if server.poll() is not None:
                            raise InvalidArtifact('session producer exited before readiness')
                    if on_ready is not None:
                        on_ready()
                    env = {**os.environ, 'FC_SUPPLIED_SESSION_PATH': str(path)}
                    env.pop('FC_SUPPLIED_SESSION_FD', None)
                    worker = subprocess.Popen(command, env=env, start_new_session=True)
                    worker_known = track(worker)
                    while worker.poll() is None:
                        table = process_table()
                        observe(server, server_known, table)
                        observe(worker, worker_known, table)
                        time.sleep(.1)
                    worker_code = worker.wait()
                    stopped = session_request_path(path, 'stop', module, declaration)
                    if stopped != {'status': 'stopped'}:
                        raise InvalidArtifact('invalid session shutdown response')
                    server_code = server.wait(timeout=300)
                    if server_code != 2:
                        raise InvalidArtifact('session producer exited unexpectedly: ' + str(server_code))
                    result = json.loads(Path(receipt).read_text())
                    if result.get('status') != 'incomplete' or not result.get('closure_witnesses'):
                        raise InvalidArtifact('session producer receipt is incomplete or missing')
                    return worker_code if worker_code >= 0 else 128 - worker_code
                finally:
                    os.close(ready_read)
                    if ready_write is not None:
                        os.close(ready_write)
    finally:
        for process, known in reversed(children):
            observe(process, known, process_table())
            if process.poll() is None or live_owned(known):
                stop_tree(process, known, 15)
        signal.signal(signal.SIGTERM, previous)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('module')
    parser.add_argument('declaration')
    parser.add_argument('--source', type=Path, required=True)
    parser.add_argument('--toolchain', type=Path, required=True)
    parser.add_argument('--cache', type=Path, required=True)
    parser.add_argument('--body', default='compiled')
    parser.add_argument('--controls', action='store_true', help='check the compiled body and four factory controls')
    parser.add_argument('--serve-fd', type=int, help='serve requests on an inherited owned socket')
    parser.add_argument('--listen-fd', type=int, help='serve clients on an inherited owned listening socket')
    parser.add_argument('--ready-fd', type=int, help='signal readiness on an inherited pipe')
    parser.add_argument('--allow-control-crash', action='store_true', help='allow the native-crash control in a session')
    parser.add_argument('--supervise', nargs=argparse.REMAINDER, help='run a command using one live session')
    parser.add_argument('--receipt', type=Path, required=True)
    args = parser.parse_args(argv)
    if args.supervise is not None:
        try:
            return supervise_session(args.module, args.declaration, args.source, args.toolchain,
                                     args.cache, args.receipt, args.supervise,
                                     allow_control_crash=args.allow_control_crash)
        except (InvalidArtifact, KernelError, OSError, ValueError, MemoryError, KeyboardInterrupt,
                subprocess.SubprocessError) as error:
            print(json.dumps({'status': 'incomplete', 'kernel': None,
                              'reason': type(error).__name__ + ': ' + str(error)}))
            return 2
    if args.receipt.resolve() == args.source.resolve():
        print('receipt cannot replace its source', file=sys.stderr)
        return 2
    attempt = {'module': args.module, 'declaration': args.declaration, 'body': args.body,
               'source': str(args.source), 'toolchain': str(args.toolchain)}
    try:
        if args.controls or args.serve_fd is not None or args.listen_fd is not None:
            result = check_many(args.module, args.declaration, args.source, args.toolchain,
                                search_path(), args.cache,
                                ('compiled', 'unresolved', 'metavariable', 'loose-index', 'wrong-type'), attempt,
                                session_fd=args.serve_fd, listener_fd=args.listen_fd,
                                ready_fd=args.ready_fd, allow_control_crash=args.allow_control_crash)
        else:
            result = check(args.module, args.declaration, args.source, args.toolchain,
                           search_path(), args.cache, args.body, attempt)
    except (InvalidArtifact, KernelError, OSError, ValueError, MemoryError,
            subprocess.SubprocessError) as error:
        result = {'schema': 1, 'status': 'incomplete', 'kernel': None,
                  'reason': type(error).__name__ + ': ' + str(error), **attempt}
    pending = args.receipt.with_name(args.receipt.name + '.partial')
    protected = {Path(row).resolve() for row in attempt.get('bindings', {})}
    protected.update(Path(row).resolve() for row in attempt.get('compiled_inputs', {}).get('files', {}))
    protected.add(args.source.resolve())
    if args.receipt.resolve() in protected or pending.resolve() in protected:
        print('receipt cannot replace an input', file=sys.stderr)
        return 2
    args.receipt.parent.mkdir(parents=True, exist_ok=True)
    with pending.open('w') as output:
        json.dump(result, output, indent=2)
        output.write('\n')
    pending.replace(args.receipt)
    print(json.dumps({key: result[key] for key in ('status', 'kernel', 'reason', 'controls') if key in result}))
    return 2  # No complete source-to-artifact provenance certificate yet.


if __name__ == '__main__':
    sys.exit(main())
