#!/usr/bin/env python3
"""Replay a nonempty, content-bound original kernel CLI regression inventory."""
import argparse,base64,hashlib,json,os,subprocess,sys
from pathlib import Path
from scripts.paths import ROOT

def sha(path):
    with Path(path).open('rb') as source:return hashlib.file_digest(source,'sha256').hexdigest()

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('manifest',type=Path);parser.add_argument('--toolchain',type=Path,required=True)
    parser.add_argument('--cache',type=Path,required=True);parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args();data=json.loads(args.manifest.read_text())
    if data.get('schema')!=1 or not data.get('cases') or not data.get('inputs'):raise ValueError('empty or malformed kernel fixture inventory')
    for row in data['inputs']:
        path=Path(row['path']);now=sha(path) if path.exists() else None
        if now!=row['sha256']:raise ValueError('stale or missing genuine fixture input: '+str(path))
    cases=data['cases'];names=[r['case'] for r in cases]
    if len(names)!=len(set(names)):raise ValueError('duplicate kernel fixture identity')
    args.output.mkdir(parents=True,exist_ok=True);results=[]
    for i,row in enumerate(cases):
        env=os.environ.copy();env['LEAN_PATH']=row['lean_path'];env['PATH']=str(args.toolchain/'bin')+os.pathsep+env.get('PATH','')
        receipt=args.output/(str(i)+'.binding.json')
        command=[sys.executable,str(ROOT/'scripts/project-module-data.py'),'type-equivalence',*row['arguments'],'--toolchain',str(args.toolchain),'--kernel-cache',str(args.cache),'--receipt',str(receipt)]
        result=subprocess.run(command,env=env,capture_output=True)
        (args.output/(str(i)+'.stdout')).write_bytes(result.stdout);(args.output/(str(i)+'.stderr')).write_bytes(result.stderr)
        expected_out=base64.b64decode(row['stdout_base64'],validate=True);expected_err=base64.b64decode(row['stderr_base64'],validate=True)
        same=result.returncode==row['exit'] and result.stdout==expected_out and result.stderr==expected_err
        results.append({'case':row['case'],'exact':same,'exit':result.returncode,'command':command,'receipt':str(receipt)})
        (args.output/'results.json').write_text(json.dumps(results,indent=2)+'\n')
        if not same:raise ValueError('kernel CLI regression: '+row['case'])
    print(str(len(results))+' exact original kernel CLI controls PASS')

if __name__=='__main__':
    try:main()
    except (ValueError,OSError) as error:print(str(error),file=sys.stderr);sys.exit(1)


# Discovery runs real current fixtures; the CLI above remains the explicit
# manifest control and is also invoked below so discovery cannot silently omit it.
import unittest
from unittest.mock import patch


class KernelFixtureTests(unittest.TestCase):
    """Exercise official-kernel acceptance, rejection and exact CLI transport."""

    def test_supervised_live_fixture_with_isolated_worker(self):
        """The owned launcher prepares a real fixture and reaps it after client checks."""
        self.check_supervised_live_fixture()

    def test_live_readiness_callback_precedes_checked_client_requests(self):
        """The readiness hook runs after producer witnessing and before the client."""
        self.check_supervised_live_fixture(readiness_callback=True)

    def check_supervised_live_fixture(self, *, crash=False, readiness_callback=False):
        """Run a real small production session, optionally crashing and reopening it."""
        import tempfile
        from scripts.lean_module_data.paths import find_olean, search_path
        toolchain = Path(os.environ['LEAN_SYSROOT']).resolve()
        search = search_path()
        init = find_olean('Init', search).resolve()
        with tempfile.TemporaryDirectory(prefix='supplied-launch-', dir=ROOT / '.lake/packages') as temporary:
            package = Path(temporary)
            source = package / 'SuppliedLaunchFixture.lean'
            source.write_text('module\npublic import Init\npublic section\n'
                              'theorem suppliedLaunchFixture : True := True.intro\n')
            artifact = package / '.lake/build/lib/lean/SuppliedLaunchFixture.olean'
            setup = package / '.lake/build/ir/SuppliedLaunchFixture.setup.json'
            artifact.parent.mkdir(parents=True)
            setup.parent.mkdir(parents=True)
            setup.write_text(json.dumps({'name': 'SuppliedLaunchFixture', 'isModule': True,
                                         'package': 'supplied-launch-fixture', 'options': {},
                                         'importArts': {'Init': [str(init), str(init.with_suffix('.ir')),
                                                                 str(init) + '.server']},
                                         'plugins': [], 'dynlibs': []}))
            env = {**os.environ, 'LEAN_PATH': str(artifact.parent) + os.pathsep + os.environ['LEAN_PATH']}
            compile_command = [str(toolchain / 'bin/lean'), str(source), '-DwarningAsError=true',
                               '--setup', str(setup), '-o', str(artifact),
                               '-i', str(artifact.with_suffix('.ilean')), '-c', str(artifact.with_suffix('.c'))]
            result = subprocess.run(compile_command, env=env, capture_output=True, text=True, timeout=300)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            receipt = package / 'receipt.json'
            client = ("import os; from scripts.lean_module_data.supplied import session_request_path; "
                      "p=os.environ['FC_SUPPLIED_SESSION_PATH']; "
                      "a=session_request_path(p,'compiled','SuppliedLaunchFixture','suppliedLaunchFixture'); "
                      "b=session_request_path(p,'unresolved','SuppliedLaunchFixture','suppliedLaunchFixture'); "
                      "print(a,b); assert a['kernel']['status']=='accepted' and b['kernel']['status']=='rejected'; ")
            if crash:
                client += ("from scripts.nanoda.processes import process_record; "
                           "c=session_request_path(p,'crash','SuppliedLaunchFixture','suppliedLaunchFixture'); "
                           "print('native-crash incomplete:',c,flush=True); "
                           "assert c['status']=='incomplete' and c['kernel'] is None and c['reason']; "
                           "assert c['reaped'] and process_record(c['pid'],live=True) is None; "
                           "d=session_request_path(p,'compiled','SuppliedLaunchFixture','suppliedLaunchFixture'); "
                           "print('native-restarted:',d,flush=True); assert d['kernel']['status']=='accepted'")
            command = [sys.executable, '-m', 'scripts.lean_module_data.supplied',
                       'SuppliedLaunchFixture', 'suppliedLaunchFixture', '--source', str(source),
                       '--toolchain', str(toolchain), '--cache', str(ROOT / '.lake/kernel-replay-tests'),
                       '--receipt', str(receipt)]
            if crash:
                command.append('--allow-control-crash')
            command += ['--supervise', sys.executable, '-c', client]
            if readiness_callback:
                marker = package / 'producer-ready'
                guarded_client = f'from pathlib import Path; assert Path({str(marker)!r}).read_text()=="ready"; ' + client
                arguments = {'source': str(source), 'toolchain': str(toolchain),
                             'cache': str(ROOT / '.lake/kernel-replay-tests'), 'receipt': str(receipt),
                             'marker': str(marker), 'command': [sys.executable, '-c', guarded_client]}
                launcher = ("import json,sys; from pathlib import Path; "
                            "from scripts.lean_module_data.supplied import supervise_session; "
                            "a=json.loads(sys.argv[1]); "
                            "sys.exit(supervise_session('SuppliedLaunchFixture','suppliedLaunchFixture',"
                            "Path(a['source']),Path(a['toolchain']),Path(a['cache']),Path(a['receipt']),"
                            "a['command'],on_ready=lambda:Path(a['marker']).write_text('ready')))")
                command = [sys.executable, '-c', launcher, json.dumps(arguments)]
            result = subprocess.run(command, env=env, capture_output=True, text=True, timeout=300)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            if crash:
                print(result.stdout, end='', flush=True)
            outcome = json.loads(receipt.read_text())
            self.assertEqual(outcome['status'], 'incomplete')
            self.assertEqual(len(outcome['closure_witnesses']), 1)
            self.assertEqual(outcome['controls']['compiled']['status'], 'accepted')
            self.assertEqual(outcome['controls']['unresolved']['status'], 'rejected')
            # Exercise the ordinary class-owned session setup with a real
            # compiled fixture before the expensive actual-Horner preparation.
            from scripts.lean_module_data.supplied import session_request_path
            class FixtureSession(SuppliedHornerTests):
                """An independently owned small instance of the production session."""
            with patch.dict(os.environ, env, clear=True):
                try:
                    FixtureSession.prepare_session('SuppliedLaunchFixture', 'suppliedLaunchFixture',
                                                   source, toolchain, ROOT / '.lake/kernel-replay-tests')
                    checked = session_request_path(FixtureSession.session_path, 'compiled',
                                                   'SuppliedLaunchFixture', 'suppliedLaunchFixture')
                    self.assertEqual(checked['kernel']['status'], 'accepted')
                finally:
                    FixtureSession.doClassCleanups()
                    self.assertFalse(FixtureSession.tearDown_exceptions)

    def test_compiled_body_insertion_uses_native_service(self):
        """Check a compiled proof body, not a constant referring to the theorem."""
        import tempfile
        import select
        import signal
        import socket
        from scripts.lean_module_data.importer import Module
        from scripts.lean_module_data.compact import InvalidArtifact
        from scripts.lean_module_data.kernel import Bindings, Native, native_build
        from scripts.lean_module_data.kernel_replay import text
        from scripts.lean_module_data.supplied import (
            _receive_session, request_bodies, serve_listener, serve_session,
            session_request, session_request_path,
        )

        runner = ROOT / 'scripts/run-lake.sh'
        toolchain = Path(subprocess.check_output([str(runner), 'env', 'lean', '--print-prefix'],
                                                cwd=ROOT, text=True).strip())
        lean_path = subprocess.check_output([str(runner), 'env', 'printenv', 'LEAN_PATH'],
                                            cwd=ROOT, text=True).strip()
        with tempfile.TemporaryDirectory(prefix='supplied-body-') as temporary:
            work = Path(temporary)
            source = work / 'SuppliedFixture.lean'
            source.write_text('module\npublic import Init\npublic section\n'
                              'theorem suppliedFixture : True := True.intro\n')
            artifact = source.with_suffix('.olean')
            compiled = subprocess.run([str(toolchain / 'bin/lean'), '-R', str(work),
                                       '-DwarningAsError=true', '-o', str(artifact), str(source)],
                                      env={**os.environ, 'LEAN_PATH': lean_path},
                                      capture_output=True, timeout=300)
            self.assertEqual(compiled.returncode, 0, (compiled.stdout + compiled.stderr).decode())
            module = Module('SuppliedFixture', artifact, {}, {})
            matches = [i for i, (_, ref, _) in enumerate(module.entries(True))
                       if text(ref) == 'suppliedFixture' and ref.kind == 2]
            self.assertEqual(len(matches), 1)
            binary = native_build(toolchain, ROOT / '.lake/kernel-replay-tests', Bindings())
            native = Native(binary, artifact, artifact, toolchain,
                            {**os.environ, 'LEAN_PATH': lean_path})
            try:
                native.call(2)
                inputs = Bindings()
                inputs.add(source, 'source')
                for suffix in ('', '.server', '.private'):
                    inputs.add(str(artifact) + suffix, 'compiled-part')
                controls = request_bodies(native, matches[0],
                                          ('compiled', 'unresolved', 'metavariable',
                                           'loose-index', 'wrong-type'), inputs.verify)
                self.assertEqual(controls['compiled']['status'], 'accepted')
                for body in ('unresolved', 'metavariable', 'loose-index', 'wrong-type'):
                    with self.subTest(body=body):
                        self.assertEqual(controls[body]['status'], 'rejected')
                        self.assertTrue(controls[body]['raw'])
                source.write_text(source.read_text() + '\n-- changed after binding\n')
                with self.assertRaisesRegex(InvalidArtifact, 'changed invocation input'):
                    request_bodies(native, matches[0], ('compiled',), inputs.verify)
            finally:
                native.close()
            client, server = socket.socketpair()
            pid = os.fork()
            if pid == 0:
                client.close()
                os.setsid()
                child_native = [None]
                try:
                    def open_child_native():
                        child_native[0] = Native(binary, artifact, artifact, toolchain,
                                                 {**os.environ, 'LEAN_PATH': lean_path})
                        child_native[0].call(2)
                        return child_native[0]
                    open_child_native()
                    child_inputs = Bindings()
                    child_inputs.add(source, 'source')
                    serve_session(server.detach(), child_native, matches[0], child_inputs.verify, {},
                                  restart=open_child_native)
                    code = 0
                except Exception:
                    code = 3
                finally:
                    if child_native[0] is not None:
                        child_native[0].close()
                os._exit(code)
            server.close()
            client.settimeout(120)
            try:
                self.assertEqual(_receive_session(client), {'status': 'ready'})
                first = session_request(client.fileno(), 'compiled')
                self.assertEqual(first['kernel']['status'], 'accepted')
                second = session_request(client.fileno(), 'unresolved')
                self.assertEqual(second['kernel']['status'], 'rejected')
                crash = session_request(client.fileno(), 'crash')
                self.assertEqual(crash['status'], 'incomplete')
                self.assertIsNone(crash['kernel'])
                self.assertTrue(crash['reaped'])
                self.assertTrue(crash['reason'])
                restarted = session_request(client.fileno(), 'compiled')
                self.assertEqual(restarted['kernel']['status'], 'accepted')
                source.write_text(source.read_text() + '\n-- changed during session\n')
                changed = session_request(client.fileno(), 'compiled')
                self.assertEqual(changed['status'], 'incomplete')
                self.assertIsNone(changed['kernel'])
                self.assertIn('changed invocation input', changed['reason'])
                _, code = os.waitpid(pid, 0)
                pid = None
                self.assertEqual(os.waitstatus_to_exitcode(code), 3)
            finally:
                client.close()
                if pid is not None:
                    try:
                        os.killpg(pid, signal.SIGKILL)
                    except ProcessLookupError:
                        pass
                    os.waitpid(pid, 0)
            # Stock tooling workers close inherited descriptors, so verify the
            # listener using two actual isolated workers, not inherited sockets.
            from scripts.verification.tooling import run_jobs
            listener = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
            listener_path = work / 'fixture.sock'
            listener.bind(str(listener_path))
            listener.listen(8)
            ready_read, ready_write = os.pipe()
            pid = os.fork()
            if pid == 0:
                os.close(ready_read)
                os.setsid()
                child_native = None
                try:
                    child_native = Native(binary, artifact, artifact, toolchain,
                                          {**os.environ, 'LEAN_PATH': lean_path})
                    child_native.call(2)
                    child_inputs = Bindings()
                    child_inputs.add(source, 'source')
                    serve_listener(listener.detach(), ready_write, [child_native], matches[0],
                                   child_inputs.verify, {}, identity=('SuppliedFixture', 'suppliedFixture'))
                    code = 0
                except Exception:
                    code = 3
                finally:
                    if child_native is not None:
                        child_native.close()
                os._exit(code)
            listener.close()
            os.close(ready_write)
            try:
                self.assertTrue(select.select([ready_read], [], [], 120)[0])
                self.assertEqual(os.read(ready_read, 1), b'R')
                code = ("import os; from scripts.lean_module_data.supplied import session_request_path; "
                        "r=session_request_path(os.environ['SUPPLIED_FIXTURE_PATH'], %r, "
                        "'SuppliedFixture', 'suppliedFixture'); print(r); "
                        "assert r['kernel']['status']==%r")
                jobs = [(body, [sys.executable, '-c', code % (body, expected)], 2 * 1024**3)
                        for body, expected in (('compiled', 'accepted'), ('unresolved', 'rejected'))]
                with patch.dict(os.environ, {'SUPPLIED_FIXTURE_PATH': str(listener_path)}):
                    self.assertEqual(run_jobs(jobs, work / 'listener-cases', 2, 4 * 1024**3), 0)
                self.assertEqual(session_request_path(listener_path, 'stop', 'SuppliedFixture',
                                                      'suppliedFixture'), {'status': 'stopped'})
                _, status = os.waitpid(pid, 0)
                pid = None
                self.assertEqual(os.waitstatus_to_exitcode(status), 0)
            finally:
                os.close(ready_read)
                if pid is not None:
                    try:
                        os.killpg(pid, signal.SIGKILL)
                    except ProcessLookupError:
                        pass
                    os.waitpid(pid, 0)

    def test_current_fixture_manifest_and_changed_type_rejection(self):
        runner = ROOT / 'scripts/run-lake.sh'
        toolchain = Path(subprocess.check_output([str(runner), 'env', 'lean', '--print-prefix'],
                                                cwd=ROOT, text=True).strip())
        lean_path = subprocess.check_output([str(runner), 'env', 'printenv', 'LEAN_PATH'],
                                            cwd=ROOT, text=True).strip()
        import tempfile
        with tempfile.TemporaryDirectory(prefix='kernel-replay-fixtures-') as temporary:
            work = Path(temporary)
            artifacts = []
            for stage, changed in [('before', False), ('after', True)]:
                directory = work / stage
                directory.mkdir()
                source = directory / 'KernelReplay.lean'
                source.write_text('module\npublic import Init\npublic section\n'
                                  'namespace KernelReplayFixture\n'
                                  '@[expose] def value : Nat := 7\n'
                                  'theorem identity : value = 7 := rfl\n'
                                  + ('def changedType : Bool := true\n' if changed else
                                     'def changedType : Nat := 1\n')
                                  + 'end KernelReplayFixture\n')
                artifact = source.with_suffix('.olean')
                compiled = subprocess.run([str(toolchain / 'bin/lean'), '-R', str(directory),
                                '-DwarningAsError=true', '-o', str(artifact), str(source)],
                               env={**os.environ, 'LEAN_PATH': lean_path},
                               capture_output=True)
                self.assertEqual(compiled.returncode, 0, (compiled.stdout + compiled.stderr).decode())
                artifacts.append(artifact)
            prefix = [str(artifact) for artifact in artifacts]
            cases = [
                {'case': 'equal-complete-types', 'arguments': [*prefix, 'KernelReplayFixture.value',
                                                              'KernelReplayFixture.identity'],
                 'exit': 0, 'stdout_base64': base64.b64encode(
                     b'kernel-defeq\tKernelReplayFixture.value\nkernel-defeq\tKernelReplayFixture.identity\n').decode(),
                 'stderr_base64': ''},
                {'case': 'missing-selected-name', 'arguments': [*prefix, 'KernelReplayFixture.missing'],
                 'exit': 1, 'stdout_base64': '', 'stderr_base64': base64.b64encode(
                     b'uncaught exception: expected one declaration named KernelReplayFixture.missing, found 0\n').decode()},
            ]
            for case in cases:
                case['lean_path'] = lean_path
            inputs = [{'path': str(path), 'sha256': sha(path)}
                      for directory in (work / 'before', work / 'after')
                      for path in directory.iterdir() if path.is_file()]
            manifest = work / 'manifest.json'
            manifest.write_text(json.dumps({'schema': 1, 'inputs': inputs, 'cases': cases}))
            cache = ROOT / '.lake/kernel-replay-tests'
            argv = [__file__, str(manifest), '--toolchain', str(toolchain),
                    '--cache', str(cache), '--output', str(work / 'results')]
            with patch.object(sys, 'argv', argv):
                main()
            self.assertEqual(len(json.loads((work / 'results/results.json').read_text())), 2)
            command = [sys.executable, str(ROOT / 'scripts/project-module-data.py'), 'type-equivalence',
                       *prefix, 'KernelReplayFixture.changedType', '--toolchain', str(toolchain),
                       '--kernel-cache', str(cache), '--receipt', str(work / 'rejected.json')]
            result = subprocess.run(command, env={**os.environ, 'LEAN_PATH': lean_path}, capture_output=True)
            self.assertEqual(result.returncode, 1)
            self.assertIn(b'type mismatch', result.stderr)
            self.assertIn(b'Nat', result.stderr)
            self.assertIn(b'Bool', result.stderr)
            self.assertEqual(json.loads((work / 'rejected.json').read_text())['status'], 'failed')


class SuppliedHornerTests(unittest.TestCase):
    """Check the actual locally built E theorem through the supplied operation."""

    @classmethod
    def setUpClass(cls):
        cls.toolchain = Path(os.environ['LEAN_SYSROOT'])
        cls.source = ROOT / 'Purelib/Approximation/Gaussian/Exponential/E.lean'
        cls.cache = ROOT / '.lake/kernel-replay-tests'
        cls.session_path = os.environ.get('FC_SUPPLIED_SESSION_PATH')
        cls.session_fd = os.environ.get('FC_SUPPLIED_SESSION_FD')
        if cls.session_path is not None or cls.session_fd is not None:
            return
        cls.prepare_session('Purelib.Approximation.Gaussian.Exponential.E',
                            'Purelib.Approximation.Gaussian.Exponential.E.horner_sample_eq_factorial',
                            cls.source, cls.toolchain, cls.cache)

    @classmethod
    def prepare_session(cls, module, declaration, source, toolchain, cache):
        """Own one live production session through class cleanup."""
        # Class preparation is an aggregate of individually guarded module
        # compilations. Each actual body request retains its own 300s watchdog.
        # Use the production supervisor even for the exact ordinary unittest
        # command, rather than silently recompiling the closure in every test.
        import select
        import tempfile
        from scripts.verification.processes import live_owned, observe, process_record, process_table, stop_tree

        temporary = tempfile.TemporaryDirectory(prefix='supplied-horner-suite-')
        directory = Path(temporary.name)
        receipt = directory / 'receipt.json'
        client = ("import json,os,sys; "
                  "print(json.dumps({'session':os.environ['FC_SUPPLIED_SESSION_PATH']}),flush=True); "
                  "assert sys.stdin.buffer.read(1)==b'\\n'")
        command = [sys.executable, '-m', 'scripts.lean_module_data.supplied', module,
                   declaration, '--source', str(source),
                   '--toolchain', str(toolchain), '--cache', str(cache),
                   '--receipt', str(receipt), '--supervise', sys.executable, '-c', client]
        try:
            process = subprocess.Popen(command, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                       text=True, start_new_session=True)
        except BaseException:
            temporary.cleanup()
            raise
        identity = process_record(process.pid)
        if identity is None:
            try:
                process.terminate()
                try:
                    process.wait(timeout=15)
                except subprocess.TimeoutExpired:
                    process.kill()
                    process.wait()
            finally:
                process.stdin.close()
                process.stdout.close()
                temporary.cleanup()
            raise AssertionError('Horner preparation supervisor identity is unavailable')
        known = {process.pid: identity[0]}

        def close_session():
            try:
                output, _ = process.communicate(input='\n', timeout=300)
                if process.returncode != 0:
                    raise AssertionError('Horner session failed: ' + output)
                result = json.loads(receipt.read_text())
                if (result.get('status') != 'incomplete' or not result.get('closure_witnesses')
                        or any(row['producer']['exit'] != 0 or row['producer']['timeout']
                               for row in result['closure_witnesses'])):
                    raise AssertionError('Horner session lacks complete live producer witnesses')
                print('horner-session-receipt ' + json.dumps(result, sort_keys=True), flush=True)
            finally:
                observe(process, known, process_table())
                if process.poll() is None or live_owned(known):
                    stop_tree(process, known, 15)
                process.stdin.close()
                process.stdout.close()
                temporary.cleanup()

        cls.addClassCleanup(close_session)
        while True:
            observe(process, known, process_table())
            if select.select([process.stdout], [], [], .25)[0]:
                ready = process.stdout.readline()
                if not ready:
                    raise AssertionError('Horner producer exited before session readiness')
                cls.session_path = json.loads(ready)['session']
                break
            if process.poll() is not None:
                raise AssertionError('Horner producer exited before session readiness')
        print('horner-session ready after live producer preparation', flush=True)

    def check_body(self, body, expected):
        from scripts.lean_module_data.supplied import session_request, session_request_path
        module = 'Purelib.Approximation.Gaussian.Exponential.E'
        declaration = module + '.horner_sample_eq_factorial'
        if self.session_path is not None:
            result = session_request_path(self.session_path, body, module, declaration)
        else:
            result = session_request(int(self.session_fd), body)
        self.assertEqual(result['status'], 'incomplete')
        self.assertEqual(result['kernel']['status'], expected)
        self.assertTrue(result['kernel']['raw'])
        print('supplied-control ' + body + ' ' + json.dumps(result['kernel'], sort_keys=True), flush=True)

    def test_actual_horner_supplied_body(self):
        self.check_body('compiled', 'accepted')

    def test_supplied_unresolved_constant_reaches_kernel(self):
        self.check_body('unresolved', 'rejected')

    def test_supplied_metavariable_reaches_kernel(self):
        self.check_body('metavariable', 'rejected')

    def test_supplied_loose_index_reaches_kernel(self):
        self.check_body('loose-index', 'rejected')

    def test_supplied_wrong_type_reaches_kernel(self):
        self.check_body('wrong-type', 'rejected')


class SuppliedFailureTests(unittest.TestCase):
    def test_interrupted_supervisor_reaps_owned_session(self):
        """Interrupt an active owned session and distinguish interruption from a verdict."""
        import signal
        import tempfile
        import time
        from scripts.lean_module_data.paths import find_olean, search_path
        from scripts.verification.processes import live_owned, observe, process_record, process_table, stop_tree

        module = 'SuppliedInterruptFixture'
        declaration = 'suppliedInterruptFixture'
        toolchain = Path(os.environ['LEAN_SYSROOT']).resolve()
        init = find_olean('Init', search_path()).resolve()
        with tempfile.TemporaryDirectory(prefix='supplied-interrupt-', dir=ROOT / '.lake/packages') as temporary:
            package = Path(temporary)
            source = package / (module + '.lean')
            source.write_text('module\npublic import Init\npublic section\n'
                              'theorem suppliedInterruptFixture : True := True.intro\n')
            artifact = package / ('.lake/build/lib/lean/' + module + '.olean')
            setup = package / ('.lake/build/ir/' + module + '.setup.json')
            artifact.parent.mkdir(parents=True)
            setup.parent.mkdir(parents=True)
            setup.write_text(json.dumps({'name': module, 'isModule': True,
                                         'package': 'supplied-interrupt-fixture', 'options': {},
                                         'importArts': {'Init': [str(init), str(init.with_suffix('.ir')),
                                                                 str(init) + '.server']},
                                         'plugins': [], 'dynlibs': []}))
            env = {**os.environ, 'LEAN_PATH': str(artifact.parent) + os.pathsep + os.environ['LEAN_PATH']}
            compile_command = [str(toolchain / 'bin/lean'), str(source), '-DwarningAsError=true',
                               '--setup', str(setup), '-o', str(artifact),
                               '-i', str(artifact.with_suffix('.ilean')), '-c', str(artifact.with_suffix('.c'))]
            compiled = subprocess.run(compile_command, env=env, capture_output=True, text=True, timeout=300)
            self.assertEqual(compiled.returncode, 0, compiled.stdout + compiled.stderr)
            self.assertEqual(compiled.stderr, '')
            guard = toolchain / 'MODULE-GUARD.json'
            guarded = Path(json.loads(guard.read_text())['prefix']) / 'bin/lean'
            bound = [source, setup, artifact, Path(str(artifact) + '.server'),
                     Path(str(artifact) + '.private'), artifact.with_suffix('.ir'),
                     init, Path(str(init) + '.server'), init.with_suffix('.ir'),
                     guard, toolchain / 'bin/lean', guarded,
                     ROOT / 'scripts/lean_module_data/supplied.py',
                     ROOT / 'scripts/lean_module_data/kernel.py',
                     ROOT / 'scripts/lean_module_data/kernel_native.c']
            print('interrupt-fixture-bindings ' + json.dumps({str(path): sha(path) for path in bound},
                                                              sort_keys=True), flush=True)
            marker = package / 'worker-ready.json'
            receipt = package / 'receipt.json'
            worker = ("import json,os,subprocess,sys,time; from pathlib import Path; "
                      "child=subprocess.Popen([sys.executable,'-c','import time; time.sleep(180)'],"
                      "start_new_session=True); "
                      "p=Path(sys.argv[1]); tmp=p.with_suffix('.tmp'); "
                      "tmp.write_text(json.dumps({'worker':os.getpid(),'child':child.pid})); os.replace(tmp,p); "
                      "time.sleep(180)")
            command = [sys.executable, '-m', 'scripts.lean_module_data.supplied', module, declaration,
                       '--source', str(source), '--toolchain', str(toolchain), '--cache',
                       str(ROOT / '.lake/kernel-replay-tests'), '--receipt', str(receipt),
                       '--supervise', sys.executable, '-c', worker, str(marker)]
            process = subprocess.Popen(command, env=env, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                       text=True, start_new_session=True)
            identity = process_record(process.pid)
            if identity is None:
                process.terminate()
                try:
                    process.wait(timeout=15)
                except subprocess.TimeoutExpired:
                    process.kill()
                    process.wait()
                self.fail('production supervisor identity was unavailable')
            known = {process.pid: identity[0]}
            try:
                deadline = time.monotonic() + 120
                while time.monotonic() < deadline and process.poll() is None:
                    observe(process, known, process_table())
                    if marker.is_file():
                        break
                    time.sleep(.05)
                else:
                    self.fail('production supervisor did not start its worker')
                worker_pids = json.loads(marker.read_text())
                owned = observe(process, known, process_table())
                self.assertIn(worker_pids['worker'], owned)
                self.assertIn(worker_pids['child'], owned)
                native = []
                for pid in owned:
                    try:
                        argv = (Path('/proc') / str(pid) / 'cmdline').read_bytes().split(b'\0')
                    except (FileNotFoundError, ProcessLookupError):
                        continue
                    if argv and argv[0].endswith(b'/kernel-replay') and len(argv) > 1 and argv[1] == b'service':
                        native.append(pid)
                self.assertEqual(len(native), 1, 'live native service must be observed')
                os.kill(process.pid, signal.SIGTERM)
                stdout, stderr = process.communicate(timeout=60)
                print('interruption-raw ' + json.dumps({'exit': process.returncode, 'stdout': stdout,
                                                        'stderr': stderr, 'native': native, 'owned': known},
                                                       sort_keys=True), flush=True)
                self.assertEqual(process.returncode, 2)
                outcome = json.loads(stdout.splitlines()[-1])
                self.assertEqual(outcome['status'], 'incomplete')
                self.assertIsNone(outcome['kernel'])
                self.assertIn('interrupted', outcome['reason'])
                self.assertFalse(receipt.exists(), 'interrupted session must not leave a completed receipt')
                self.assertFalse(live_owned(known), 'owned supervisor descendants survived interruption')
            finally:
                if process.poll() is None or live_owned(known):
                    stop_tree(process, known, 15)

    def test_truncated_cli_session_frame_is_incomplete(self):
        """A truncated CLI session request is incomplete and its native service is reaped."""
        self.check_truncated_cli_session_frame(False)

    def test_transport_error_preserved_with_changed_cleanup_input(self):
        """Keep a real transport failure primary when currentness cleanup also fails."""
        self.check_truncated_cli_session_frame(True)

    def test_interrupted_native_response_through_cli_is_incomplete(self):
        """A native service interrupted with a queued request yields no kernel verdict."""
        self.check_truncated_cli_session_frame(False, interrupt_native=True)

    def check_truncated_cli_session_frame(self, change_source, *, interrupt_native=False):
        """Exercise the production session with an optional changed cleanup input."""
        import select
        import fcntl
        import signal
        import socket
        import struct
        import tempfile
        import termios
        import time
        from scripts.lean_module_data.paths import find_olean, search_path
        from scripts.lean_module_data.supplied import _receive_session, _send_session, session_request
        from scripts.verification.processes import live_owned, observe, process_record, process_table, stop_tree

        module = 'SuppliedTransportFixture'
        declaration = 'suppliedTransportFixture'
        toolchain = Path(os.environ['LEAN_SYSROOT']).resolve()
        init = find_olean('Init', search_path()).resolve()
        with tempfile.TemporaryDirectory(prefix='supplied-transport-', dir=ROOT / '.lake/packages') as temporary:
            package = Path(temporary)
            source = package / (module + '.lean')
            source.write_text('module\npublic import Init\npublic section\n'
                              'theorem suppliedTransportFixture : True := True.intro\n')
            artifact = package / ('.lake/build/lib/lean/' + module + '.olean')
            setup = package / ('.lake/build/ir/' + module + '.setup.json')
            artifact.parent.mkdir(parents=True)
            setup.parent.mkdir(parents=True)
            setup.write_text(json.dumps({'name': module, 'isModule': True,
                                         'package': 'supplied-transport-fixture', 'options': {},
                                         'importArts': {'Init': [str(init), str(init.with_suffix('.ir')),
                                                                 str(init) + '.server']},
                                         'plugins': [], 'dynlibs': []}))
            env = {**os.environ, 'LEAN_PATH': str(artifact.parent) + os.pathsep + os.environ['LEAN_PATH']}
            compile_command = [str(toolchain / 'bin/lean'), str(source), '-DwarningAsError=true',
                               '--setup', str(setup), '-o', str(artifact),
                               '-i', str(artifact.with_suffix('.ilean')), '-c', str(artifact.with_suffix('.c'))]
            compiled = subprocess.run(compile_command, env=env, capture_output=True, text=True, timeout=300)
            self.assertEqual(compiled.returncode, 0, compiled.stdout + compiled.stderr)
            self.assertEqual(compiled.stderr, '')
            receipt = package / 'transport.json'
            client, server = socket.socketpair()
            command = [sys.executable, '-m', 'scripts.lean_module_data.supplied', module, declaration,
                       '--source', str(source), '--toolchain', str(toolchain), '--cache',
                       str(ROOT / '.lake/kernel-replay-tests'), '--receipt', str(receipt),
                       '--serve-fd', str(server.fileno())]
            process = subprocess.Popen(command, env=env, pass_fds=(server.fileno(),),
                                       stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                       text=True, start_new_session=True)
            server.close()
            identity = process_record(process.pid)
            if identity is None:
                client.close()
                process.terminate()
                try:
                    process.wait(timeout=15)
                except subprocess.TimeoutExpired:
                    process.kill()
                    process.wait()
                self.fail('production CLI process identity was unavailable')
            known = {process.pid: identity[0]}
            try:
                deadline = time.monotonic() + 120
                while time.monotonic() < deadline and process.poll() is None:
                    observe(process, known, process_table())
                    if select.select([client], [], [], .05)[0]:
                        break
                else:
                    self.fail('production session did not become ready')
                client.settimeout(120)
                self.assertEqual(_receive_session(client), {'status': 'ready'})
                current = session_request(client.fileno(), 'compiled')
                self.assertEqual(current['kernel']['status'], 'accepted')
                owned = observe(process, known, process_table())
                native = []
                for pid in owned:
                    try:
                        argv = (Path('/proc') / str(pid) / 'cmdline').read_bytes().split(b'\0')
                    except (FileNotFoundError, ProcessLookupError):
                        continue
                    if argv and argv[0].endswith(b'/kernel-replay') and len(argv) > 1 and argv[1] == b'service':
                        native.append(pid)
                self.assertEqual(len(native), 1, 'actual owned native service must be observed')
                original_source_sha = sha(source)
                if change_source:
                    source.write_text(source.read_text() + '\n-- changed during the live session\n')
                    self.assertNotEqual(sha(source), original_source_sha)
                session_error = None
                pending = None
                if interrupt_native:
                    self.assertEqual(process_record(native[0], live=True)[0], known[native[0]])
                    os.kill(native[0], signal.SIGSTOP)
                    deadline = time.monotonic() + 30
                    while time.monotonic() < deadline:
                        status = (Path('/proc') / str(native[0]) / 'status').read_text()
                        if any(line.split()[1] in ('T', 't') for line in status.splitlines()
                               if line.startswith('State:')):
                            break
                        time.sleep(.01)
                    else:
                        self.fail('owned native service did not stop')
                    native_input = os.open('/proc/{}/fd/0'.format(native[0]), os.O_RDONLY | os.O_NONBLOCK)
                    try:
                        _send_session(client, {'body': 'compiled'})
                        deadline = time.monotonic() + 60
                        pending = 0
                        while time.monotonic() < deadline:
                            pending = struct.unpack('i', fcntl.ioctl(native_input, termios.FIONREAD,
                                                                     struct.pack('i', 0)))[0]
                            if pending >= 25:  # One complete op=9 request, before any response.
                                break
                            time.sleep(.02)
                        self.assertGreaterEqual(pending, 25, 'native request was not queued')
                        self.assertEqual(process_record(native[0], live=True)[0], known[native[0]])
                        os.kill(native[0], signal.SIGKILL)
                    finally:
                        os.close(native_input)
                    session_error = _receive_session(client)
                    self.assertEqual(session_error['status'], 'incomplete')
                    self.assertIsNone(session_error['kernel'])
                    self.assertIn('native kernel transport ended before complete response', session_error['reason'])
                else:
                    client.sendall(struct.pack('<I', 32) + b'{"body":')
                    client.shutdown(socket.SHUT_WR)
                stdout, stderr = process.communicate(timeout=120)
                self.assertEqual(process.returncode, 2, stdout + stderr)
                outcome = json.loads(receipt.read_text())
                print('truncated-cli-receipt ' + json.dumps(outcome, sort_keys=True), flush=True)
                print('truncated-cli-transport ' + json.dumps({'stdout': stdout, 'stderr': stderr,
                                                               'native_pid': native[0], 'owned': known,
                                                               'session_error': session_error,
                                                               'queued_native_bytes': pending},
                                                              sort_keys=True), flush=True)
                self.assertEqual(outcome['status'], 'incomplete')
                self.assertIsNone(outcome['kernel'])
                expected_reason = ('InvalidArtifact: native kernel transport ended before complete response'
                                   if interrupt_native else 'InvalidArtifact: incomplete supplied session frame')
                self.assertEqual(outcome['reason'], expected_reason)
                self.assertEqual(outcome['controls']['compiled']['status'], 'accepted')
                if change_source:
                    self.assertEqual(outcome['bindings'][str(source)]['sha256'], original_source_sha)
                    self.assertTrue(any('changed invocation input: ' + str(source) in error
                                        for error in outcome['cleanup_errors']))
                elif interrupt_native:
                    self.assertTrue(any('native kernel terminated unexpectedly' in error
                                        for error in outcome['cleanup_errors']))
                else:
                    self.assertNotIn('cleanup_errors', outcome)
                self.assertFalse(live_owned(known), 'owned CLI or native service survived')
                if interrupt_native:
                    remaining = process_record(native[0])
                    self.assertTrue(remaining is None or remaining[0] != known[native[0]],
                                    'interrupted native service was not reaped')
            finally:
                client.close()
                if process.poll() is None or live_owned(known):
                    stop_tree(process, known, 15)

    def test_malformed_expr_cache_is_incomplete_before_native(self):
        """A changed Expr cache with intact constructor shape cannot reach native loading."""
        import tempfile
        from scripts.lean_module_data.importer import Module
        from scripts.lean_module_data.kernel_replay import text
        from scripts.lean_module_data.paths import find_olean, search_path

        module = 'SuppliedCacheFixture'
        declaration = 'suppliedCacheFixture'
        toolchain = Path(os.environ['LEAN_SYSROOT']).resolve()
        init = find_olean('Init', search_path()).resolve()
        with tempfile.TemporaryDirectory(prefix='supplied-cache-', dir=ROOT / '.lake/packages') as temporary:
            package = Path(temporary)
            source = package / (module + '.lean')
            source.write_text('module\npublic import Init\npublic section\n'
                              'theorem suppliedCacheFixture : True := True.intro\n')
            artifact = package / ('.lake/build/lib/lean/' + module + '.olean')
            setup = package / ('.lake/build/ir/' + module + '.setup.json')
            artifact.parent.mkdir(parents=True)
            setup.parent.mkdir(parents=True)
            setup.write_text(json.dumps({'name': module, 'isModule': True,
                                         'package': 'supplied-cache-fixture', 'options': {},
                                         'importArts': {'Init': [str(init), str(init.with_suffix('.ir')),
                                                                 str(init) + '.server']},
                                         'plugins': [], 'dynlibs': []}))
            env = {**os.environ, 'LEAN_PATH': str(artifact.parent) + os.pathsep + os.environ['LEAN_PATH']}
            compile_command = [str(toolchain / 'bin/lean'), str(source), '-DwarningAsError=true',
                               '--setup', str(setup), '-o', str(artifact),
                               '-i', str(artifact.with_suffix('.ilean')), '-c', str(artifact.with_suffix('.c'))]
            compiled = subprocess.run(compile_command, env=env, capture_output=True, text=True, timeout=300)
            self.assertEqual(compiled.returncode, 0, compiled.stdout + compiled.stderr)
            self.assertEqual(compiled.stderr, '')

            def invoke(label, cache):
                receipt = package / (label + '.json')
                command = [sys.executable, '-m', 'scripts.lean_module_data.supplied', module, declaration,
                           '--source', str(source), '--toolchain', str(toolchain), '--cache', str(cache),
                           '--receipt', str(receipt)]
                result = subprocess.run(command, env=env, capture_output=True, text=True, timeout=300)
                self.assertEqual(result.returncode, 2, result.stdout + result.stderr)
                outcome = json.loads(receipt.read_text())
                print(label + '-receipt ' + json.dumps(outcome, sort_keys=True), flush=True)
                print(label + '-transport ' + json.dumps({'stdout': result.stdout, 'stderr': result.stderr}),
                      flush=True)
                return outcome

            current = invoke('current', ROOT / '.lake/kernel-replay-tests')
            self.assertEqual(current['status'], 'incomplete')
            self.assertEqual(current['kernel']['status'], 'accepted')
            parsed = Module(module, artifact, {}, {})
            selected = [ref for _, ref, _ in parsed.entries(True) if text(ref) == declaration]
            self.assertEqual(len(selected), 1)
            expression = selected[0].fields[1]
            before = parsed.d.descriptor('Expr', expression)
            region, offset, header = parsed.d.header(expression)
            self.assertEqual(before[0], 4, 'fixture proof must be an Expr.const')
            self.assertEqual(region.path, Path(str(artifact) + '.private'))
            self.assertEqual(header[2], 2)
            raw = bytearray(region.path.read_bytes())
            cache_offset = offset + 8 + 8 * header[2]
            raw[cache_offset] ^= 1  # Change only the low byte of Expr's 64-bit cache.
            region.path.write_bytes(raw)

            mutated = Module(module, artifact, {}, {})
            selected_after = [ref for _, ref, _ in mutated.entries(True) if text(ref) == declaration]
            self.assertEqual(len(selected_after), 1)
            selected_after[0].info()  # The complete record still has a valid typed shape.
            after = mutated.d.descriptor('Expr', selected_after[0].fields[1])
            self.assertEqual(before[:2], after[:2])
            self.assertNotEqual(before[2], after[2])
            cache = package / 'unexpected-native-cache'
            result = invoke('malformed-cache', cache)
            self.assertEqual(result['status'], 'incomplete')
            self.assertIsNone(result['kernel'])
            self.assertIn('fresh selected-source output differs: .private', result['reason'])
            self.assertFalse(cache.exists(), 'malformed cache must fail before native preparation')

    def check_real_private_versions(self, mixed):
        """Submit genuine stale or mixed compiler parts to the production CLI."""
        import tempfile
        from scripts.lean_module_data.paths import find_olean, search_path

        toolchain = Path(os.environ['LEAN_SYSROOT']).resolve()
        init = find_olean('Init', search_path()).resolve()
        module = 'SuppliedVersionFixture'
        declaration = 'suppliedVersionFixture'
        with tempfile.TemporaryDirectory(prefix='supplied-versions-', dir=ROOT / '.lake/packages') as temporary:
            package = Path(temporary)
            source = package / (module + '.lean')
            artifact = package / ('.lake/build/lib/lean/' + module + '.olean')
            setup = package / ('.lake/build/ir/' + module + '.setup.json')
            artifact.parent.mkdir(parents=True)
            setup.parent.mkdir(parents=True)
            setup.write_text(json.dumps({'name': module, 'isModule': True,
                                         'package': 'supplied-versions', 'options': {},
                                         'importArts': {'Init': [str(init), str(init.with_suffix('.ir')),
                                                                 str(init) + '.server']},
                                         'plugins': [], 'dynlibs': []}))
            env = {**os.environ, 'LEAN_PATH': str(artifact.parent) + os.pathsep + os.environ['LEAN_PATH']}
            parts = [artifact, Path(str(artifact) + '.server'),
                     Path(str(artifact) + '.private'), artifact.with_suffix('.ir')]
            snapshots = []
            for version in (1, 2):
                source.write_text('module\npublic import Init\npublic section\n'
                                  'private def versionMarker : Nat := ' + str(version + 2) + '\n'
                                  '@[expose] def versionPublic : Nat := ' + str(version if mixed else 1) + '\n'
                                  'theorem suppliedVersionFixture : True := True.intro\n')
                command = [str(toolchain / 'bin/lean'), str(source), '-DwarningAsError=true',
                           '--setup', str(setup), '-o', str(artifact),
                           '-i', str(artifact.with_suffix('.ilean')), '-c', str(artifact.with_suffix('.c'))]
                compiled = subprocess.run(command, env=env, capture_output=True, text=True, timeout=300)
                self.assertEqual(compiled.returncode, 0, compiled.stdout + compiled.stderr)
                self.assertEqual(compiled.stderr, '')
                snapshots.append([part.read_bytes() for part in parts])
            hashes = [[hashlib.sha256(part).hexdigest() for part in version] for version in snapshots]
            print('compiler-parts ' + json.dumps(hashes), flush=True)
            self.assertNotEqual(hashes[0][2], hashes[1][2], 'compiler private parts must differ')
            if mixed:
                self.assertNotEqual(hashes[0][0], hashes[1][0], 'compiler public parts must differ')
            else:
                self.assertEqual(hashes[0][0], hashes[1][0], 'stale control isolates the private change')

            def invoke(label, cache):
                receipt = package / (label + '.json')
                command = [sys.executable, '-m', 'scripts.lean_module_data.supplied', module, declaration,
                           '--source', str(source), '--toolchain', str(toolchain), '--cache', str(cache),
                           '--receipt', str(receipt)]
                result = subprocess.run(command, env=env, capture_output=True, text=True, timeout=300)
                self.assertEqual(result.returncode, 2, result.stdout + result.stderr)
                outcome = json.loads(receipt.read_text())
                self.assertEqual(outcome['status'], 'incomplete')
                print(label + ' ' + json.dumps({'stdout': result.stdout, 'stderr': result.stderr,
                                                'kernel': outcome['kernel'], 'reason': outcome['reason']},
                                               sort_keys=True), flush=True)
                print(label + '-bindings ' + json.dumps(outcome.get('bindings', outcome.get('inputs')),
                                                        sort_keys=True), flush=True)
                return outcome

            baseline = invoke('current', ROOT / '.lake/kernel-replay-tests')
            self.assertEqual(baseline['kernel']['status'], 'accepted')
            for index, part in enumerate(parts):
                part.write_bytes(snapshots[0][index] if not mixed or index == 2 else snapshots[1][index])
            cache = package / 'unexpected-native-cache'
            outcome = invoke('mixed-private' if mixed else 'stale-artifacts', cache)
            self.assertIsNone(outcome['kernel'])
            self.assertIn('fresh selected-source output differs: .private', outcome['reason'])
            self.assertFalse(cache.exists(), 'stale or mixed parts must fail before native preparation')

    def test_stale_genuine_private_artifact_is_incomplete(self):
        """Old compiler outputs with current source are refused before native loading."""
        self.check_real_private_versions(False)

    def test_mixed_genuine_private_artifact_is_incomplete(self):
        """An old private part paired with new compiler outputs is refused before native loading."""
        self.check_real_private_versions(True)

    """Keep unsupported and missing inputs outside semantic kernel results."""

    def test_timeout_cleanup_uses_term_then_kill_grace(self):
        """A real unresponsive owned process receives TERM before the kill grace."""
        import signal
        import time
        from scripts.lean_module_data.supplied import terminate_with_grace
        child_code = ("import os,signal,time; "
                      "signal.signal(signal.SIGTERM, lambda *_: os.write(1,b'TERM\\n')); "
                      "os.write(1,b'ready\\n'); time.sleep(120)")
        process = subprocess.Popen([sys.executable, '-c', child_code], stdout=subprocess.PIPE,
                                   stderr=subprocess.PIPE, text=True)
        try:
            self.assertEqual(process.stdout.readline().strip(), 'ready')
            started = time.monotonic()
            terminate_with_grace(process)
            elapsed = time.monotonic() - started
            stdout, stderr = process.communicate(timeout=15)
            self.assertIn('TERM', stdout, repr((process.returncode, stdout, stderr, elapsed)))
            self.assertEqual(process.returncode, -signal.SIGKILL, stderr)
            self.assertGreaterEqual(elapsed, 14.5)
            print('timeout cleanup: TERM, 15-second grace, SIGKILL; elapsed', round(elapsed, 2), flush=True)
        finally:
            if process.poll() is None:
                process.kill()
                process.wait()

    def test_supervised_missing_input_never_runs_worker(self):
        """A failed producer cannot start a supervised client command."""
        import tempfile
        with tempfile.TemporaryDirectory(prefix='supplied-supervisor-failure-') as temporary:
            work = Path(temporary)
            marker = work / 'worker-ran'
            receipt = work / 'receipt.json'
            command = [sys.executable, '-m', 'scripts.lean_module_data.supplied',
                       'Missing.Module', 'Missing.theorem', '--source', str(work / 'missing.lean'),
                       '--toolchain', os.environ['LEAN_SYSROOT'], '--cache', str(work / 'cache'),
                       '--receipt', str(receipt), '--supervise', sys.executable, '-c',
                       'from pathlib import Path; import sys; Path(sys.argv[1]).touch()', str(marker)]
            result = subprocess.run(command, capture_output=True, text=True, timeout=300)
            self.assertEqual(result.returncode, 2, result.stdout + result.stderr)
            self.assertFalse(marker.exists(), 'worker must not start without a producer')
            outcome = json.loads(receipt.read_text())
            self.assertEqual(outcome['status'], 'incomplete')
            self.assertIsNone(outcome['kernel'])
            self.assertIn('missing source', outcome['reason'])

    def test_ordered_import_witness_checks_nonleaf_and_mixed_setup(self):
        """A real imported chain is witnessed and a mixed setup is incomplete."""
        import tempfile
        from scripts.lean_module_data.compact import InvalidArtifact
        from scripts.lean_module_data.kernel import Bindings
        from scripts.lean_module_data.paths import search_path
        from scripts.lean_module_data.supplied import (
            closure_producer_plan, producer_import_scope, witness_producer_sequence,
        )
        from scripts.nanoda.artifact_inputs import compiled_inputs, verify_inputs
        search = search_path()
        toolchain = Path(os.environ['LEAN_SYSROOT']).resolve()
        inputs = compiled_inputs(['Purelib.Approximation.Gaussian.Exponential.E'], search)
        plan = closure_producer_plan(inputs, toolchain)
        nodes = {node['name']: node for node in inputs['inventory']['modules']}
        prefix = plan['modules'][:5]
        self.assertEqual(prefix[-1]['module'], 'Aesop.Constants')
        self.assertIn('Aesop.Percent', nodes[prefix[-1]['module']]['imports'])
        attempt = {'search_path': [str(p.resolve()) for p in search]}
        binding = Bindings()
        witness_producer_sequence(prefix, plan['core_modules'], toolchain, inputs, binding, attempt,
                                  selected_name='', selected_source=Path('/unused'))
        self.assertEqual(len(attempt['closure_witnesses']), len(prefix))
        self.assertTrue(all(row['producer']['exit'] == 0 for row in attempt['closure_witnesses']))
        verify_inputs(inputs, search)
        binding.verify()
        print('ordered-producer-prefix ' + json.dumps(attempt['closure_witnesses'], sort_keys=True),
              flush=True)
        with tempfile.TemporaryDirectory(prefix='supplied-mixed-setup-') as temporary:
            item = dict(prefix[-1])
            spec = json.loads(Path(item['setup']).read_text())
            target = next(iter(spec['importArts']))
            artifact = Path(nodes[target]['files'][0]).resolve()
            spec['importArts'][target][0] = str(artifact) + '.private'
            path = Path(temporary) / 'mixed.setup.json'
            path.write_text(json.dumps(spec))
            item['setup'] = str(path)
            ready = set(plan['core_modules']) | {row['module'] for row in prefix[:-1]}
            with self.assertRaisesRegex(InvalidArtifact, 'mixed import parts'):
                producer_import_scope(item, nodes, ready)
            with self.assertRaisesRegex(InvalidArtifact, 'dependency is not witnessed'):
                producer_import_scope(prefix[-1], nodes, set(plan['core_modules']))

    def test_changed_source_fails_before_native(self):
        """A supplied source differing from the selected workspace source is incomplete."""
        import tempfile
        module = 'Purelib.Approximation.Gaussian.Exponential.E'
        original = ROOT / 'Purelib/Approximation/Gaussian/Exponential/E.lean'
        with tempfile.TemporaryDirectory(prefix='supplied-stale-source-') as temporary:
            work = Path(temporary)
            source = work / 'E.lean'
            source.write_text(original.read_text() + '\npublic theorem suppliedWitnessMutation : True := True.intro\n')
            receipt = work / 'result.json'
            cache = work / 'cache'
            command = [sys.executable, '-m', 'scripts.lean_module_data.supplied', module,
                       module + '.horner_sample_eq_factorial', '--source', str(source),
                       '--toolchain', os.environ['LEAN_SYSROOT'], '--cache', str(cache),
                       '--receipt', str(receipt)]
            result = subprocess.run(command, capture_output=True, text=True, timeout=300)
            self.assertEqual(result.returncode, 2, result.stderr)
            outcome = json.loads(receipt.read_text())
            self.assertEqual(outcome['status'], 'incomplete')
            self.assertIsNone(outcome['kernel'])
            self.assertNotIn('producer', outcome)
            self.assertIn('selected source differs from the workspace source', outcome['reason'])
            self.assertTrue(outcome['bindings'])
            self.assertFalse(cache.exists(), 'stale source must not launch native preparation')

    def test_actual_import_closure_plan_and_leaf_witness(self):
        """Plan the actual E closure and freshly compile one Core-only project leaf."""
        from scripts.lean_module_data.kernel import Bindings
        from scripts.lean_module_data.paths import find_olean, search_path
        from scripts.lean_module_data.supplied import closure_producer_plan, witness_selected
        from scripts.nanoda.artifact_inputs import compiled_inputs

        search = search_path()
        toolchain = Path(os.environ['LEAN_SYSROOT']).resolve()
        inputs = compiled_inputs(['Purelib.Approximation.Gaussian.Exponential.E'], search)
        plan = closure_producer_plan(inputs, toolchain)
        rows = plan['modules']
        positions = {row['module']: i for i, row in enumerate(rows)}
        self.assertEqual(len(positions), len(rows))
        self.assertIn('Purelib.Approximation.Gaussian.Exponential.E', positions)
        self.assertTrue(plan['core_modules'])
        for node in inputs['inventory']['modules']:
            if node['name'] in positions:
                for dep in node['imports']:
                    if dep in positions:
                        self.assertLess(positions[dep], positions[node['name']])
        print('closure-plan core={} noncore={}'.format(len(plan['core_modules']), len(rows)), flush=True)
        for name in ('Purelib.Data.Nat.Subtraction', 'Batteries.Data.Nat.Basic'):
            with self.subTest(module=name):
                row = rows[positions[name]]
                node = next(n for n in inputs['inventory']['modules'] if n['name'] == name)
                self.assertTrue(all(dep not in positions for dep in node['imports']))
                binding = Bindings()
                binding.add(row['source'], 'selected-source')
                attempt = {'search_path': [str(p.resolve()) for p in search]}
                witness_selected(name, Path(row['source']), find_olean(name, search).resolve(),
                                 toolchain, inputs, binding, attempt, package_root=row['package_root'])
                self.assertEqual(attempt['producer']['exit'], 0)
                self.assertFalse(attempt['producer']['timeout'])
                self.assertEqual(len(attempt['producer']['outputs']), 6)
                print('import-witness ' + name + ' ' + json.dumps(attempt['producer'], sort_keys=True),
                      flush=True)

    def test_supplied_operational_failure_is_incomplete(self):
        import tempfile
        with tempfile.TemporaryDirectory(prefix='supplied-failure-') as temporary:
            work = Path(temporary)
            receipt = work / 'result.json'
            command = [sys.executable, '-m', 'scripts.lean_module_data.supplied',
                       'Missing.Module', 'Missing.theorem', '--source', str(work / 'missing.lean'),
                       '--toolchain', os.environ['LEAN_SYSROOT'], '--cache', str(work / 'cache'),
                       '--receipt', str(receipt)]
            missing = subprocess.run(command, capture_output=True, text=True, timeout=300)
            self.assertEqual(missing.returncode, 2, missing.stderr)
            outcome = json.loads(receipt.read_text())
            self.assertEqual(outcome['status'], 'incomplete')
            self.assertIsNone(outcome['kernel'])
            self.assertIn('missing source', outcome['reason'])
            unsupported = subprocess.run(command + ['--body', 'arbitrary-compact-bytes'],
                                         capture_output=True, text=True, timeout=300)
            self.assertEqual(unsupported.returncode, 2, unsupported.stderr)
            outcome = json.loads(receipt.read_text())
            self.assertEqual(outcome['status'], 'incomplete')
            self.assertIsNone(outcome['kernel'])
            self.assertIn('unsupported supplied body selector', outcome['reason'])

    def test_missing_private_and_bad_header_never_launch_native(self):
        """Reject unavailable or malformed module parts before native setup."""
        import shutil
        import tempfile
        module = 'Purelib.Approximation.Gaussian.Exponential.E'
        name = module + '.horner_sample_eq_factorial'
        relative = Path(*module.split('.')).with_suffix('.olean')
        original = ROOT / '.lake/build/lib/lean' / relative
        source = ROOT / 'Purelib/Approximation/Gaussian/Exponential/E.lean'
        with tempfile.TemporaryDirectory(prefix='supplied-parts-') as temporary:
            work = Path(temporary)
            shadow = work / 'library' / relative
            shadow.parent.mkdir(parents=True)
            shutil.copyfile(original, shadow)
            shutil.copyfile(str(original) + '.server', str(shadow) + '.server')
            cache = work / 'cache'
            receipt = work / 'result.json'
            command = [sys.executable, '-m', 'scripts.lean_module_data.supplied', module, name,
                       '--source', str(source), '--toolchain', os.environ['LEAN_SYSROOT'],
                       '--cache', str(cache), '--receipt', str(receipt)]
            env = {**os.environ, 'LEAN_PATH': str(work / 'library') + os.pathsep + os.environ['LEAN_PATH']}
            missing = subprocess.run(command, env=env, capture_output=True, text=True, timeout=300)
            self.assertEqual(missing.returncode, 2, missing.stderr)
            outcome = json.loads(receipt.read_text())
            self.assertEqual(outcome['status'], 'incomplete')
            self.assertIsNone(outcome['kernel'])
            self.assertIn('.private', outcome['reason'])
            self.assertFalse(cache.exists(), 'native build must not run with missing private input')
            raw = bytearray(shadow.read_bytes())
            raw[0] ^= 1
            shadow.write_bytes(raw)
            malformed = subprocess.run(command, env=env, capture_output=True, text=True, timeout=300)
            self.assertEqual(malformed.returncode, 2, malformed.stderr)
            outcome = json.loads(receipt.read_text())
            self.assertEqual(outcome['status'], 'incomplete')
            self.assertIsNone(outcome['kernel'])
            self.assertIn('not pinned', outcome['reason'])
            self.assertFalse(cache.exists(), 'native build must not run with an unsupported header')

    def test_bad_selected_expression_never_launches_native(self):
        """Reject a malformed selected proof record before adapter preparation."""
        import shutil
        import tempfile
        from scripts.lean_module_data.importer import Module
        from scripts.lean_module_data.kernel_replay import text
        module = 'Purelib.Approximation.Gaussian.Exponential.E'
        name = module + '.horner_sample_eq_factorial'
        relative = Path(*module.split('.')).with_suffix('.olean')
        original = ROOT / '.lake/build/lib/lean' / relative
        parsed = Module(module, original, {}, {})
        refs = [ref for _, ref, _ in parsed.entries(True) if text(ref) == name]
        self.assertEqual(len(refs), 1)
        region, offset = parsed.d.parts.locate(refs[0].fields[1])
        self.assertEqual(region.path, Path(str(original) + '.private'))
        with tempfile.TemporaryDirectory(prefix='supplied-bad-expr-') as temporary:
            work = Path(temporary)
            shadow = work / 'library' / relative
            shadow.parent.mkdir(parents=True)
            for suffix in ('', '.server', '.private', '.ir'):
                shutil.copyfile(str(original) + suffix if suffix != '.ir' else original.with_suffix('.ir'),
                                str(shadow) + suffix if suffix != '.ir' else shadow.with_suffix('.ir'))
            private = Path(str(shadow) + '.private')
            data = bytearray(private.read_bytes())
            data[offset + 7] = 12  # Not a supported Expr constructor tag.
            private.write_bytes(data)
            cache = work / 'cache'
            receipt = work / 'result.json'
            command = [sys.executable, '-m', 'scripts.lean_module_data.supplied', module, name,
                       '--source', str(ROOT / 'Purelib/Approximation/Gaussian/Exponential/E.lean'),
                       '--toolchain', os.environ['LEAN_SYSROOT'], '--cache', str(cache),
                       '--receipt', str(receipt)]
            env = {**os.environ, 'LEAN_PATH': str(work / 'library') + os.pathsep + os.environ['LEAN_PATH']}
            result = subprocess.run(command, env=env, capture_output=True, text=True, timeout=300)
            self.assertEqual(result.returncode, 2, result.stderr)
            outcome = json.loads(receipt.read_text())
            self.assertEqual(outcome['status'], 'incomplete')
            self.assertIsNone(outcome['kernel'])
            self.assertIn('invalid Expr constructor', outcome['reason'])
            self.assertFalse(cache.exists(), 'adapter build must not run with a malformed proof')

    def test_native_crash_is_incomplete_and_reaped(self):
        """A real killed native service cannot become a kernel verdict."""
        from scripts.nanoda.processes import process_record

        session_fd = os.environ.get('FC_SUPPLIED_SESSION_FD')
        session_path = os.environ.get('FC_SUPPLIED_SESSION_PATH')
        if session_fd is not None or session_path is not None:
            from scripts.lean_module_data.supplied import session_request, session_request_path
            module = 'Purelib.Approximation.Gaussian.Exponential.E'
            outcome = (session_request_path(session_path, 'crash', module,
                                            module + '.horner_sample_eq_factorial')
                       if session_path is not None else session_request(int(session_fd), 'crash'))
            self.assertEqual(outcome['status'], 'incomplete')
            self.assertIsNone(outcome['kernel'])
            self.assertTrue(outcome['reason'])
            self.assertTrue(outcome.get('reaped'), repr(outcome))
            self.assertIsNone(process_record(outcome['pid'], live=True))
            print('native-crash incomplete: ' + json.dumps(outcome, sort_keys=True), flush=True)
            return

        # A crash is an operational control, so use the same genuine small
        # production fixture as the supervisor/recovery regression. Waiting for
        # E's complete producer preparation inside this test hid the native
        # service beyond its observation deadline.
        KernelFixtureTests.check_supervised_live_fixture(self, crash=True)

    def test_truncated_native_transport_is_incomplete(self):
        """An incomplete counted command cannot become a kernel verdict."""
        import struct
        from scripts.lean_module_data.compact import InvalidArtifact
        from scripts.lean_module_data.kernel import Bindings, Native, native_build
        artifact = ROOT / '.lake/build/lib/lean/Purelib/Approximation/Gaussian/Exponential/E.olean'
        toolchain = Path(os.environ['LEAN_SYSROOT'])
        binary = native_build(toolchain, ROOT / '.lake/kernel-replay-tests', Bindings())
        native = Native(binary, artifact, artifact, toolchain, dict(os.environ))
        try:
            native.process.stdin.write(bytes([5]) + struct.pack('<Q', 24) + b'\0')
            native.process.stdin.close()
            with self.assertRaisesRegex(InvalidArtifact, 'transport ended before complete response'):
                native.read(9)
            self.assertEqual(native.process.wait(timeout=15), 2)
        finally:
            with self.assertRaisesRegex(InvalidArtifact, 'terminated unexpectedly'):
                native.close()
        self.assertIsNotNone(native.process.poll())

    def test_resource_limited_attempt_is_incomplete(self):
        """A finite host address-space limit must not produce a kernel verdict."""
        import resource
        import tempfile
        module = 'Purelib.Approximation.Gaussian.Exponential.E'
        with tempfile.TemporaryDirectory(prefix='supplied-resource-') as temporary:
            work = Path(temporary)
            receipt = work / 'result.json'
            command = [sys.executable, '-m', 'scripts.lean_module_data.supplied', module,
                       module + '.horner_sample_eq_factorial', '--source',
                       str(ROOT / 'Purelib/Approximation/Gaussian/Exponential/E.lean'),
                       '--toolchain', os.environ['LEAN_SYSROOT'], '--cache', str(work / 'cache'),
                       '--receipt', str(receipt)]
            def limit_address_space():
                bound = 384 * 1024**2
                resource.setrlimit(resource.RLIMIT_AS, (bound, bound))
            result = subprocess.run(command, preexec_fn=limit_address_space, timeout=180,
                                    text=True, capture_output=True)
            self.assertEqual(result.returncode, 2, result.stdout + result.stderr)
            outcome = json.loads(receipt.read_text())
            self.assertEqual(outcome['status'], 'incomplete')
            self.assertIsNone(outcome['kernel'])
            if 'MemoryError' not in outcome['reason']:
                # The address-space bound can prevent the checked compiler's
                # thread-stack allocation before Python exhausts its heap.
                self.assertEqual(outcome['reason'],
                                 'InvalidArtifact: fresh selected-source compilation failed')
                producer = outcome['closure_witnesses'][-1]['producer']
                self.assertIsInstance(producer['exit'], int)
                self.assertNotEqual(producer['exit'], 0)
                self.assertFalse(producer['timeout'])
                self.assertEqual(producer['outputs'], {})
                self.assertIn('failed to create thread', producer['stderr'])
            self.assertFalse((work / 'cache').exists(), 'resource failure preceded native preparation')
            print('resource-limit incomplete: ' + outcome['reason'], flush=True)
