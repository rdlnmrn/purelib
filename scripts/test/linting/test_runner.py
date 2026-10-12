#!/usr/bin/env python3
"""Check scope preservation, artifact-bound reuse, failures and interrupted recovery."""
import os
from pathlib import Path
import sys
import tempfile
import threading
import time
import unittest
from unittest import mock

from scripts.linting import runner


class ScopeTests(unittest.TestCase):
    def test_auto_concurrency_uses_cpus_and_measured_memory(self):
        gib = 1024**3
        self.assertEqual(runner.worker_count({}, cpus=4096, available=10000*gib), 4096)
        self.assertEqual(runner.worker_count({}, cpus=192, available=80*gib), 40)
        self.assertEqual(runner.worker_count({}, cpus=192, available=gib), 1)
        self.assertEqual(runner.worker_count({'CCL_LINT_JOBS': '10000'}, cpus=2, available=gib), 10000)
        for value in ('0', '-1', '', '1.5', 'all'):
            with self.subTest(value=value), self.assertRaisesRegex(ValueError, 'CCL_LINT_JOBS'):
                runner.worker_count({'CCL_LINT_JOBS': value})

    def test_scheduler_reports_fast_later_job_before_slow_first_job(self):
        release = threading.Event()
        def check(task):
            if task == 'slow':
                release.wait(3)
            return task
        with runner.concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
            results = runner.completed_tasks(pool, check, ['slow', 'fast', 'next'], 2)
            try:
                self.assertEqual(next(results), ('fast', 'fast'))
                self.assertEqual(next(results), ('next', 'next'))
            finally:
                release.set()
            self.assertEqual(list(results), [('slow', 'slow')])

    def test_scheduler_flushes_checkpoints_while_a_worker_is_slow(self):
        release, checkpointed = threading.Event(), threading.Event()
        def check(task):
            if task == 'slow':
                release.wait(3)
            return task
        def idle():
            checkpointed.set()
            release.set()
        with runner.concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
            results = runner.completed_tasks(pool, check, ['slow', 'fast'], 2, idle)
            try:
                self.assertEqual(next(results), ('fast', 'fast'))
                self.assertEqual(list(results), [('slow', 'slow')])
                self.assertTrue(checkpointed.is_set())
            finally:
                release.set()

    def test_plain_global_options_and_explicit_scope(self):
        self.assertEqual(runner.plain_request(['--wfail', '-q', 'lint', 'Purelib.A', 'scripts.Harness'],
                                             {'builtinLint': True}),
                         (['--wfail', '-q'], ['Purelib.A', 'scripts.Harness']))
        self.assertEqual(runner.plain_request(['--no-build', '--wfail', 'lint', 'Purelib.A'],
                                             {'builtinLint': True}),
                         (['--no-build', '--wfail'], ['Purelib.A']))

    def test_nonstandard_cli_and_drivers_delegate_unchanged(self):
        for args in (['lint', '--linters', 'linter.foo', 'Purelib.A'],
                     ['lint', '--record-exceptions', 'Purelib.A'],
                     ['lint', '--lint-only', 'Purelib.A'], ['lint', '--', 'custom'],
                     ['--dir=/tmp', 'lint', 'Purelib.A'],
                     ['-K', 'mode=custom', 'lint', 'Purelib.A'], ['lint', 'Purelib/A.lean'],
                     ['lint', 'Purelib..A'], ['lint', 'Purelib.A', 'Purelib.A'],
                     ['lint'], ['build', 'Purelib.A']):
            with self.subTest(args=args):
                self.assertIsNone(runner.plain_request(args, {'builtinLint': True}))
        self.assertIsNone(runner.plain_request(['lint', 'Purelib.A'],
                                               {'builtinLint': True, 'lintDriver': 'custom'}))

    def test_build_failure_does_not_start_checker(self):
        for options in (['--wfail'], ['--no-build', '--wfail']):
            with self.subTest(options=options), \
                    mock.patch.object(runner.subprocess, 'run', return_value=mock.Mock(returncode=19)) as build, \
                    mock.patch.object(runner.subprocess, 'check_output') as env:
                self.assertEqual(runner.lint('lake', options, ['Purelib.A', 'scripts.Harness'], {}), 19)
            build.assert_called_once_with(['lake', *options, 'build', '+Purelib.A', '+scripts.Harness'],
                                          cwd=runner.ROOT)
            env.assert_not_called()


class NativeBuildTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='ccl-lint-native-build-test-')
        self.root = Path(self.temp.name)
        self.cache = self.root / 'cache'
        self.helper = self.root / 'RunBuiltinLint.lean'
        self.helper.write_text(runner.HELPER)
        self.lean = self.root / 'bin/lean'
        for name in ('bin/lean', 'bin/leanc', 'bin/clang', 'lib/lean/libLake.a', 'lib/lean/libLean.a',
                     'lib/lean/libInit.a', 'lib/lean/libStd.a', 'lib/lean/libleancpp.a', 'lib/lean/libleanrt.a'):
            p = self.root / name
            p.parent.mkdir(parents=True, exist_ok=True)
            p.write_bytes(b'compiler fixture')

    def tearDown(self):
        self.temp.cleanup()

    def build(self, environment=None):
        paths = [Path(runner.__file__), *[p for p in self.root.rglob('*')
                                        if p.is_file() and self.cache not in p.parents]]
        files, inputs = runner.checked_fingerprints(paths)
        return runner.build_native_worker(str(self.lean), {'LEAN_SYSROOT': str(self.root), **(environment or {})}, self.helper,
                                          self.cache, 'retained-support-key', {'files': files}, inputs)

    def compile(self, command, **kwargs):
        output = Path(command[command.index('-o') + 1])
        if command[0] == str(self.lean):
            Path(command[command.index('-c') + 1]).write_text(
                'res = runtime_initialize_RunBuiltinLint(1 /* builtin */);')
        else:
            c_source = Path(command[command.index('-o') + 2])
            self.assertIn('res = initialize_RunBuiltinLint(1 /* builtin */);', c_source.read_text())
            self.assertIn('-Wl,--export-dynamic', command)
            self.assertIn('-Wl,--whole-archive', command)
            output.write_bytes(b'linked worker fixture')

    def test_native_build_reuse_corruption_and_library_invalidation(self):
        with mock.patch.object(runner.subprocess, 'run', side_effect=self.compile) as compiler:
            binary = self.build()
            self.assertEqual(compiler.call_count, 2)
            self.assertEqual(self.build(), binary)
            self.assertEqual(compiler.call_count, 2)
            library = self.root / 'lib/lean/libLean.a'
            library.write_bytes(b'changed library')
            replacement = self.build()
            self.assertNotEqual(replacement, binary)
            self.assertEqual(compiler.call_count, 4)
            replacement.write_bytes(b'corrupt executable')
            with self.assertRaisesRegex(ValueError, 'corrupt native'):
                self.build()

    def test_changed_compiler_inputs_leave_no_native_build_receipt(self):
        def mutate(command, **kwargs):
            self.compile(command, **kwargs)
            self.helper.write_text('changed during native build')
        with mock.patch.object(runner.subprocess, 'run', side_effect=mutate):
            with self.assertRaisesRegex(ValueError, 'inputs changed during native'):
                self.build()
        self.assertEqual(list(self.cache.glob('native/*/build.json')), [])

    def test_custom_c_compiler_selects_a_distinct_bound_native_build(self):
        custom = self.root / 'bin/custom-cc'
        custom.write_bytes(b'custom compiler')
        custom.chmod(0o755)
        with mock.patch.object(runner.subprocess, 'run', side_effect=self.compile) as compiler:
            default = self.build()
            selected = self.build({'LEAN_CC': str(custom)})
            self.assertNotEqual(default, selected)
            self.assertEqual(self.build({'LEAN_CC': str(custom)}), selected)
            self.assertEqual(compiler.call_count, 4)
            custom.write_bytes(b'changed custom compiler')
            self.assertNotEqual(self.build({'LEAN_CC': str(custom)}), selected)
            self.assertEqual(compiler.call_count, 6)


class CheckpointTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='ccl-lint-runner-test-')
        self.root = Path(self.temp.name)
        self.artifact = self.root / 'A.olean'
        self.artifact.write_bytes(b'original compiled input')
        self.helper = self.root / 'helper.lean'
        self.helper.write_text(runner.HELPER)
        self.lean = self.root / 'lean'
        self.lean.write_text('#!/usr/bin/env python3\nimport os,sys,time,signal\n'
                             "child_file=os.environ.get('TEST_CHILD_FILE')\n"
                             "if child_file:\n"
                             " child=os.fork()\n"
                             " if child==0:\n"
                             "  signal.signal(signal.SIGTERM,signal.SIG_IGN)\n"
                             "  with open(child_file,'w') as out: out.write(str(os.getpid()))\n"
                             "  time.sleep(20)\n"
                             "  os._exit(0)\n"
                             " while not os.path.exists(child_file): time.sleep(0.01)\n"
                             "time.sleep(float(os.environ.get('TEST_LINT_SLEEP','0')))\n"
                             "print('checked '+sys.argv[-1])\n"
                             "raise SystemExit(int(os.environ.get('TEST_LINT_EXIT','0')))\n")
        self.lean.chmod(0o755)
        self.cache = self.root / 'cache'
        self.inputs = {p: runner.signature(p) for p in (self.artifact, self.helper, self.lean)}
        self.graph = {name: {'files': [str(self.artifact)], 'imports': []}
                      for name in ('Purelib.A', 'Purelib.B', runner.SUPPORT)}

    def tearDown(self):
        self.temp.cleanup()

    def workers(self, **environment):
        return runner.Workers([str(self.lean)], {**os.environ, **environment}, self.cache,
                              self.inputs, self.graph, {self.helper, self.lean})

    def checked(self, workers, task):
        result = workers.check(task)
        if result[0] == 0 and not result[2]:
            workers.publish([task])
        return result

    def test_one_module_worker_and_completed_reuse_after_interruption(self):
        workers = self.workers()
        code, output, reused = self.checked(workers, ('Purelib.A', 'key-a'))
        self.assertEqual((code, output, reused), (0, b'checked Purelib.A\n', False))
        workers.stop()
        with self.assertRaises(InterruptedError):
            self.checked(workers, ('Purelib.B', 'key-b'))
        resumed = self.workers()
        self.assertEqual(self.checked(resumed, ('Purelib.A', 'key-a')), (0, output, True))
        self.assertEqual(self.checked(resumed, ('Purelib.B', 'key-b')), (0, b'checked Purelib.B\n', False))

    def test_batch_publishes_only_completed_passes_with_shared_inputs_checked_once(self):
        workers = self.workers()
        tasks = [('Purelib.A', 'a'), ('Purelib.B', 'b')]
        for task in tasks:
            self.assertEqual(workers.check(task)[0], 0)
            self.assertFalse((self.cache / 'results' / task[1] / 'pass.json').exists())
        with mock.patch.object(runner, 'signature', wraps=runner.signature) as checked:
            workers.publish(tasks)
        self.assertEqual(checked.call_count, len(self.inputs))
        for task in tasks:
            self.assertTrue(workers.check(task)[2])

    def test_mutated_batch_inputs_publish_no_passes(self):
        workers = self.workers()
        tasks = [('Purelib.A', 'a'), ('Purelib.B', 'b')]
        for task in tasks:
            workers.check(task)
        self.artifact.write_bytes(b'changed after workers completed')
        with self.assertRaisesRegex(ValueError, 'inputs changed'):
            workers.publish(tasks)
        self.assertEqual(list(self.cache.glob('results/*/pass.json')), [])

    def test_failed_modules_never_create_pass_receipt(self):
        workers = self.workers(TEST_LINT_EXIT='7')
        self.assertEqual(self.checked(workers, ('Purelib.A', 'failed'))[0], 7)
        self.assertFalse((self.cache / 'results/failed/pass.json').exists())
        self.assertFalse(self.checked(self.workers(), ('Purelib.A', 'failed'))[2])

    def test_running_worker_stops_and_unfinished_module_is_rerun(self):
        workers = self.workers(TEST_LINT_SLEEP='20')
        result = []
        thread = threading.Thread(target=lambda: result.append(self.checked(workers, ('Purelib.A', 'stopped'))))
        thread.start()
        try:
            deadline = time.monotonic() + 3
            while time.monotonic() < deadline:
                with workers.lock:
                    if workers.processes:
                        break
                time.sleep(0.01)
            else:
                self.fail('checker did not start')
        finally:
            workers.stop()
            thread.join(timeout=3)
        self.assertFalse(thread.is_alive())
        self.assertNotEqual(result[0][0], 0)
        self.assertFalse((self.cache / 'results/stopped/pass.json').exists())
        self.assertEqual(self.checked(self.workers(), ('Purelib.A', 'stopped')),
                         (0, b'checked Purelib.A\n', False))

    def test_changed_input_rejected_before_publishing_pass(self):
        self.artifact.write_bytes(b'changed private proof input with a different size')
        with self.assertRaisesRegex(ValueError, 'inputs changed'):
            self.checked(self.workers(), ('Purelib.A', 'stale'))
        self.assertFalse((self.cache / 'results/stale/pass.json').exists())

    def test_digest_and_signature_cannot_straddle_mutation(self):
        digest = runner.sha

        def mutate_after_digest(path):
            value = digest(path)
            Path(path).write_bytes(b'changed immediately after hashing, before the signature')
            return value

        with mock.patch.object(runner, 'sha', side_effect=mutate_after_digest):
            with self.assertRaisesRegex(ValueError, 'changed during fingerprinting'):
                runner.checked_fingerprints([self.artifact])

    def test_tool_identity_rejects_mutation_between_digest_and_signature(self):
        for name in ('scripts/run-lake.sh', 'scripts/linting/lake_args.py',
                     'scripts/linting/providers.py', 'scripts/nanoda/input_key.py',
                     'lakefile.toml', 'lake-manifest.json', 'bin/leanc', 'bin/clang'):
            path = self.root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(b'tool fixture')
        digest = runner.sha

        def mutate_helper_after_digest(path):
            value = digest(path)
            if Path(path) == self.helper:
                self.helper.write_text('changed helper immediately after its digest')
            return value

        with mock.patch.object(runner, 'ROOT', self.root), \
                mock.patch.object(runner, 'sha', side_effect=mutate_helper_after_digest):
            with self.assertRaisesRegex(ValueError, 'changed during fingerprinting'):
                runner.tool_identity(str(self.lean), str(self.lean),
                                     {'LEAN_SYSROOT': str(self.root)}, [], self.helper, {})

    def test_term_resistant_descendants_stopped_after_leader_exit_or_cancellation(self):
        for cancel in (False, True):
            with self.subTest(cancel=cancel):
                child_file = self.root / f'child-{cancel}.pid'
                workers = self.workers(TEST_CHILD_FILE=str(child_file),
                                       TEST_LINT_SLEEP='20' if cancel else '0')
                result = []
                key = f'child-{cancel}'
                thread = threading.Thread(target=lambda: result.append(self.checked(workers, ('Purelib.A', key))))
                thread.start()
                try:
                    deadline = time.monotonic() + 3
                    while not child_file.exists() and time.monotonic() < deadline:
                        time.sleep(0.01)
                    self.assertTrue(child_file.exists(), 'descendant did not start')
                    if cancel:
                        workers.stop()
                    thread.join(timeout=3)
                    self.assertFalse(thread.is_alive(), 'worker cleanup did not finish')
                    pid = int(child_file.read_text())
                    status = Path(f'/proc/{pid}/stat')
                    deadline = time.monotonic() + 2
                    while status.exists() and status.read_text().split()[2] != 'Z' \
                            and time.monotonic() < deadline:
                        time.sleep(0.01)
                    self.assertTrue(not status.exists() or status.read_text().split()[2] == 'Z',
                                    'TERM-resistant descendant remains live')
                    self.assertEqual(bool(result[0][0]), cancel)
                finally:
                    workers.stop()
                    thread.join(timeout=3)

    def test_corrupt_output_rejected(self):
        self.checked(self.workers(), ('Purelib.A', 'corrupt'))
        (self.cache / 'results/corrupt/output.log').write_text('altered')
        with self.assertRaisesRegex(ValueError, 'corrupt lint result'):
            self.checked(self.workers(), ('Purelib.A', 'corrupt'))

    def test_input_key_binds_private_ir_and_dependencies(self):
        files = {'A.olean': 'public', 'A.olean.private': 'private', 'A.olean.server': 'server',
                 'A.ir': 'ir', 'B.olean': 'dependency'}
        data = {'modules': [{'name': 'A', 'imports': ['B'],
                             'files': [str(self.root / p) for p in
                                       ('A.olean', 'A.olean.server', 'A.olean.private')]},
                            {'name': 'B', 'imports': [], 'files': [str(self.root / 'B.olean')]}]}
        hashes = {str((self.root / p).resolve()): value for p, value in files.items()}
        original = runner.INPUTS.module_keys(data, hashes)['A']
        for part in ('A.olean.private', 'A.ir', 'B.olean'):
            changed = {**hashes, str((self.root / part).resolve()): 'changed'}
            self.assertNotEqual(runner.INPUTS.module_keys(data, changed)['A'], original)

    def test_missing_private_or_interpreter_inputs_rejected_before_checker(self):
        modules = []
        for name in ('Purelib.A', runner.SUPPORT):
            main = self.root / Path(*name.split('.')).with_suffix('.olean')
            main.parent.mkdir(parents=True, exist_ok=True)
            files = [main, Path(str(main) + '.server'), Path(str(main) + '.private')]
            for path in [*files, main.with_suffix('.ir')]:
                path.write_bytes(b'fixture input')
            modules.append({'name': name, 'imports': [], 'files': list(map(str, files))})
        data = {'schema': 1, 'roots': ['Purelib.A', runner.SUPPORT], 'modules': modules}
        main = self.root / 'Purelib/A.olean'
        for missing in (Path(str(main) + '.private'), main.with_suffix('.ir')):
            with self.subTest(missing=missing):
                missing.unlink()
                with mock.patch.object(runner, 'inventory', return_value=(data, None)), \
                        mock.patch.object(runner.Workers, 'check') as checker:
                    with self.assertRaises((OSError, ValueError)):
                        runner.bind_inputs(['Purelib.A'], [self.root], self.cache)
                checker.assert_not_called()
                missing.write_bytes(b'fixture input')

    def test_cached_node_paths_keep_exact_original_completed_check_scope(self):
        modern = [self.artifact, Path(str(self.artifact) + '.server'),
                  Path(str(self.artifact) + '.private'), self.artifact.with_suffix('.ir')]
        dependency = self.root / 'B.olean'
        shared = self.root / 'C.olean'
        source = self.root / 'Purelib/A.lean'
        source.parent.mkdir(parents=True, exist_ok=True)
        for path in [*modern[1:], dependency, shared, source]:
            path.write_bytes(b'fixture input')
        self.inputs.update({p: runner.signature(p) for p in [*modern[1:], dependency, shared, source]})
        self.graph = {
            'Purelib.A': {'files': list(map(str, modern[:3])), 'imports': ['Purelib.B', 'Purelib.C']},
            'Purelib.B': {'files': [str(dependency)], 'imports': ['Purelib.C']},
            'Purelib.C': {'files': [str(shared)], 'imports': []},
            runner.SUPPORT: {'files': [str(dependency)], 'imports': ['Purelib.C']}}
        expected, reached, pending = {self.helper, self.lean}, set(), ['Purelib.A', runner.SUPPORT]
        with mock.patch.object(runner, 'ROOT', self.root):
            while pending:
                name = pending.pop()
                if name in reached:
                    continue
                reached.add(name)
                node = self.graph[name]
                expected.update(Path(p).resolve() for p in node['files'])
                if len(node['files']) == 3:
                    expected.add(Path(node['files'][0]).with_suffix('.ir').resolve())
                original_source = runner.ROOT / (name.replace('.', '/') + '.lean')
                if original_source in self.inputs:
                    expected.add(original_source)
                pending.extend(node['imports'])
            workers = self.workers()
            with mock.patch.object(runner, 'signature', wraps=runner.signature) as checked:
                workers.validate_completed_inputs(['Purelib.A'])
        self.assertEqual({call.args[0] for call in checked.call_args_list}, expected)
        self.assertEqual(checked.call_count, len(expected))


if __name__ == '__main__':
    unittest.main()
