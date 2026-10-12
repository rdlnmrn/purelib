"""Check hash memoization, recovery, and the native scheduler regression.

Set CCL_TEST_CORE_PREFIX to exercise the real pinned native installer as well.
The integration test uses an isolated cache and two ordinary Lake packages.
"""
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

from scripts.toolchain import prepare_lake as installer


def packages(root):
    provider, consumer = root / 'provider', root / 'consumer'
    for directory in (provider / 'Support', provider / 'Tools', consumer / 'Probe'):
        directory.mkdir(parents=True)
    for package in (provider, consumer):
        (package / 'lean-toolchain').write_text('leanprover/lean4:v4.32.2\n')
    (provider / 'lakefile.toml').write_text('''name = "helpers"
version = "0.1.0"
defaultTargets = ["Support", "Tools"]
[[lean_lib]]
name = "Support"
roots = ["Support.Root"]
globs = ["Support.+"]
[[lean_lib]]
name = "Tools"
roots = ["Tools.P0", "Tools.P1", "Tools.P2", "Tools.P3", "Tools.P4"]
globs = ["Tools.+"]
''')
    for i in range(24):
        imports = ''.join(f'import Support.N{j}\n' for j in range(max(0, i - 3), i))
        (provider / f'Support/N{i}.lean').write_text(
            f'module\n{imports}/-- A diagnostic constant. -/\npublic def Support.n{i} : Nat := {i}\n')
    (provider / 'Support/Root.lean').write_text(
        'module\n' + ''.join(f'public import Support.N{i}\n' for i in range(24)))
    for i in range(5):
        (provider / f'Tools/P{i}.lean').write_text('module\nimport Support.Root\n')
    plugins = ', '.join(f'"helpers/+Tools.P{i}:dynlib"' for i in range(5))
    (consumer / 'lakefile.toml').write_text(
        'name = "consumer"\nversion = "0.1.0"\ndefaultTargets = ["Probe"]\n'
        'dynlibs = ["helpers/Support:shared"]\n' + f'plugins = [{plugins}]\n'
        '[[require]]\nname = "helpers"\npath = "../provider"\n'
        '[[lean_lib]]\nname = "Probe"\nroots = ["Probe.Root"]\n')
    (consumer / 'Probe/Root.lean').write_text(
        'module\n/-- A diagnostic constant. -/\npublic def Probe.value : Nat := 42\n')
    return consumer


class MemoTests(unittest.TestCase):
    def test_unchanged_metadata_does_not_hash(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'file'
            path.write_bytes(b'original')
            rows = [installer.bind(path)]
            with patch.object(installer, 'sha', side_effect=AssertionError('warm rehash')):
                self.assertTrue(installer.valid(rows))

    def test_metadata_change_rehashes_and_corruption_is_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'file'
            path.write_bytes(b'original')
            rows = [installer.bind(path)]
            os.utime(path, ns=(1, 1))
            self.assertTrue(installer.valid(rows))
            path.write_bytes(b'changed!')
            self.assertFalse(installer.valid(rows))
            path.unlink()
            self.assertFalse(installer.valid(rows))

    def test_retargeted_symlink_is_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            first, second, link = (Path(directory) / n for n in ('first', 'second', 'link'))
            first.write_bytes(b'original')
            second.write_bytes(b'changed!')
            link.symlink_to(first)
            rows = [installer.bind(link)]
            link.unlink()
            link.symlink_to(second)
            self.assertFalse(installer.valid(rows))


@unittest.skipUnless(os.environ.get('CCL_TEST_CORE_PREFIX'), 'set CCL_TEST_CORE_PREFIX for native integration')
class NativeTests(unittest.TestCase):
    def test_idempotency_recovery_and_parallel_cli(self):
        prefix = Path(os.environ['CCL_TEST_CORE_PREFIX']).resolve()
        with tempfile.TemporaryDirectory(prefix='ccl-lake-installer-') as directory:
            root = Path(directory)
            cache = root / 'cache'
            lake = installer.prepare(prefix, cache)
            installed = lake.parent.parent
            library = installed / 'lib/lean/libLake_shared.so'
            stamp = library.stat().st_mtime_ns
            self.assertEqual(installer.prepare(prefix, cache), lake)
            self.assertEqual(library.stat().st_mtime_ns, stamp)
            compile_log = next(cache.glob('*.building/compile.log'))
            compile_stamp = compile_log.stat().st_mtime_ns
            library.write_bytes(b'damaged cached native library')
            repaired = installer.prepare(prefix, cache)
            self.assertNotEqual(repaired, lake)
            self.assertEqual(compile_log.stat().st_mtime_ns, compile_stamp)
            self.assertEqual(installer.prepare(prefix, cache), repaired)
            # A missing selection receipt represents an interrupted publication:
            # the checked expensive compile remains reusable.
            next(cache.glob('*.json')).unlink()
            command = [os.sys.executable, '-m', 'scripts.toolchain.prepare_lake',
                       '--prefix', str(prefix), '--cache', str(cache)]
            processes = [subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
                         for _ in range(2)]
            selections = []
            for process in processes:
                stdout, stderr = process.communicate(timeout=60)
                self.assertEqual(process.returncode, 0, stderr.decode())
                selections.append(stdout.decode().strip())
            self.assertEqual(selections[0], selections[1])
            repaired = Path(selections[0])
            self.assertEqual(compile_log.stat().st_mtime_ns, compile_stamp)
            # A changed upstream pin must fail rather than select a stock driver.
            config = json.loads((installer.HERE / 'lake-patch.json').read_text())
            config['native_inputs']['bin/lean'] = '0' * 64
            bad_config = root / 'lake-patch.json'
            bad_config.write_text(json.dumps(config))
            (root / config['patch']).write_bytes((installer.HERE / config['patch']).read_bytes())
            with self.assertRaisesRegex(ValueError, 'unsupported upstream native input'):
                installer.prepare(prefix, cache, bad_config)
            consumer = packages(root / 'packages')
            env = os.environ.copy()
            for name in ('LEAN_SYSROOT', 'LEAN_PATH', 'LEAN_GITHASH', 'LAKE_OVERRIDE_LEAN'):
                env.pop(name, None)
            env.update(LEAN_NUM_THREADS='1', LEAN_ABORT_ON_PANIC='1', ELAN_NO_UPDATE_CHECK='1')
            def run(*args):
                result = subprocess.run([str(repaired), *args], cwd=consumer, env=env,
                                        stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=60)
                self.assertEqual(result.returncode, 0, result.stdout.decode(errors='replace'))
                self.assertNotIn(b'PANIC', result.stdout)
            run('--wfail', 'build', 'Probe')
            for threads in ('8', '24'):
                env['LEAN_NUM_THREADS'] = threads
                for _ in range(10):
                    run('--no-build', '--wfail', 'build', 'Probe.Root:leanArts')
                run('--wfail', 'build', 'Probe')


if __name__ == '__main__':
    unittest.main()
