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
