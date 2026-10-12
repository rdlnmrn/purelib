"""Build the pinned meta-phase native exporter with its complete own initialization.

Lean 4.32's emitted standalone C main calls the runtime initializer even for a
meta entrypoint. Its public full module initializer is the embedding entrypoint
that also initializes the exporter's meta constants. Adjust that one bootstrap
call; target artifacts remain imported with loadExts=false and plugins=[].
"""

import argparse
import fcntl
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

from .artifact_inputs import compiled_inputs, digest, identity, verify_inputs
from .export_cache import atomic_json


from scripts.paths import ROOT
SOURCE = ROOT / 'scripts/nanoda/NativeExport.lean'
RUNNER = ROOT / 'scripts/run-lake.sh'


def initialize_meta_entrypoint(source):
    """Select the supported full initializer at the pinned generated main call."""
    old = 'res = runtime_initialize_scripts_nanoda_NativeExport(1 /* builtin */);'
    new = 'res = initialize_scripts_nanoda_NativeExport(1 /* builtin */);'
    if source.count(old) != 1:
        raise ValueError('pinned meta entrypoint bootstrap no longer matches generated C')
    return source.replace(old, new)


def build(cache, *, sessions=None):
    """Atomically retain a source/compiler-bound native executable."""
    def invoke(command):
        result = (sessions.run(command) if sessions is not None else
                  subprocess.run(command, stdout=subprocess.PIPE, text=True))
        result.check_returncode()
        return result.stdout
    sysroot = Path(invoke([str(RUNNER), 'env', 'lean', '--print-prefix']).strip())
    bindings = {'schema': 1, 'bootstrap': 'full-own-meta-module-initialization-v1',
                'sources': {str(path): digest(path) for path in
                            (SOURCE, Path(__file__), Path(__file__).with_name('artifact_inputs.py'), RUNNER)},
                'compiler': {str(sysroot / 'bin/lean'): digest(sysroot / 'bin/lean'),
                             str(sysroot / 'bin/leanc'): digest(sysroot / 'bin/leanc')},
                'sysroot': str(sysroot), 'options': ['warningAsError=true', 'weak.linter.missingDocs=true', '-O3']}
    search = [sysroot / 'lib/lean']
    bindings['compiled_inputs'] = compiled_inputs(
        ['Lean', 'Std.Data.HashMap.Basic', 'Lean.Compiler.CSimpAttr'], search)
    # Linking embeds the pinned native libraries; bind them as well as the compiler.
    for path in sorted((sysroot / 'lib/lean').glob('*.a')):
        bindings['compiler'][str(path)] = digest(path)
    folder = Path(cache) / identity(bindings)
    folder.mkdir(parents=True, exist_ok=True)
    with (folder / 'build.lock').open('w') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        binary, receipt = folder / 'nanoda-export', folder / 'build.json'
        if receipt.exists():
            saved = json.loads(receipt.read_text())
            if saved['bindings'] != bindings or digest(binary) != saved['binary_sha256']:
                raise ValueError(f'corrupt native exporter build: {folder}')
            return binary
        with tempfile.TemporaryDirectory(prefix='pending-', dir=folder) as temporary:
            pending = Path(temporary)
            c_source = pending / 'NativeExport.c'
            output = invoke([str(RUNNER), 'env', 'lean', '-R', str(ROOT), '-DwarningAsError=true',
                            '-Dweak.linter.missingDocs=true', '-o', str(pending / 'NativeExport.olean'),
                            '-c', str(c_source), str(SOURCE)])
            if output:
                print(output, end='', file=sys.stderr)
            c_source.write_text(initialize_meta_entrypoint(c_source.read_text()))
            output = invoke([str(RUNNER), 'env', 'leanc', '-O3', '-o', str(pending / 'nanoda-export'),
                             str(c_source)])
            if output:
                print(output, end='', file=sys.stderr)
            if any(digest(path) != expected for path, expected in bindings['sources'].items()):
                raise ValueError('exporter source changed during native build')
            verify_inputs(bindings['compiled_inputs'], search)
            if any(digest(path) != expected for path, expected in bindings['compiler'].items()):
                raise ValueError('compiler or native library changed during native build')
            os.replace(pending / 'nanoda-export', binary)
            atomic_json(receipt, {'bindings': bindings, 'binary_sha256': digest(binary)})
        return binary


def main():
    """Print the verified executable path for production and fixture callers."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cache', type=Path, default=ROOT / '.lake/nanoda-tools')
    args = parser.parse_args()
    print(build(args.cache))


if __name__ == '__main__':
    main()
