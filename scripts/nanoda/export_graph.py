#!/usr/bin/env python3
"""Produce a retained declaration graph with compiled-dependency provenance.

Builds selected project modules unless --no-build is supplied. The latter
requires current artifacts. Stdout contains only the completed graph path.
Reporting/analysis changes do not invalidate a compatible producer result.
"""
import argparse
import fcntl
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time

from scripts.paths import ROOT


from . import input_key as inputs
from . import graph as graphs


def cached_graph(directory, identity, command, files, metadata):
    directory.mkdir(parents=True, exist_ok=True)
    output = directory / 'graph.jsonl'
    receipt = directory / 'graph.receipt.json'
    provenance = directory / 'provenance.json'
    validator = inputs.identity({'analyzer': inputs.digest(graphs.__file__),
                                 'wrapper': inputs.digest(__file__)})
    with (directory / 'lock').open('w') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        if provenance.exists():
            saved = json.loads(provenance.read_text())
            if saved['identity'] != identity or saved['command'] != command:
                raise ValueError('graph producer identity mismatch')
        else:
            inputs.atomic_json(provenance, {'identity': identity, 'command': command,
                                           'producer': metadata})
        had_receipt = receipt.exists()
        if had_receipt:
            saved = json.loads(receipt.read_text())
            if saved['identity'] != identity or inputs.digest(output) != saved['sha256']:
                raise ValueError('corrupt retained declaration graph')
            if saved.get('validator') == validator:
                return output, True
        # The native producer publishes this filename by atomic rename only
        # after finishing traversal. Recover the narrow interruption window
        # between that publication and our receipt, without rerunning it.
        recovered = output.exists()
        if not recovered:
            invocation = 0
            while (directory / f'graph-{invocation}.log').exists():
                invocation += 1
            with (directory / f'graph-{invocation}.log').open('w') as log:
                subprocess.run(['/usr/bin/time', '-v', '-o',
                                str(directory / f'graph-{invocation}.time'), *command],
                               stdout=log, stderr=subprocess.STDOUT, check=True)
        # A graph must not acquire a successful receipt for inputs changed while
        # the producer was reading them. Preserve unverified output separately.
        if inputs.fingerprint([Path(p) for p in files]) != files:
            output.rename(directory / f'graph-unverified-{time.time_ns()}.jsonl')
            raise ValueError('compiled inputs changed during graph extraction')
        header, nodes = graphs.inventory(output)
        reached = graphs.closure(nodes, [r['name'] for r in header['roots']])
        if reached != set(nodes):
            raise ValueError('graph contains declarations outside the required closure')
        result = {'identity': identity, 'validator': validator, 'sha256': inputs.digest(output),
                  'roots': len(header['roots']), 'declarations': len(nodes),
                  'recovered_publication': recovered and not had_receipt,
                  'revalidated': recovered and had_receipt}
        inputs.atomic_json(receipt, result)
        return output, recovered


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--manifest', type=Path)
    parser.add_argument('--no-build', action='store_true')
    args = parser.parse_args()
    os.chdir(ROOT)
    runner = str(ROOT / 'scripts/run-lake.sh')
    modules = (args.manifest.read_text() if args.manifest else subprocess.check_output(
        ['python3', str(ROOT / 'scripts/project-modules.py'), '--configured-scripts'], text=True))
    names = [line.strip() for line in modules.splitlines() if line.strip()]
    if not names or len(names) != len(set(names)):
        raise ValueError('empty or duplicate graph module inventory')
    if not args.no_build:
        subprocess.run([runner, '--wfail', 'build', *names], stdout=sys.stderr, check=True)
    command_base=['python3', '-m', 'scripts.nanoda.graph_data']
    sysroot = Path(subprocess.check_output([runner, 'env', 'lean', '--print-prefix'], text=True).strip())
    lean_path = subprocess.check_output(
        [runner, 'env', 'printenv', 'LEAN_PATH'], text=True).strip()
    os.environ['LEAN_PATH'] = lean_path
    os.environ['PATH'] = str(sysroot / 'bin') + ':' + os.environ['PATH']
    cache = ROOT / '.lake/nanoda-graphs'
    manifests = cache / 'manifests'; manifests.mkdir(parents=True, exist_ok=True)
    manifest = manifests / (inputs.identity(names) + '.modules')
    contents = '\n'.join(names) + '\n'
    if manifest.exists():
        if manifest.read_text() != contents:
            raise ValueError('corrupt retained graph module manifest')
    else:
        with tempfile.NamedTemporaryFile(mode='w', dir=manifests, delete=False) as pending:
            pending.write(contents)
        os.replace(pending.name, manifest)
    search = [Path(p) for p in lean_path.split(os.pathsep) if p] + [sysroot / 'lib/lean']
    policy = {'format': 1, 'mode': 'declaration-graph',
              'producer': inputs.producer_identity(command_base),
              'lean': inputs.digest(sysroot / 'bin/lean')}
    _, input_receipt, _ = inputs.input_key(manifest, command_base, ROOT / '.lake/nanoda-inputs',
                                          search, inputs.identity(policy))
    provenance = json.loads(input_receipt.read_text())
    # Deliberately do not key the graph by reporting-wrapper source or the
    # opaque input-inventory namespace. Exact producer/data identity suffices.
    identity = {'policy': policy, 'roots': names, 'files': provenance['files']}
    directory = cache / inputs.identity(identity)
    metadata = {'revision': subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip(),
                'diff': subprocess.check_output(['git', 'diff', 'HEAD', '--binary'], text=True),
                'status': subprocess.check_output(['git', 'status', '--short'], text=True),
                'input_receipt': str(input_receipt)}
    command = [*command_base, '--graph', str(manifest), str(directory / 'graph.jsonl')]
    output, retained = cached_graph(directory, identity, command, provenance['files'], metadata)
    print(f'nanoda graph: {"retained" if retained else "produced"} {output}', file=sys.stderr)
    print(output)


if __name__ == '__main__':
    main()
