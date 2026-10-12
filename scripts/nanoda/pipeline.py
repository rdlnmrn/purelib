"""Prepare native compatible graphs and independently check every selected group.

The shell frontdoor performs the warnings-fatal build. This coordinator consumes
complete compiled artifacts, keeps exact input/export/check receipts, and never
combines conflicting standalone declaration environments.
"""

import argparse
import json
from pathlib import Path
import signal
import sys
import time

from scripts.lean_module_data.paths import search_path
from .artifact_inputs import compiled_inputs, digest, identity, verify_inputs
from .build_exporter import build
from .export_cache import atomic_json
from .planning import group_inputs, plan, retained_inputs, reusable_inputs
from .processes import ProcessSessions
from .scheduling import schedule


from scripts.paths import ROOT
POLICY = 'native-private-artifacts-complete-audit-roots-one-compatible-graph-v1'


def _run(manifest, cache, checker, config, sessions, *, exporters=3, checkers=3, pipeline=True):
    """Retain successful work independently of worker counts and request ordering."""
    modules = Path(manifest).read_text().splitlines()
    if not modules or len(set(modules)) != len(modules) or any(not module.strip() for module in modules):
        raise ValueError('selected module inventory is empty, repeated or contains blank entries')
    cache = Path(cache).resolve()
    checker, config = Path(checker).resolve(), Path(config).resolve()
    search = search_path()
    started = time.monotonic()
    binary = build(cache / 'nanoda-tools', sessions=sessions)
    producer_seconds = time.monotonic() - started
    before = time.monotonic()
    context = compiled_inputs(modules, search)
    input_seconds = time.monotonic() - before
    groups = plan(modules, context, ROOT)
    tools = [*sorted(Path(__file__).parent.glob('*.py')),
             *sorted((ROOT / 'scripts/lean_module_data').glob('*.py'))]
    tools.extend([ROOT / 'scripts/verification/environments.py', ROOT / 'scripts/paths.py'])
    request = {'schema': 1, 'modules': modules, 'compiled_inputs': identity(context),
               'producer_sha256': digest(binary), 'policy': POLICY,
               'tool_sources': {str(path): digest(path) for path in tools},
               'checker_sha256': digest(checker), 'config_sha256': digest(config),
               'groups': groups}
    request_dir = cache / 'nanoda-runs' / identity(request)
    request_dir.mkdir(parents=True, exist_ok=True)
    atomic_json(request_dir / 'request.json', request)
    atomic_json(request_dir / 'inputs.json', context)
    inputs = {}
    retained = retained_inputs(cache / 'nanoda-inputs')
    for index, group in enumerate(groups):
        incoming = reusable_inputs(group_inputs(context, group), retained)
        path = cache / 'nanoda-inputs' / (identity(incoming) + '.json')
        if path.exists():
            if json.loads(path.read_text()) != incoming:
                raise ValueError(f'corrupt compiled input receipt: {path}')
        else:
            atomic_json(path, incoming)
        inputs[tuple(group)] = path
    def worker(command):
        result = sessions.run([sys.executable, '-m', 'scripts.nanoda.worker', *map(str, command)])
        if result.returncode:
            raise RuntimeError(f'nanoda worker exited {result.returncode}: {command}')
        return json.loads(result.stdout)
    def export(group):
        value = worker(['export', '--inputs', inputs[tuple(group)], '--binary', binary,
                        '--cache', cache / 'nanoda-native', '--policy', POLICY])
        print(f'nanoda: ready group ({len(group)} modules, {value["coverage"]["roots"]} roots, '
              f'{value["coverage"]["declarations"]} declarations; retained={value["retained"]})',
              flush=True)
        return value
    def check(value):
        checked = worker(['check', '--group', value['group'], '--receipt-sha256', value['receipt_sha256'],
                          '--checker', checker, '--config', config, '--cache', cache / 'nanoda-checked'])
        if checked['result']['declarations'] != value['coverage']['declarations']:
            raise ValueError('checker receipt does not cover the exported declarations')
        print(checked['result']['report'], end='', flush=True)
        return checked
    outputs = schedule(groups, export, check, exporters=exporters, checkers=checkers,
                       cancel=sessions.cancel, pipeline=pipeline)
    verify_inputs(context, search)
    if digest(binary) != request['producer_sha256']:
        raise ValueError('native producer changed during the pipeline')
    if digest(checker) != request['checker_sha256'] or digest(config) != request['config_sha256']:
        raise ValueError('checker or configuration changed during the pipeline')
    if any(digest(path) != expected for path, expected in request['tool_sources'].items()):
        raise ValueError('coordinator or verification tools changed during the pipeline')
    report = {'schema': 1, 'request': request, 'groups': outputs,
              'producer_build_seconds': producer_seconds, 'compiled_inventory_hash_seconds': input_seconds,
              'pipeline_wall_seconds': time.monotonic() - started}
    atomic_json(request_dir / 'checked.json', report)
    print(f'nanoda: all {len(groups)} module sets checked without errors or axioms', flush=True)
    return report


def run(manifest, cache, checker, config, *, exporters=3, checkers=3, pipeline=True):
    """Own cancellation throughout preparation, export and independent checking."""
    sessions = ProcessSessions()
    previous = signal.getsignal(signal.SIGTERM)
    def interrupted(*_):
        raise KeyboardInterrupt
    signal.signal(signal.SIGTERM, interrupted)
    try:
        return _run(manifest, cache, checker, config, sessions,
                    exporters=exporters, checkers=checkers, pipeline=pipeline)
    finally:
        signal.signal(signal.SIGTERM, previous)
        sessions.cancel()


def main():
    """Run the native coordinator against an explicit built module manifest."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--manifest', type=Path, required=True)
    parser.add_argument('--cache', type=Path, required=True)
    parser.add_argument('--checker', type=Path, required=True)
    parser.add_argument('--config', type=Path, required=True)
    parser.add_argument('--exporters', type=int, default=3)
    parser.add_argument('--checkers', type=int, default=3)
    parser.add_argument('--sequential', action='store_true')
    args = parser.parse_args()
    if min(args.exporters, args.checkers) < 1:
        parser.error('worker counts must be positive')
    run(args.manifest, args.cache, args.checker, args.config, exporters=args.exporters,
        checkers=args.checkers, pipeline=not args.sequential)


if __name__ == '__main__':
    main()
