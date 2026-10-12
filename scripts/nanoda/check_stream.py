#!/usr/bin/env python3
"""Check one complete nanoda stream, caching success by exact semantic inputs.

This certifies checker success for these bytes only. The caller remains
responsible for validating export provenance and required-root coverage.
"""
import argparse
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

POLICY = 'nanoda-empty-axioms-no-skips-exact-count-v3'


def digest(path):
    with path.open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def result(report, expected_declarations=None):
    successes = re.findall(r'^Checked (0|[1-9][0-9]*) declarations with no errors$', report, re.M)
    if len(successes) != 1 or 'skipping exported' in report:
        raise ValueError('nanoda did not report one complete, non-skipping check:\n' + report)
    count = int(successes[0])
    if count == 0 and expected_declarations != 0:
        raise ValueError('an empty check requires independently validated zero declarations')
    if expected_declarations is not None and count != expected_declarations:
        raise ValueError(f'nanoda checked {count} declarations; expected {expected_declarations}')
    axioms = []
    for line in report.splitlines():
        if line.startswith('axiom '):
            raise ValueError('nanoda reported a forbidden axiom: ' + line)
    return {'declarations': int(successes[0]), 'axioms': sorted(set(axioms)), 'report': report}


def check(stream, checker, config, cache, expected_declarations=None):
    stream, checker, config, cache = map(Path, (stream, checker, config, cache))
    config_bytes = config.read_bytes()
    settings = json.loads(config_bytes)
    for field in ['use_stdin', 'print_axioms', 'print_success_message']:
        if settings.get(field) is not True:
            raise ValueError(f'nanoda checking requires {field}=true')
    if settings.get('unsafe_permit_all_axioms') is not False:
        raise ValueError('nanoda checking requires unsafe_permit_all_axioms=false')
    if settings.get('permitted_axioms') != []:
        raise ValueError('nanoda checking requires permitted_axioms=[]')
    if settings.get('unpermitted_axiom_hard_error') is not True:
        raise ValueError('nanoda checking requires unpermitted_axiom_hard_error=true')
    identity = {'stream': digest(stream), 'checker': digest(checker),
                'config': hashlib.sha256(config_bytes).hexdigest(), 'policy': POLICY,
                'helper': digest(Path(__file__)),
                'expected_declarations': expected_declarations}
    key = hashlib.sha256(json.dumps(identity, sort_keys=True).encode()).hexdigest()
    cache.mkdir(parents=True, exist_ok=True)
    receipt = cache / (key + '.json')
    with (cache / (key + '.lock')).open('w') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        if receipt.exists():
            saved = json.loads(receipt.read_text())
            if saved.get('schema') != 1 or saved.get('identity') != identity:
                raise ValueError(f'invalid nanoda checker receipt: {receipt}')
            checked = result(saved['result']['report'], expected_declarations)
            if checked != saved['result']:
                raise ValueError(f'inconsistent nanoda checker receipt: {receipt}')
            return checked, True
        # Run with the exact configuration bytes named by the identity, even if
        # the caller later rewrites its temporary runtime configuration file.
        with tempfile.TemporaryDirectory(prefix='nanoda-check-', dir=cache) as temporary:
            frozen = Path(temporary) / 'config.json'
            frozen.write_bytes(config_bytes)
            with stream.open('rb') as source:
                process = subprocess.run([str(checker.resolve()), str(frozen.resolve())],
                                         stdin=source, stdout=subprocess.PIPE,
                                         stderr=subprocess.STDOUT, text=True)
            if process.returncode:
                raise RuntimeError(f'nanoda exited {process.returncode}:\n{process.stdout}')
            checked = result(process.stdout, expected_declarations)
            # Do not publish success under an identity whose inputs changed
            # during checking. Export producers should already be immutable.
            if digest(stream) != identity['stream'] or digest(checker) != identity['checker']:
                raise ValueError('nanoda input changed during checking')
            pending = Path(temporary) / 'receipt.json'
            pending.write_text(json.dumps({'schema': 1, 'identity': identity,
                                          'result': checked}, sort_keys=True) + '\n')
            os.replace(pending, receipt)
        return checked, False


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--checker', required=True, type=Path)
    parser.add_argument('--config', required=True, type=Path)
    parser.add_argument('--cache', required=True, type=Path)
    parser.add_argument('--expected-declarations', type=int)
    parser.add_argument('stream', type=Path)
    args = parser.parse_args()
    if args.expected_declarations is not None and args.expected_declarations < 0:
        parser.error('--expected-declarations must be nonnegative')
    checked, retained = check(args.stream, args.checker, args.config, args.cache, args.expected_declarations)
    if retained:
        import sys
        print(f'nanoda: retaining checked stream: {args.stream}', file=sys.stderr)
    print(checked['report'], end='')


if __name__ == '__main__':
    main()
