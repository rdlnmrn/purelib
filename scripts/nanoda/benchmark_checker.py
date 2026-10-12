#!/usr/bin/env python3
"""Measure checker worker counts on identical bytes, retaining completed runs."""
import argparse
import fcntl
import json
from pathlib import Path
import subprocess

from scripts.paths import ROOT


from . import input_key as inputs
from . import check_stream as check


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('stream', type=Path)
    parser.add_argument('--jobs', type=int, nargs='+', default=[1, 2])
    args = parser.parse_args()
    if any(n < 1 for n in args.jobs):
        parser.error('worker counts must be positive')
    stream = args.stream.resolve()
    checker = ROOT / '.external/nanoda/target/release/nanoda_bin'
    settings = json.loads((ROOT / 'scripts/nanoda/config.json').read_text())
    reports = []
    for jobs in args.jobs:
        settings['num_threads'] = jobs
        identity = {'stream': inputs.digest(stream), 'checker': inputs.digest(checker),
                    'configuration': dict(settings)}
        directory = ROOT / '.lake/nanoda-checker-benchmarks' / inputs.identity(identity)
        directory.mkdir(parents=True, exist_ok=True)
        config, log, timing, producer = [directory / name for name in
                                         ['config.json', 'checker.log', 'time.json', 'producer.json']]
        lock = (directory / 'lock').open('w')
        fcntl.flock(lock, fcntl.LOCK_EX)
        inputs.atomic_json(config, settings)
        if producer.exists():
            saved = json.loads(producer.read_text())
            if (saved['identity'] != identity or saved['log'] != inputs.digest(log)
                    or saved['timing'] != inputs.digest(timing)):
                raise ValueError('corrupt retained checker benchmark')
            print('retaining checker measurement:', directory, flush=True)
        else:
            with stream.open('rb') as source, log.open('w') as output:
                process = subprocess.run(['/usr/bin/time', '-f',
                    '{"wall_seconds":%e,"user_seconds":%U,"system_seconds":%S,"rss_kib":%M,"exit":%x}',
                    '-o', str(timing), str(checker), str(config)],
                    stdin=source, stdout=output, stderr=subprocess.STDOUT)
            if inputs.digest(stream) != identity['stream'] or inputs.digest(checker) != identity['checker']:
                raise ValueError('checker benchmark input changed during run')
            saved = {'identity': identity, 'exit': process.returncode,
                     'log': inputs.digest(log), 'timing': inputs.digest(timing)}
            inputs.atomic_json(producer, saved)
        if saved['exit']:
            raise RuntimeError(f'checker failed ({saved["exit"]}); retained {directory}')
        checked = check.result(log.read_text())
        report = {'jobs': jobs, 'timing': json.loads(timing.read_text()),
                  'declarations': checked['declarations'], 'axioms': checked['axioms'],
                  'directory': str(directory)}
        inputs.atomic_json(directory / 'checked.json', report)
        reports.append(report)
        lock.close()
        print(json.dumps(report, sort_keys=True), flush=True)
    print(json.dumps(reports, indent=2), flush=True)


if __name__ == '__main__':
    main()
