"""Measure cold and warm production runs in an isolated, retained cache.

Run from the repository root with ``python3 -m scripts.nanoda.benchmark_pipeline``.
The benchmark never clears another run's cache. A completed run records the
exact manifests, emitted stream hashes, declaration multiplicity and process
RSS samples. Pipeline wall time includes hashing and queueing; it is not kernel
checking time. Existing exporter phase messages are retained separately.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import time


from scripts.paths import ROOT


def digest(path):
    """Hash a file without retaining its contents."""
    h = hashlib.sha256()
    with path.open('rb') as source:
        for block in iter(lambda: source.read(1024 * 1024), b''):
            h.update(block)
    return h.hexdigest()


def process_table():
    """Read process identities, ancestry and resident pages from Linux procfs."""
    table = {}
    page_size = os.sysconf('SC_PAGE_SIZE')
    for folder in Path('/proc').iterdir():
        if not folder.name.isdecimal():
            continue
        try:
            stat = (folder / 'stat').read_text()
            fields = stat[stat.rindex(')') + 2:].split()
            table[int(folder.name)] = {
                'parent': int(fields[1]), 'group': int(fields[2]),
                'started': int(fields[19]), 'rss': int(fields[21]) * page_size,
            }
        except (FileNotFoundError, ProcessLookupError):
            continue
    return table


def descendants(table, parent, known):
    """Retain descendants by PID/start time even after their parent exits."""
    owned = {pid for pid, row in table.items()
             if known.get(pid) == row['started']}
    if parent in table:
        owned.add(parent)
    while True:
        added = {pid for pid, row in table.items() if row['parent'] in owned}
        if added <= owned:
            break
        owned.update(added)
    for pid in owned:
        known[pid] = table[pid]['started']
    return owned


def stream_inventory(cache):
    """Count declarations using names local to each independently parsed stream."""
    declarations = set()
    occurrences = 0
    streams = []
    for path in sorted((cache / 'nanoda-native').glob('*/stream.ndjson')):
        names = {0: ()}
        count = 0
        with path.open() as source:
            for line in source:
                record = json.loads(line)
                if 'in' in record:
                    tag = 'str' if 'str' in record else 'num'
                    data = record[tag]
                    names[record['in']] = (*names[data['pre']], (tag, data.get('str', data.get('i'))))
                for tag in ('axiom', 'def', 'opaque', 'thm', 'quot'):
                    if tag in record:
                        declarations.add(names[record[tag]['name']])
                        count += 1
                if 'inductive' in record:
                    for tag in ('types', 'ctors', 'recs'):
                        for data in record['inductive'][tag]:
                            declarations.add(names[data['name']])
                            count += 1
        occurrences += count
        streams.append({'path': str(path), 'sha256': digest(path),
                        'bytes': path.stat().st_size, 'declarations': count})
    if not streams:
        raise ValueError('successful pipeline emitted no streams')
    return {'streams': streams, 'total_bytes': sum(s['bytes'] for s in streams),
            'declaration_occurrences': occurrences, 'distinct_declaration_names': len(declarations),
            'repeated_declaration_names': occurrences - len(declarations)}


def input_inventory(cache):
    """Bind every retained input and checker receipt independently of stream names."""
    return {str(path.relative_to(cache)): digest(path)
            for directory in ('nanoda-inputs', 'nanoda-checked')
            for path in sorted((cache / directory).rglob('*.json'))}


def run_pipeline(folder, phase, environment):
    """Run the real frontdoor, measuring the combined RSS of its owned tree."""
    known, peaks, peak_total = {}, {}, 0
    started = time.monotonic()
    log = folder / f'{phase}.log'
    with log.open('wb') as output:
        process = subprocess.Popen([str(ROOT / 'scripts/check-nanoda.sh')], env=environment,
                                   stdout=output, stderr=subprocess.STDOUT, start_new_session=True)
        try:
            while process.poll() is None:
                table = process_table()
                owned = descendants(table, process.pid, known)
                peak_total = max(peak_total, sum(table[pid]['rss'] for pid in owned))
                for pid in owned:
                    key = f'{pid}:{table[pid]["started"]}'
                    peaks[key] = max(peaks.get(key, 0), table[pid]['rss'])
                time.sleep(0.1)
        except BaseException:
            # Supervisors propagate TERM to the exporter/checker sessions they own.
            if process.poll() is None:
                os.killpg(process.pid, signal.SIGTERM)
                process.wait()
            raise
    elapsed = time.monotonic() - started
    if process.returncode:
        raise RuntimeError(f'{phase} pipeline exited {process.returncode}; see {log}')
    text = log.read_text()
    if 'module sets checked without errors or axioms' not in text:
        raise ValueError(f'{phase} pipeline has no final success report; see {log}')
    return {'wall_seconds': elapsed, 'sampled_peak_combined_rss_bytes': peak_total,
            'sampled_process_peak_rss_bytes': peaks, 'log_sha256': digest(log),
            'export_phase_reports': [line for line in text.splitlines()
                                     if any(key in line for key in ('import_ms=', 'roots_ms=', 'export_ms='))]}


def main():
    """Create one cold run and then replay the same completed cache warm."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--manifest', type=Path)
    parser.add_argument('--exporters', type=int, default=3)
    parser.add_argument('--checker-threads', type=int, default=2)
    parser.add_argument('--checker-instances', type=int, default=3)
    args = parser.parse_args()
    if min(args.exporters, args.checker_threads, args.checker_instances) < 1:
        parser.error('worker counts must be positive')
    folder = args.output.resolve()
    folder.mkdir(parents=True, exist_ok=False)
    manifest = folder / 'selected.modules'
    data = args.manifest.read_bytes() if args.manifest else subprocess.check_output([
        'python3', str(ROOT / 'scripts/project-modules.py'), '--configured-scripts'])
    manifest.write_bytes(data)
    cache = folder / 'cache'
    environment = dict(os.environ, NANODA_CACHE_ROOT=str(cache), NANODA_MODULE_MANIFEST=str(manifest),
                       NANODA_EXPORT_JOBS=str(args.exporters),
                       NANODA_JOBS=str(args.checker_threads), NANODA_POST_EXPORT_CHECKS=str(args.checker_instances))
    report = {'schema': 1, 'manifest_sha256': digest(manifest),
              'frontdoor_sha256': digest(ROOT / 'scripts/check-nanoda.sh'),
              'settings': {key: value for key, value in environment.items() if key.startswith('NANODA_')},
              'rss_sampling_interval_seconds': 0.1,
              'rss_accounting': 'sum of resident pages; shared mappings may be counted more than once'}
    for phase in ('cold', 'warm'):
        if digest(ROOT / 'scripts/check-nanoda.sh') != report['frontdoor_sha256']:
            raise ValueError('frontdoor changed during the benchmark')
        report[phase] = run_pipeline(folder, phase, environment)
        report[phase]['inventory'] = stream_inventory(cache)
        report[phase]['input_and_checker_receipts'] = input_inventory(cache)
        if phase == 'warm' and report['cold']['inventory'] != report['warm']['inventory']:
            raise ValueError('warm replay changed the emitted streams')
        if phase == 'warm' and report['cold']['input_and_checker_receipts'] != report['warm']['input_and_checker_receipts']:
            raise ValueError('warm replay changed its input/checker receipts')
        pending = folder / 'report.json.partial'
        pending.write_text(json.dumps(report, indent=2) + '\n')
        pending.replace(folder / 'report.json')
        print(f'{phase}: {report[phase]["wall_seconds"]:.3f}s; '
              f'sampled peak combined RSS {report[phase]["sampled_peak_combined_rss_bytes"] / 2**30:.3f} GiB',
              flush=True)


if __name__ == '__main__':
    main()
