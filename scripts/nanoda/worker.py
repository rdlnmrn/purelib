"""Isolated native export and independent checker workers for the production scheduler."""

import argparse
import json
from pathlib import Path
import resource
import time

from scripts.lean_module_data.paths import search_path
from .artifact_inputs import digest
from .check_stream import check
from .export_cache import export_group, reload_group


def main():
    """Emit small structured results; complete streams and receipts remain in the cache."""
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest='mode', required=True)
    producer = commands.add_parser('export')
    producer.add_argument('--inputs', type=Path, required=True)
    producer.add_argument('--binary', type=Path, required=True)
    producer.add_argument('--cache', type=Path, required=True)
    producer.add_argument('--policy', required=True)
    consumer = commands.add_parser('check')
    consumer.add_argument('--group', type=Path, required=True)
    consumer.add_argument('--receipt-sha256', required=True)
    consumer.add_argument('--checker', type=Path, required=True)
    consumer.add_argument('--config', type=Path, required=True)
    consumer.add_argument('--cache', type=Path, required=True)
    args = parser.parse_args()
    started = time.monotonic()
    if args.mode == 'export':
        context = json.loads(args.inputs.read_text())
        folder, receipt, hit = export_group(context['selected_modules'], context, args.binary,
                                            args.cache, search_path(), args.policy)
        result = {'group': str(folder.resolve()), 'receipt_sha256': digest(folder / 'complete.json'),
                  'retained': hit, 'coverage': receipt['coverage']}
    else:
        marker = args.group / 'complete.json'
        if digest(marker) != args.receipt_sha256:
            raise ValueError('export receipt changed before checking')
        receipt = json.loads(marker.read_text())
        reload_group(args.group, receipt['binding'])
        checked, hit = check(args.group / 'stream.ndjson', args.checker, args.config, args.cache,
                             receipt['coverage']['declarations'])
        if digest(marker) != args.receipt_sha256:
            raise ValueError('export receipt changed during checking')
        result = {'group': str(args.group.resolve()), 'retained': hit, 'result': checked}
    result['wall_seconds'] = time.monotonic() - started
    # Linux reports KiB; ru_maxrss is a whole-worker peak, not a combined-tree peak.
    result['worker_peak_rss_bytes'] = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss * 1024
    print(json.dumps(result, sort_keys=True))


if __name__ == '__main__':
    main()
