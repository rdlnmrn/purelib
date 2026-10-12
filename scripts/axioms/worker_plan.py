#!/usr/bin/env python3
"""Partition exact audit misses without combining standalone entrypoint environments.

Lake-declared script owners and their compiled importing roots receive independent
workers. Ordinary mathematical modules keep the checker's dependency clusters.
The scheduler, rather than this partition, bounds concurrently running workers.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path


from scripts.verification.environments import configured_entrypoints, entrypoint_importers


def plan(records: list[tuple[str, str]], imports: dict[str, list[str]],
         entrypoints: set[str], jobs: int) -> list[list[tuple[str, str]]]:
    """Preserve each selected (surface, scanned module) exactly once."""
    if jobs < 1:
        raise ValueError('worker jobs must be positive')
    if len(records) != len(set(records)):
        raise ValueError('duplicate selected audit record')
    isolated = []
    clusters: list[list[tuple[str, str]]] = [[] for _ in range(jobs)]
    containing = entrypoint_importers(imports, entrypoints)
    for index, record in enumerate(records):
        surface, module = record
        if surface == 'project':
            if module not in imports:
                raise ValueError(f'missing selected compiled module: {module}')
            if module in containing:
                isolated.append([record])
                continue
        elif surface != 'canonical' or module != '@canonical':
            raise ValueError(f'invalid audit surface: {record}')
        if jobs == 1:
            worker = 0
        elif surface == 'canonical':
            worker = 1
        elif jobs == 2:
            worker = 0 if module.startswith('formalisations.DivineProportions.') else 1
        elif module.startswith('formalisations.DivineProportions.'):
            worker = 0
        elif module.startswith(('CCL.', 'Purelib.Riemann.', 'Purelib.CCL.', 'Purelib.RootIsolation.')):
            worker = 1 % jobs
        elif module.startswith(('Purelib.Measure.', 'Purelib.Rotations.', 'Purelib.Geometry.Rotations.',
                                'formalisations.RationalRotations.')):
            worker = 2 % jobs
        else:
            worker = index % jobs
        clusters[worker].append(record)
    groups = [group for group in clusters if group] + isolated
    flattened = [record for group in groups for record in group]
    if sorted(flattened) != sorted(records):
        raise ValueError('worker plan did not preserve exact selected audit records')
    return groups


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path, required=True)
    parser.add_argument('--jobs', type=int, required=True)
    parser.add_argument('misses', type=Path)
    parser.add_argument('inventory', type=Path)
    args = parser.parse_args()
    try:
        rows = [line.split('\t') for line in args.misses.read_text().splitlines()]
        if any(len(row) != 4 for row in rows):
            raise ValueError('malformed audit cache miss record')
        inventory = json.loads(args.inventory.read_text())
        if inventory.get('schema') != 1:
            raise ValueError('unsupported compiled module inventory')
        modules = inventory['modules']
        imports = {module['name']: module['imports'] for module in modules}
        if len(imports) != len(modules):
            raise ValueError('duplicate compiled inventory module')
        groups = plan([(row[0], row[1]) for row in rows], imports,
                      configured_entrypoints(args.repo), args.jobs)
        for worker, group in enumerate(groups):
            for surface, module in group:
                print(f'{worker}\t{surface}\t{module}')
    except (KeyError, ValueError, OSError) as error:
        parser.exit(1, f'axiom worker planning failed: {error}\n')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
