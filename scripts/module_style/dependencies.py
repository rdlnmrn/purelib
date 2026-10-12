#!/usr/bin/env python3
"""Report compiled declaration dependencies as evidence for module import reviews.

This reads existing artifacts and never builds the selected module. It separates
public signatures, exposed bodies, private signatures, private bodies and proofs;
syntax, tactics and external clients still require source review.
"""
from __future__ import annotations

import argparse
import hashlib
from pathlib import Path
import subprocess
import sys
import os
from scripts.lean_module_data.observations import artifact_pins

from scripts.module_style import core as style

ROOT = style.ROOT
HELPER = ROOT / 'scripts/project-module-data.py'
READER_PARTS = tuple(sorted(HELPER.with_name('lean_module_data').glob('*.py')))


def file_digest(path: Path) -> str:
    """Hash retained source, compiler metadata or review tooling bytes."""
    return hashlib.sha256(path.read_bytes()).hexdigest()


def inputs(path: Path, search) -> dict:
    """Identify the source and selected compiled artifacts used by this report."""
    relative = path.relative_to(ROOT)
    artifact = ROOT / '.lake/build/lib/lean' / relative.with_suffix('.olean')
    artifacts = {}
    for suffix in ('', '.server', '.private'):
        part = Path(str(artifact) + suffix)
        style.require(part.is_file(), f'missing compiled artifact: {part}; build the module first')
        artifacts[part.relative_to(ROOT).as_posix()] = file_digest(part)
    return {'source': relative.as_posix(), 'source_sha256': file_digest(path),
            'artifacts': artifacts, 'dependency_parts': artifact_pins('.'.join(relative.with_suffix('').parts), search),
            'search_path': [str(p) for p in search], 'toolchain': (ROOT / 'lean-toolchain').read_text().strip(),
            'tools': {p.relative_to(ROOT).as_posix(): file_digest(p) for p in
                      (Path(__file__).resolve(), HELPER, *READER_PARTS, ROOT / 'scripts/run-lake.sh')}}


def summarize(report: dict) -> dict:
    """Group external owner modules by use while retaining all declaration evidence."""
    groups = {key: set() for key in ('public_signature', 'exposed_body', 'proof', 'private_signature', 'private_body')}
    implicit_init = set()
    unresolved = set()
    for declaration in report['declarations']:
        for part in declaration['parts']:
            for dependency in part['dependencies']:
                owner = dependency['owner']
                if owner is None:
                    unresolved.add(dependency['constant'])
                elif owner == 'Init' or owner.startswith('Init.'):
                    implicit_init.add(owner)
                elif owner != report['module']:
                    groups[part['role']].add(owner)
    return {'owners_by_role': {k: sorted(v) for k, v in groups.items()},
            'public_owner_candidates': sorted(groups['public_signature'] | groups['exposed_body']),
            'implicit_init_owners': sorted(implicit_init), 'unresolved_constants': sorted(unresolved)}


def main(argv=None) -> int:
    """Produce or reuse one JSON report bound to the selected source and artifacts."""
    parser = argparse.ArgumentParser(description=__doc__)
    selected = parser.add_mutually_exclusive_group(required=True)
    selected.add_argument('--file', type=Path, help='Lean source relative to the repository root')
    selected.add_argument('--module', help='module name, e.g. Purelib.Data.Gaussian.Multiplication')
    parser.add_argument('--output', type=Path, help='atomic JSON output; reuse matching checked output')
    parser.add_argument('--refresh', action='store_true', help='refresh dependency owner evidence even if selected inputs match')
    parser.add_argument('--namespace', action='append', default=[],
                        help='query persisted namespace registrations without executing initialization callbacks; repeat as needed')
    args = parser.parse_args(argv)
    try:
        if args.module:
            style.name(args.module, '--module')
            path = ROOT / Path(*args.module.split('.')).with_suffix('.lean')
        else:
            path = ROOT / args.file
        path = path.resolve()
        style.require(path.is_relative_to(ROOT) and path.suffix == '.lean', 'select a Lean source in this repository')
        style.require(args.output is None or args.output.suffix == '.json', '--output must name a .json file')
        module = '.'.join(path.relative_to(ROOT).with_suffix('').parts)
        runner = ROOT / 'scripts/run-lake.sh'
        paths = subprocess.run([str(runner), 'env', 'printenv', 'LEAN_PATH'], cwd=ROOT, check=True, text=True, capture_output=True).stdout.strip('\r\n')
        sysroot = subprocess.run([str(runner), 'env', 'lean', '--print-prefix'], cwd=ROOT, check=True, text=True, capture_output=True).stdout.strip()
        search = [Path(p) for p in paths.split(os.pathsep)] + [Path(sysroot) / 'lib/lean']
        state = inputs(path, search)
        for namespace in args.namespace:
            style.name(namespace, '--namespace')
        state['namespace_queries'] = args.namespace
        state['namespace_contract'] = 'persisted-only-no-initializers-v1'
        if args.output and args.output.is_file() and not args.refresh:
            cached = style.read_json(args.output)
            if (cached.get('schema') == 1 and cached.get('inputs') == state
                    and cached.get('report_sha256') == style.digest(style.encoded(cached.get('report')))):
                print(f'reused dependency evidence: {module}', file=sys.stderr)
                return 0
        command = [str(ROOT / 'scripts/run-lake.sh'), 'env', 'python3',
                   str(HELPER), 'dependencies', module, *args.namespace]
        result = subprocess.run(command, cwd=ROOT, text=True, capture_output=True)
        if result.returncode:
            raise ValueError(f'compiled dependency reader failed:\n{result.stdout}{result.stderr}')
        import json
        report = json.loads(result.stdout)
        style.require(report['module'] == module, 'reader returned a different module')
        report.update(summarize(report))
        style.require({**inputs(path, search), 'namespace_queries': args.namespace,
                       'namespace_contract': 'persisted-only-no-initializers-v1'} == state, 'selected source, artifacts or tools changed during capture; rerun')
        output = {'schema': 1, 'inputs': state, 'report': report,
                  'report_sha256': style.digest(style.encoded(report)),
                  'limitations': ['Source and selected artifacts are bound separately; this report does not certify they match.',
                                  'Selected metadata and IR dependencies are content-bound; source-to-artifact agreement still requires a build.',
                                  'Syntax, tactics, elaborator extensions and external re-export clients require source review.',
                                  'Owner candidates are direct defining modules; an existing deliberate re-export may already expose them.',
                                  'Namespace queries read persisted extension registrations only; no initialization callback executes.']}
        if args.output:
            style.atomic_write(args.output, style.encoded(output))
        else:
            print(style.encoded(output), end='')
        return 0
    except (ValueError, KeyError, OSError, subprocess.CalledProcessError) as error:
        print(f'module-style-dependencies: {error}', file=sys.stderr)
        return 1


if __name__ == '__main__':
    raise SystemExit(main())
