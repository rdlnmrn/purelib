#!/usr/bin/env python3
"""Stage redundant plain public-import demotions with checked route witnesses.

No Lean source or canonical plan is modified. Meta imports and import-all edges
are preserved and never used as witnesses. Every removed edge has a path through
plain public imports in the final proposed graph, including simultaneous edits.
"""
from __future__ import annotations

import argparse
from collections import deque
import copy
import json
import os
from pathlib import Path
import subprocess
import tempfile

from scripts.module_style import core as style

ROOT = style.ROOT


def identity(value):
    """Hash deterministic JSON describing graph inputs or immutable evidence."""
    return style.digest(style.encoded(value))


def header_imports(text):
    """Read the module header with comments and literals protected lexically."""
    code = style.mask(text, style.lex(text))
    rows = []
    for line in code.splitlines():
        line = line.strip()
        if not line or line in {'module', 'prelude'}:
            continue
        match = style.IMPORT.fullmatch(line)
        if not match:
            break
        rows.append((match['mode'], match['module']))
    return rows


def reachable(graph):
    """Compute strict descendants and reject cycles in the modeled public DAG."""
    result, active = {}, set()
    def visit(node):
        if node in result:
            return result[node]
        style.require(node not in active, f'public import cycle through {node}')
        active.add(node)
        descendants = set()
        for child in sorted(graph.get(node, ())):
            descendants.add(child)
            descendants.update(visit(child))
        active.remove(node)
        result[node] = descendants
        return descendants
    for node in sorted(graph):
        visit(node)
    return result


def path_between(graph, start, target):
    """Return a deterministic shortest retained import route, if one exists."""
    queue, visited = deque([[start]]), {start}
    while queue:
        path = queue.popleft()
        if path[-1] == target:
            return path
        for child in sorted(graph.get(path[-1], ())):
            if child not in visited:
                visited.add(child)
                queue.append(path + [child])
    return None


def reduce_graph(graph, selected):
    """Reduce selected vertices while proving all public reachability unchanged."""
    before = reachable(graph)
    reduced = {node: set(children) for node, children in graph.items()}
    removed = {}
    for node in sorted(selected):
        children = graph.get(node, set())
        redundant = {child for child in children
                     if any(child in before[other] for other in children if other != child)}
        if redundant:
            reduced[node].difference_update(redundant)
            removed[node] = sorted(redundant)
    style.require(reachable(reduced) == before, 'proposed graph changes public reachability')
    witnesses = {}
    for node, targets in removed.items():
        witnesses[node] = {}
        for target in targets:
            route = path_between(reduced, node, target)
            style.require(route is not None and len(route) >= 3,
                          f'no retained indirect public route: {node} -> {target}')
            witnesses[node][target] = route
    return reduced, witnesses


def immutable_json(path, value):
    """Publish complete evidence without replacing an existing or competing writer."""
    text = style.encoded(value)
    path.parent.mkdir(parents=True, exist_ok=True)
    pending = None
    try:
        with tempfile.NamedTemporaryFile('w', encoding='utf-8', dir=path.parent,
                                         prefix=path.name + '.', delete=False) as handle:
            pending = Path(handle.name)
            handle.write(text)
            handle.flush()
            os.fsync(handle.fileno())
        pending.chmod(0o644)
        try:
            os.link(pending, path)
        except FileExistsError:
            style.require(path.read_bytes() == text.encode('utf-8'),
                          f'conflicting immutable evidence: {path}')
    finally:
        if pending is not None:
            pending.unlink(missing_ok=True)


def checked_json(path, inputs):
    """Parse and bind the same input bytes, including duplicate-key rejection."""
    text = path.read_text()
    def unique(pairs):
        result = {}
        for key, value in pairs:
            style.require(key not in result, f'duplicate JSON key: {key}')
            result[key] = value
        return result
    value = json.loads(text, object_pairs_hook=unique)
    inputs[str(path)] = style.digest(text)
    return value


def reviewed_state(plan, current, history):
    """Recover the original without rebasing an applied or pending style plan."""
    if style.digest(current) == plan['prepared']['result_sha256']:
        original = style.recover_original(plan, current)
        return original, current, plan
    previous = history / plan['path'][:-5] / (style.digest(current) + '.json')
    style.require(previous.is_file(), f'{plan["path"]}: full plan is not applied and no checked prior exists')
    prior = style.read_json(previous)
    style.require(prior['path'] == plan['path'] and prior['source_sha256'] == plan['source_sha256'],
                  'prior describes a different original source')
    original = style.recover_original(prior, current)
    proposed = style.apply_plan(plan, original)
    return original, proposed, prior



def publish_checked(run, evidence, staged):
    """Publish an application manifest only while all reviewed inputs still match."""
    for file, record in evidence['sources'].items():
        style.require(style.digest(Path(file).read_text()) == record['source_sha256'],
                      f'source changed during preparation: {file}')
    style.require(style.digest(Path(__file__).read_text()) == evidence['tool_sha256'],
                  'reducer changed during preparation')
    for file, digest in evidence['inputs'].items():
        style.require(style.digest(Path(file).read_text()) == digest,
                      f'review input changed during preparation: {file}')
    immutable_json(run / 'graph.json', evidence)
    immutable_json(run / 'manifest.json', dict(schema=1, plans=staged, graph=str(run / 'graph.json')))


def main(argv=None):
    """Load reviewed plans, prove a reduction, and stage plans plus immutable priors."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--manifest', type=Path, default=ROOT / 'docs/module-style/manifest.json')
    parser.add_argument('--plans', type=Path, default=ROOT / 'docs/module-style/plans')
    parser.add_argument('--plan', type=Path, action='append', help='limit demotions to these canonical plans')
    parser.add_argument('--exclude', action='append', default=[], help='source path to leave unchanged')
    parser.add_argument('--output', type=Path, default=ROOT / '.lake/module-style-public-imports')
    args = parser.parse_args(argv)
    tool_sha256 = style.digest(Path(__file__).read_text())
    inputs = {str(file): style.digest(file.read_text()) for file in
              (Path(style.__file__), ROOT / 'lean-toolchain', ROOT / 'scripts/run-lake.sh')}
    manifest = checked_json(args.manifest, inputs)
    authored = {row['path'] for row in manifest['files'] if row['classification'] == 'authored'}
    style.require(set(args.exclude) <= authored, 'excluded paths must be authored manifest sources')
    plan_files = args.plan or [args.plans / Path(p).with_suffix('.json') for p in sorted(authored) if p not in args.exclude]
    history = args.output / 'priors'
    states, overrides = {}, {}
    for file in plan_files:
        plan = checked_json(file, inputs)
        path = plan['path']
        if path in args.exclude:
            continue
        style.require(path in authored, f'not an authored manifest module: {path}')
        style.require(path not in states, f'duplicate plan for {path}')
        current = style.source_path(plan).read_text()
        original, proposed, prior = reviewed_state(plan, current, history)
        states[path] = (file, plan, current, original, proposed, prior)
        overrides[path] = proposed
    roots = [ROOT] + sorted(p for p in (ROOT / '.lake/packages').iterdir() if p.is_dir())
    sysroot = Path(subprocess.check_output([ROOT / 'scripts/run-lake.sh', 'env', 'lean', '--print-prefix'], text=True).strip())
    roots.append(sysroot / 'src/lean')
    graph, sources, unresolved = {}, {}, []
    pending = [row['module'] for row in manifest['files']]
    while pending:
        module = pending.pop()
        if module in graph:
            continue
        relative = Path(module.replace('.', '/') + '.lean')
        file = next((root / relative for root in roots if (root / relative).is_file()), None)
        if file is None:
            graph[module] = set()
            unresolved.append(module)
            continue
        actual = file.read_text()
        if file == ROOT / relative and relative.as_posix() in states:
            style.require(actual == states[relative.as_posix()][2],
                          f'source changed during preparation: {file}')
        text = overrides.get(relative.as_posix(), actual) if file.is_relative_to(ROOT) else actual
        sources[str(file)] = {'source_sha256': style.digest(actual), 'proposed_sha256': style.digest(text)}
        graph[module] = {owner for mode, owner in header_imports(text) if mode == 'public import'}
        pending.extend(graph[module])
    selected = {path[:-5].replace('/', '.') for path in states}
    reduced, witnesses = reduce_graph(graph, selected)
    evidence = dict(schema=1, tool_sha256=tool_sha256,
                    toolchain=(ROOT / 'lean-toolchain').read_text().strip(), inputs=inputs,
                    sources=sources, unresolved_leaves=sorted(unresolved), excluded=sorted(args.exclude),
                    before={n: sorted(e) for n, e in sorted(graph.items())},
                    after={n: sorted(e) for n, e in sorted(reduced.items())}, witnesses=witnesses)
    run = args.output / 'runs' / identity(evidence)
    staged = []
    for path, (file, plan, current, original, proposed, prior) in sorted(states.items()):
        module = path[:-5].replace('/', '.')
        if module not in witnesses:
            continue
        changed = copy.deepcopy(plan)
        for row in changed['imports']:
            if row['module'] in witnesses[module]:
                style.require(row['mode'] == 'public import', 'refuse phase or import-all change')
                row['mode'] = 'import'
                row['reason'] = ('Direct dependency; its public availability is retained through ' +
                                 ' -> '.join(witnesses[module][row['module']][1:]) + '.')
        changed, result = style.prepare(changed, original)
        before_rows, after_rows = header_imports(proposed), header_imports(result)
        expected = [('import' if mode == 'public import' and owner in witnesses[module] else mode, owner)
                    for mode, owner in before_rows]
        style.require(after_rows == expected, f'unexpected header change for {path}')
        expected_text = proposed
        for entry in reversed(style.inventory(proposed)['imports']):
            if entry['mode'] == 'public import' and entry['module'] in witnesses[module]:
                start = entry['start']
                style.require(expected_text[start:start + 7] == 'public ', 'unexpected import spelling')
                expected_text = expected_text[:start] + expected_text[start + 7:]
        style.require(result == expected_text, f'change outside import visibility for {path}')
        style.require(style.apply_plan(changed, result) == result, f'non-idempotent plan for {path}')
        prior_file = history / path[:-5] / (style.digest(current) + '.json')
        immutable_json(prior_file, prior)
        target = run / 'plans' / Path(path).with_suffix('.json')
        immutable_json(target, changed)
        staged.append(dict(path=path, canonical_plan=str(file), plan=str(target), prior_plan=str(prior_file),
                           source_sha256=style.digest(current), result_sha256=style.digest(result)))
    # Staged plan bytes alone are not authorization to apply a partial run.
    publish_checked(run, evidence, staged)
    print(style.encoded(dict(modules=len(staged), demotions=sum(len(v) for v in witnesses.values()),
                            manifest=str(run / 'manifest.json'))), end='')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
