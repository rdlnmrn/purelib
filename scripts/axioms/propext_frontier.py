#!/usr/bin/env python3
"""Order authoritative dirty dependencies from providers to consumers.

The retained export graph supplies atomic components and an independent
reachability cross-check. Audit records supply exact roots, including canonical
auxiliaries absent from the exporter. This produces a schedule, never a pass.
"""
import argparse
from collections import defaultdict, deque
import hashlib
import json
from pathlib import Path


from scripts.nanoda import graph

def graph_tools():
    return graph


def fingerprint(path):
    with path.open('rb') as handle:
        return hashlib.file_digest(handle, 'sha256').hexdigest()


def audit_records(paths):
    roots, dirty = {}, {}
    for path in paths:
        with path.open() as handle:
            for line in handle:
                # A worker with no selected roots emits one trailing newline.
                if not line.strip():
                    continue
                row = json.loads(line)
                name = row['name']
                if row['kind'] == 'root':
                    # Standalone modules can each declare the same public basename.
                    # Older receipts lack scanned_module and record their owner.
                    key = (row.get('scanned_module', row['owner']), name)
                    previous = roots.get(key)
                    if previous:
                        if previous['axioms'] != row['axioms']:
                            raise ValueError(f'inconsistent audit roots: {key}')
                        row['canonical'] |= previous['canonical']
                    roots[key] = row
                elif row['kind'] == 'dirty':
                    previous = dirty.get(name)
                    if previous:
                        # Lazy equation proofs can retain different generated
                        # helpers in different worker import environments.
                        # Preserve every actual route and its exact variant.
                        variant = {'owner': row['owner'], 'dependencies': row['dependencies'],
                                   'external': row['external']}
                        variants = previous.get('variants', [])
                        if variant not in variants:
                            variants.append(variant)
                        row['variants'] = variants
                        row['dependencies'] = sorted(set(previous['dependencies']) | set(row['dependencies']))
                        row['external'] = sorted(set(previous['external']) | set(row['external']))
                    else:
                        row['variants'] = [{'owner': row['owner'], 'dependencies': row['dependencies'],
                                            'external': row['external']}]
                    row['owner_candidates'] = sorted(set((previous or {}).get('owner_candidates', [])) | {row['owner']})
                    dirty[name] = row
                else:
                    raise ValueError(f'unknown audit record kind: {row["kind"]}')
    for name, row in dirty.items():
        for dep in set(row['dependencies']) - set(row['external']):
            if dep not in dirty:
                raise ValueError(f'missing dirty project prerequisite: {name}: {dep}')
    for (_, name), row in roots.items():
        if row['axioms'] and name not in dirty:
            raise ValueError(f'missing dirty audit root: {name}')
    return roots, dirty


def schedule(dirty, atomic):
    """Kahn layers on the project DAG, preserving exporter atomic groups."""
    tools = graph_tools()
    nodes = {}
    for name, row in dirty.items():
        deps = (set(row['dependencies']) - set(row['external'])) | (set(atomic.get(name, [])) & dirty.keys())
        nodes[name] = {'dependencies': sorted(deps)}
    groups = tools.components(nodes)
    owner = {name: min(group) for group in groups for name in group}
    edges, reverse = {}, defaultdict(set)
    for group in groups:
        identity = min(group)
        edges[identity] = {owner[d] for n in group for d in nodes[n]['dependencies']} - {identity}
        for dep in edges[identity]:
            reverse[dep].add(identity)
    remaining = {name: len(deps) for name, deps in edges.items()}
    ready = deque(sorted(name for name, count in remaining.items() if not count))
    layers, ordered = {}, []
    while ready:
        name = ready.popleft()
        layers[name] = max((layers[d] + 1 for d in edges[name]), default=0)
        ordered.append(name)
        for consumer in sorted(reverse[name]):
            remaining[consumer] -= 1
            if not remaining[consumer]:
                ready.append(consumer)
    if len(ordered) != len(groups):
        raise ValueError('condensed project graph is cyclic')
    members = {min(group): group for group in groups}
    return [dict(name=name, layer=layers[name], members=members[name],
                 providers=sorted(edges[name]), consumers=sorted(reverse[name]),
                 external=sorted({d for n in members[name] for d in dirty[n]['external']}),
                 modules=sorted({m for n in members[name] for m in dirty[n].get('owner_candidates', [dirty[n]['owner']])}),
                 status='ready' if not edges[name] else 'blocked')
            for name in sorted(ordered, key=lambda name: (layers[name], name))]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('graph', type=Path)
    parser.add_argument('reports', type=Path)
    parser.add_argument('--output', required=True, type=Path)
    args = parser.parse_args()
    paths = sorted(args.reports.glob('closures.*.jsonl'))
    if not paths:
        raise ValueError('no authoritative closure reports')
    roots, dirty = audit_records(paths)
    tools = graph_tools()
    header, nodes = tools.inventory(args.graph)
    reverse = defaultdict(list)
    for name, row in nodes.items():
        for dep in row['dependencies']:
            reverse[dep].append(name)
    reached, pending = {'propext'}, ['propext']
    while pending:
        for consumer in reverse[pending.pop()]:
            if consumer not in reached:
                reached.add(consumer)
                pending.append(consumer)
    mismatch = [name for (_, name), row in roots.items() if name in nodes and
                ('propext' in row['axioms'] and name not in reached)]
    if mismatch:
        raise ValueError(f'graph/audit contamination mismatch: {mismatch[:10]}')
    components = schedule(dirty, {n: row['atomic'] for n, row in nodes.items()})
    canonical = {name for (_, name), row in roots.items() if row['canonical'] and row['axioms']}
    pending = list(canonical)
    while pending:
        for dep in dirty[pending.pop()]['dependencies']:
            if dep in dirty and dep not in canonical:
                canonical.add(dep)
                pending.append(dep)
    for row in components:
        row['canonical_prerequisite'] = bool(set(row['members']) & canonical)
    result = {'schema': 1, 'evidence': {str(p): fingerprint(p) for p in paths + [args.graph]},
              'roots': len(roots), 'dirty_roots': sum(bool(r['axioms']) for r in roots.values()),
              'canonical_dirty_roots': sum(r['canonical'] and bool(r['axioms']) for r in roots.values()),
              'export_roots': len(header['roots']),
              'root_identity': 'scanned_module,name',
              'audit_roots_missing_from_export_graph': sorted({name for (_, name) in roots if name not in nodes}),
              'audit_root_records_missing_from_export_graph': sorted(
                  [dict(scanned_module=module, name=name) for module, name in roots if name not in nodes],
                  key=lambda row: (row['scanned_module'], row['name'])),
              'graph_dirty_audit_clean_roots': sorted(name for (_, name), row in roots.items()
                   if name in reached and not row['axioms']),
              'dirty_nodes': len(dirty), 'components': components}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    pending_output = args.output.with_suffix('.pending')
    pending_output.write_text(json.dumps(result, sort_keys=True) + '\n')
    pending_output.replace(args.output)
    print(json.dumps({k: v for k, v in result.items() if k not in ('components', 'evidence', 'audit_roots_missing_from_export_graph', 'audit_root_records_missing_from_export_graph', 'graph_dirty_audit_clean_roots')}, indent=2))
    print('ready canonical providers:')
    for row in components:
        if row['status'] == 'ready' and row['canonical_prerequisite']:
            print(row['name'], row['external'])


if __name__ == '__main__':
    main()
