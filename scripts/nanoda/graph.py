#!/usr/bin/env python3
"""Validate export closures against an inventory and report shared declarations.

Reads streams incrementally; only declaration names, not expression records, are
retained. Estimates in the inventory never substitute for exact set equality.
"""
import argparse
from collections import Counter
import json
from pathlib import Path


def inventory(path):
    with path.open() as f:
        header = json.loads(next(f))
        if header['schema'] != 1:
            raise ValueError('unsupported graph schema')
        nodes = {}
        for line in f:
            node = json.loads(line)
            if node['name'] in nodes:
                raise ValueError(f"duplicate graph node: {node['name']}")
            nodes[node['name']] = node
    roots = [r['name'] for r in header['roots']]
    if len(set(roots)) != len(roots):
        raise ValueError('duplicate roots')
    for name in roots:
        if name not in nodes:
            raise ValueError(f'missing root: {name}')
    for node in nodes.values():
        for name in node['dependencies'] + node['atomic']:
            if name not in nodes:
                raise ValueError(f'unresolved dependency: {name}')
    return header, nodes


def closure(nodes, roots):
    seen = set(roots)
    pending = list(roots)
    while pending:
        for dep in nodes[pending.pop()]['dependencies']:
            if dep not in seen:
                seen.add(dep)
                pending.append(dep)
    return seen


def exported(path):
    names = {0: ''}
    declarations = set()
    expressions = 0
    with path.open() as f:
        for line in f:
            item = json.loads(line)
            if 'in' in item:
                component = item.get('str', item.get('num'))
                prefix = names[component['pre']]
                suffix = str(component.get('str', component.get('i')))
                names[item['in']] = prefix + ('.' if prefix else '') + suffix
            elif 'ie' in item:
                expressions += 1
            elif 'inductive' in item:
                for kind in ('types', 'ctors', 'recs'):
                    for decl in item['inductive'][kind]:
                        declarations.add(names[decl['name']])
            else:
                for kind in ('axiom', 'def', 'thm', 'opaque', 'quot'):
                    if kind in item:
                        declarations.add(names[item[kind]['name']])
    return declarations, expressions


def components(nodes):
    """Iterative Kosaraju; no recursion-depth tuning for large graphs."""
    seen, order = set(), []
    reverse = {name: [] for name in nodes}
    for name, node in nodes.items():
        for dep in node['dependencies']:
            reverse[dep].append(name)
        if name in seen:
            continue
        seen.add(name)
        stack = [(name, iter(node['dependencies']))]
        while stack:
            current, edges = stack[-1]
            dep = next(edges, None)
            if dep is None:
                order.append(current)
                stack.pop()
            elif dep not in seen:
                seen.add(dep)
                stack.append((dep, iter(nodes[dep]['dependencies'])))
    seen, groups = set(), []
    for name in reversed(order):
        if name in seen:
            continue
        pending, group = [name], []
        seen.add(name)
        while pending:
            current = pending.pop()
            group.append(current)
            for parent in reverse[current]:
                if parent not in seen:
                    seen.add(parent)
                    pending.append(parent)
        groups.append(sorted(group))
    return groups


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('graph', type=Path)
    parser.add_argument('--stream', type=Path, help='complete native stream to compare')
    parser.add_argument('--dag', type=Path, help='write the condensed dependency DAG')
    parser.add_argument('--costs', action='store_true', help='estimate each selected root closure; use on benchmark manifests')
    args = parser.parse_args()
    header, nodes = inventory(args.graph)
    roots = [r['name'] for r in header['roots']]
    groups = components(nodes)
    owner = {name: min(group) for group in groups for name in group}
    for name, node in nodes.items():
        if any(owner[member] != owner[name] for member in node['atomic']):
            raise ValueError(f'exporter atomic group was split: {name}')
    if args.dag:
        dag = {'schema': 1, 'roots': header['roots'], 'groups': {}}
        for group in groups:
            identity = min(group)
            dependencies = sorted({owner[dep] for name in group
                                   for dep in nodes[name]['dependencies']} - {identity})
            dag['groups'][identity] = {
                'members': group, 'dependencies': dependencies,
                'expression_estimate': sum(nodes[n]['expression_estimate'] for n in group)}
        pending = args.dag.with_suffix(args.dag.suffix + '.partial')
        pending.write_text(json.dumps(dag, sort_keys=True) + '\n')
        pending.replace(args.dag)
    report = {'roots': len(roots), 'declarations': len(nodes),
              'components': len(groups), 'largest_component': max(map(len, groups), default=0)}
    if args.costs:
        fan_in = Counter(dep for node in nodes.values() for dep in node['dependencies'])
        report['high_direct_fan_in'] = fan_in.most_common(10)
        report['large_declaration_estimates'] = sorted(
            ((name, node['expression_estimate']) for name, node in nodes.items()),
            key=lambda pair: (-pair[1], pair[0]))[:10]
        # Intentionally opt-in: never retain all transitive closures or do this
        # quadratic work implicitly on the full repository graph.
        root_costs = []
        for root in roots:
            reached = closure(nodes, [root])
            root_costs.append({'name': root, 'declarations': len(reached),
                              'expression_estimate': sum(nodes[n]['expression_estimate']
                                                         for n in reached)})
        report['root_closures'] = root_costs
    if args.stream:
        actual = exported(args.stream)
        if actual != set(nodes):
            raise ValueError('stream declaration coverage differs from the complete graph')
        report['stream_declarations'] = len(actual)
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
