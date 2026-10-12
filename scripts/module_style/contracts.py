#!/usr/bin/env python3
"""Capture and compare compiled declarations for reviewed module-style plans.

This wrapper never builds. Capture before applying plans, then check after
building their results. Every declaration difference is reported, including
private auxiliaries, expression hashes, and public exposure. Per-module atomic
snapshots and content-addressed captures make interrupted runs reusable.
"""
from __future__ import annotations

import argparse
import copy
from concurrent.futures import Future, ThreadPoolExecutor, as_completed
import json
from pathlib import Path
import re
import sys
from threading import Lock

from scripts.module_style import core as style

from scripts.verification import contracts
ROOT = contracts.ROOT


def name_components(value):
    """Parse only the Name repr forms emitted by the pinned Lean helper."""
    position = 0
    def skip():
        nonlocal position
        while position < len(value) and value[position].isspace():
            position += 1
    def parse():
        nonlocal position
        skip()
        if value[position:position + 1] == '(':
            position += 1
            result = parse()
            skip()
            style.require(value[position:position + 1] == ')', 'malformed Name repr parenthesis')
            position += 1
            return result
        if value.startswith('Lean.Name.anonymous', position):
            position += len('Lean.Name.anonymous')
            return []
        for constructor, tag in [('Lean.Name.mkStr', 'str'), ('Lean.Name.mkNum', 'num')]:
            if not value.startswith(constructor, position):
                continue
            position += len(constructor)
            parent = parse()
            skip()
            if tag == 'str':
                suffix, consumed = json.JSONDecoder().raw_decode(value[position:])
                style.require(isinstance(suffix, str), 'expected Name string component')
                position += consumed
            else:
                number = re.match(r'[0-9]+', value[position:])
                style.require(number is not None, 'expected Name numeric component')
                suffix = int(number[0])
                position += len(number[0])
            return parent + [(tag, suffix)]
        style.require(value[position:position + 1] == '`', 'unsupported Name repr')
        position += 1
        components = []
        while True:
            if value[position:position + 1] == '«':
                end = value.find('»', position + 1)
                style.require(end >= 0, 'unterminated escaped Name component')
                component = value[position + 1:end]
                style.require('«' not in component, 'unsupported escaped Name component')
                position = end + 1
            else:
                part = re.match(r"_@(?=\.|\s|\)|$)|[^\W\d][\w'!?₀-₉]*", value[position:], re.UNICODE)
                style.require(part is not None, 'unsupported literal Name component')
                component = part[0]
                position += len(component)
            components.append(('str', component))
            if value[position:position + 1] != '.':
                return components
            position += 1
    result = parse()
    skip()
    style.require(position == len(value), 'trailing material in Name repr')
    return result


def erased_macro_name(value):
    """Mirror pinned Init/Prelude Name.hasMacroScopes/eraseMacroScopes.

    Reject names without actual macro scopes and malformed scope encodings.
    Only binder-name slots call this function; constant identities never do.
    """
    components = name_components(value)
    tail = len(components) - 1
    while tail >= 0 and components[tail][0] == 'num':
        tail -= 1
    style.require(tail >= 0 and components[tail] == ('str', '_hyg'),
                  'binder name has no actual macro scopes')
    for index in range(tail - 1, -1, -1):
        if components[index] == ('str', '_@'):
            style.require(index > 0, 'macro binder has no retained base name')
            return components[:index]
    raise ValueError('macro binder has no scope delimiter')


def binder_changes(before, after, field):
    """Compare exact DAGs, admitting changes only to scoped binder names."""
    style.require(isinstance(before, dict) and isinstance(after, dict), 'expected expression DAGs')
    style.require(set(before) == set(after) == {'nodes', 'root'}, 'unexpected expression DAG fields')
    style.require(before['root'] == after['root'] and len(before['nodes']) == len(after['nodes']),
                  'expression DAG structure changed')
    changes = []
    for index, (old, new) in enumerate(zip(before['nodes'], after['nodes'])):
        if old == new:
            continue
        style.require(isinstance(old, list) and isinstance(new, list) and
                      len(old) == len(new) and len(old) >= 2 and
                      old[0] in {'lam', 'forallE', 'letE'} and
                      old[:1] == new[:1] and old[2:] == new[2:],
                      f'non-binder expression change at {field} node {index}')
        style.require(erased_macro_name(old[1]) == erased_macro_name(new[1]),
                      f'binder base name changed at {field} node {index}')
        changes.append({'field': field, 'node': index, 'before': old[1], 'after': new[1]})
    return changes


def metadata_position_skeleton(value):
    """Erase parsed source positions in recursive-call or pattern syntax metadata.

    Lean.Elab.RecAppSyntax and `_patWithRef` retain positions for diagnostics and to keep
    distinct call sites apart during hashconsing. Strings, syntax, names and
    every other metadata value remain byte-for-byte intact. In particular a
    number inside a quoted string is never interpreted as a position.
    """
    style.require(isinstance(value, str), 'expected metadata repr')
    tokens = list(re.finditer(r'"(?:[^"\\]|\\.)*"|[A-Za-z_][\w.]*|[0-9]+|:=|[^\s]', value))
    words = [token[0] for token in tokens]
    style.require(words[:6] == ['{', 'entries', ':=', '[', '(', '`'] and
                  words[6:7] in [['_recApp'], ['_patWithRef']] and
                  words[7:9] == [',', 'Lean.DataValue.ofSyntax'],
                  'source-position evidence requires recursive-call or pattern syntax metadata')
    pattern = words[6] == '_patWithRef'
    positions = set()
    for i, word in enumerate(words):
        if word == 'Lean.SourceInfo.original' and not pattern:
            part = words[i:i + 16]
            style.require(len(part) == 16 and part[1].startswith('"') and
                          part[2:6] == ['.', 'toRawSubstring', '{', 'byteIdx'] and
                          part[6] == ':=' and part[7].isdigit() and part[8] == '}' and
                          part[9].startswith('"') and
                          part[10:14] == ['.', 'toRawSubstring', '{', 'byteIdx'] and
                          part[14] == ':=' and part[15].isdigit() and words[i + 16:i + 17] == ['}'],
                          'unsupported original source-info repr')
            positions.update([i + 7, i + 15])
        if word == 'Lean.SourceInfo.synthetic' and pattern:
            part = words[i:i + 12]
            style.require(len(part) == 12 and part[1:4] == ['{', 'byteIdx', ':='] and
                          part[4].isdigit() and part[5:9] == ['}', '{', 'byteIdx', ':='] and
                          part[9].isdigit() and part[10] == '}' and part[11] in {'true', 'false'},
                          'unsupported pattern synthetic source-info repr')
            positions.update([i + 4, i + 9])
        if not pattern and word == '_recAppPos' and words[max(0, i - 2):i] == ['(', '`']:
            style.require(words[i + 1:i + 3] == [',', 'Lean.DataValue.ofNat'] and
                          words[i + 3:i + 4] and words[i + 3].isdigit() and
                          words[i + 4:i + 5] == [')'], 'unsupported recursive-call position repr')
            positions.add(i + 3)
    style.require(positions, 'no recognized metadata source positions')
    result = value
    for i in sorted(positions, reverse=True):
        result = result[:tokens[i].start()] + '<source-position>' + result[tokens[i].end():]
    return result


def expression_changes(before, after, field):
    """Partition exact DAG differences into scoped names and source positions."""
    style.require(isinstance(before, dict) and isinstance(after, dict) and
                  set(before) == set(after) == {'nodes', 'root'} and
                  before['root'] == after['root'] and len(before['nodes']) == len(after['nodes']),
                  'expression DAG structure changed')
    old_binders, new_binders = copy.deepcopy(before), copy.deepcopy(after)
    positions = []
    for index, (old, new) in enumerate(zip(before['nodes'], after['nodes'])):
        if old == new or not (old[0] == new[0] == 'mdata'):
            continue
        style.require(len(old) == len(new) == 3 and old[2] == new[2] and
                      metadata_position_skeleton(old[1]) == metadata_position_skeleton(new[1]),
                      f'non-position metadata change at {field} node {index}')
        positions.append({'field': field, 'node': index, 'before': old[1], 'after': new[1]})
        new_binders['nodes'][index] = copy.deepcopy(old)
    return binder_changes(old_binders, new_binders, field), positions


def raw_declarations(path, module):
    """Read complete raw records without silently accepting duplicate names."""
    declarations = {}
    module_system = None
    expected_count = None
    for line in path.read_text().splitlines():
        row = json.loads(line)
        metadata = 'declaration_count' in row
        fields = {'module', 'module_system', 'declaration_count' if metadata else 'declaration'}
        style.keys(row, fields, fields, 'raw record')
        style.require(row['module'] == module, 'raw record belongs to a different module')
        style.require(type(row['module_system']) is bool, 'invalid raw module system')
        if module_system is not None:
            style.require(module_system == row['module_system'], 'inconsistent raw module system')
        module_system = row['module_system']
        if metadata:
            count = row['declaration_count']
            style.require(expected_count is None and not declarations and
                          type(count) is int and count >= 0, 'invalid or duplicate raw module metadata')
            expected_count = count
            continue
        declaration = row['declaration']
        name = declaration['name']
        style.require(name not in declarations, 'duplicate raw declaration')
        declarations[name] = declaration
    if expected_count is not None:
        style.require(len(declarations) == expected_count, 'incomplete raw declaration set')
    style.require(module_system is not None, 'missing raw module metadata')
    return declarations, module_system


def hashed_record(record):
    """Use the authoritative schema-2 hash encoding for every raw field."""
    result = dict(record)
    result.pop('name')
    for field in ('type', 'body', 'levels', 'extra'):
        result[field + '_sha256'] = contracts.contract_digest(result.pop(field), 2)
    return result


def make_hygiene_receipt(module, before, after, original_path, current_path):
    """Bind recovered raw records to both captures before retaining evidence."""
    original, original_system = raw_declarations(original_path, module)
    current, current_system = raw_declarations(current_path, module)
    for raw, system, capture in [(original, original_system, before), (current, current_system, after)]:
        style.require(capture['schema'] == 2, 'hygiene receipts require schema-2 captures')
        style.require(system == capture['module_system'][module], 'raw module system differs from capture')
        style.require({name: hashed_record(record) for name, record in raw.items()} ==
                      capture['declarations'][module], 'raw declaration records do not match captured hashes')
    style.require(set(original) == set(current) and original_system == current_system,
                  'declaration set or module system changed')
    entries = []
    for name in sorted(original):
        old, new = original[name], current[name]
        if old == new:
            continue
        style.require({k: v for k, v in old.items() if k not in {'type', 'body'}} ==
                      {k: v for k, v in new.items() if k not in {'type', 'body'}},
                      f'declaration metadata changed: {name}')
        changes, positions = [], []
        for field in ('type', 'body'):
            if old[field] != new[field]:
                binders, locations = expression_changes(old[field], new[field], field)
                changes.extend(binders)
                positions.extend(locations)
        entries.append({'original': old, 'binder_names': changes, 'metadata_positions': positions})
    style.require(entries, 'no hygiene differences to record')
    receipt = {'schema': 2, 'module': module, 'lean_toolchain': before['lean_toolchain'], 'entries': entries}
    validate_hygiene_receipt(receipt, module, before, after)
    return receipt


def validate_hygiene_receipt(receipt, module, before, after):
    """Reconstruct current records; verify exact hashes before accepting edits."""
    style.keys(receipt, {'schema', 'module', 'lean_toolchain', 'entries'},
               {'schema', 'module', 'lean_toolchain', 'entries'}, 'hygiene receipt')
    style.require(receipt['schema'] in {1, 2} and receipt['module'] == module, 'invalid hygiene receipt identity')
    style.require(before['schema'] == after['schema'] == 2, 'hygiene receipts require schema-2 captures')
    style.require(receipt['lean_toolchain'] == before['lean_toolchain'] == after['lean_toolchain'],
                  'hygiene receipt toolchain mismatch')
    style.require(before['module_system'] == after['module_system'], 'module system changed')
    accepted, count, names = set(), 0, set()
    for entry in receipt['entries']:
        fields = {'original', 'binder_names'} | ({'metadata_positions'} if receipt['schema'] == 2 else set())
        style.keys(entry, fields, fields, 'hygiene entry')
        original = entry['original']
        name = original['name']
        style.require(name not in names, 'duplicate hygiene declaration')
        names.add(name)
        style.require(hashed_record(original) == before['declarations'][module].get(name),
                      f'original raw record does not match baseline: {name}')
        current = copy.deepcopy(original)
        seen = set()
        style.require(bool(entry['binder_names'] or entry.get('metadata_positions')), 'empty hygiene entry')
        for change in entry['binder_names']:
            style.keys(change, {'field', 'node', 'before', 'after'},
                       {'field', 'node', 'before', 'after'}, 'binder-name change')
            field, index = change['field'], change['node']
            style.require(field in {'type', 'body'} and type(index) is int and index >= 0,
                          'invalid binder-name location')
            style.require((field, index) not in seen, 'duplicate binder-name location')
            seen.add((field, index))
            expression = current[field]
            style.require(isinstance(expression, dict) and index < len(expression['nodes']),
                          'binder-name location outside expression')
            node = expression['nodes'][index]
            style.require(node[0] in {'lam', 'forallE', 'letE'} and node[1] == change['before'],
                          'binder-name evidence does not match original node')
            style.require(change['before'] != change['after'] and
                          erased_macro_name(change['before']) == erased_macro_name(change['after']),
                          'binder base name changed')
            node[1] = change['after']
            accepted.add((module, name, field + '_sha256'))
            count += 1
        for change in entry.get('metadata_positions', []):
            style.keys(change, {'field', 'node', 'before', 'after'},
                       {'field', 'node', 'before', 'after'}, 'metadata-position change')
            field, index = change['field'], change['node']
            style.require(field in {'type', 'body'} and type(index) is int and index >= 0,
                          'invalid metadata-position location')
            style.require((field, index) not in seen, 'duplicate metadata-position location')
            seen.add((field, index))
            expression = current[field]
            style.require(isinstance(expression, dict) and index < len(expression['nodes']),
                          'metadata-position location outside expression')
            node = expression['nodes'][index]
            style.require(len(node) == 3 and node[0] == 'mdata' and node[1] == change['before'],
                          'metadata-position evidence does not match original node')
            style.require(change['before'] != change['after'] and
                          metadata_position_skeleton(change['before']) ==
                          metadata_position_skeleton(change['after']), 'non-position metadata change')
            node[1] = change['after']
            accepted.add((module, name, field + '_sha256'))
            count += 1
        style.require(hashed_record(current) == after['declarations'][module].get(name),
                      f'reconstructed raw record does not match current capture: {name}')
    style.require(bool(accepted), 'empty hygiene receipt')
    return accepted, count


def plain_name_components(value):
    """Read the unescaped declaration names used by a checked rename route."""
    parts = value.split('.')
    style.require(all(re.fullmatch(r"[A-Za-z_][\w'!?₀-₉]*|[0-9]+", part) for part in parts),
                  'unsupported declaration name spelling in namespace evidence')
    return [('num', int(part)) if part.isdigit() else ('str', part) for part in parts]


def route_name_components(parts, module, old_prefix, new_prefix):
    """Route a namespace prefix, including its compiler-private module wrapper."""
    old = plain_name_components(old_prefix)
    new = plain_name_components(new_prefix)
    start = 0
    private = [('str', '_private')] + plain_name_components(module)
    if parts[:len(private)] == private and len(parts) > len(private) and parts[len(private)][0] == 'num':
        start = len(private) + 1
    if parts[start:start + len(old)] == old:
        return parts[:start] + new + parts[start + len(old):]
    return parts


def namespace_record_changes(original, current, module, old_prefix, new_prefix):
    """Verify only exact Name routes and previously checked expression hygiene.

    All DAG edges, node kinds, universe levels, definition metadata, privacy and
    public exposure are exact. `internal` is recomputed by pinned Name.isInternal
    (a string component starts with `_`), not treated as visibility metadata.
    """
    old_name = plain_name_components(original['name'])
    new_name = plain_name_components(current['name'])
    style.require(route_name_components(old_name, module, old_prefix, new_prefix) == new_name,
                  f'outside namespace route: {original["name"]}')
    routed = copy.deepcopy(original)
    routed['name'] = current['name']
    for value, parts in [(original, old_name), (current, new_name)]:
        style.require(value['internal'] == any(tag == 'str' and part.startswith('_') for tag, part in parts),
                      f'incorrect Name.isInternal classification: {value["name"]}')
    routed['internal'] = current['internal']
    edits = []
    if old_name != new_name:
        edits.append({'field': 'name', 'before': original['name'], 'after': current['name']})
    if original['internal'] != current['internal']:
        edits.append({'field': 'internal', 'before': original['internal'], 'after': current['internal']})
    for field in ('type', 'body'):
        old, new = routed[field], current[field]
        if old == new:
            continue
        style.require(isinstance(old, dict) and isinstance(new, dict) and
                      set(old) == set(new) == {'nodes', 'root'} and old['root'] == new['root'] and
                      len(old['nodes']) == len(new['nodes']), 'expression DAG structure changed')
        for index, (a, b) in enumerate(zip(old['nodes'], new['nodes'])):
            if a == b:
                continue
            if (a[0] in {'const', 'proj', 'lam', 'forallE', 'letE', 'fvar', 'mvar'} and
                    a[0] == b[0] and len(a) == len(b) and a[2:] == b[2:]):
                before_name, after_name = name_components(a[1]), name_components(b[1])
                if (before_name != after_name and
                        route_name_components(before_name, module, old_prefix, new_prefix) == after_name):
                    edits.append({'field': field, 'node': index, 'name_before': a[1], 'name_after': b[1]})
                    a[1] = b[1]
        if old != new:
            binders, positions = expression_changes(old, new, field)
            edits.extend({'hygiene': 'binder', **change} for change in binders)
            edits.extend({'hygiene': 'source-position', **change} for change in positions)
            # expression_changes checked every node before this exact substitution.
            routed[field] = copy.deepcopy(new)
    style.require(routed == current, f'non-rename declaration change: {original["name"]}')
    return edits


def validate_namespace_receipt(receipt, module, before, after):
    """Bind all raw records to captures and verify an explicit namespace route."""
    fields = {'schema', 'kind', 'module', 'lean_toolchain', 'route', 'before_source_sha256',
              'before_raw_sha256', 'before_provenance', 'original', 'current', 'module_system'}
    style.keys(receipt, fields, fields, 'namespace receipt')
    style.require(receipt['schema'] == 1 and receipt['kind'] == 'namespace-route' and
                  receipt['module'] == module and receipt['lean_toolchain'] == after['lean_toolchain'],
                  'invalid namespace receipt identity')
    style.require(receipt['before_provenance'] == 'retained pre-rename raw export and source; historical artifacts not retained',
                  'invalid namespace evidence provenance')
    for field in ('before_source_sha256', 'before_raw_sha256'):
        style.require(re.fullmatch('[0-9a-f]{64}', receipt[field]) is not None, 'invalid retained input hash')
    route = receipt['route']
    style.keys(route, {'from', 'to'}, {'from', 'to'}, 'namespace route')
    style.require(route['from'] != route['to'] and route['from'] and route['to'], 'empty namespace route')
    original, current = receipt['original'], receipt['current']
    style.require(all(name == row['name'] for name, row in original.items()) and
                  all(name == row['name'] for name, row in current.items()), 'raw declaration key mismatch')
    style.require(after['schema'] == 2 and receipt['module_system'] == after['module_system'][module] and
                  {name: hashed_record(row) for name, row in current.items()} == after['declarations'][module],
                  'namespace current records do not match captured hashes')
    if before is not None:
        style.require(before['schema'] == 2 and before['lean_toolchain'] == after['lean_toolchain'] and
                      receipt['module_system'] == before['module_system'][module] and
                      {name: hashed_record(row) for name, row in original.items()} == before['declarations'][module],
                      'namespace original records do not match captured baseline')
    mapped, count = set(), 0
    for name, row in original.items():
        parts = route_name_components(plain_name_components(name), module, route['from'], route['to'])
        target = '.'.join(str(part) for _, part in parts)
        style.require(target not in mapped and target in current, 'namespace declaration collision or missing target')
        mapped.add(target)
        count += len(namespace_record_changes(row, current[target], module, route['from'], route['to']))
    style.require(mapped == set(current), 'declaration set changed outside namespace route')
    style.require(count > 0, 'empty namespace receipt')
    return count


def record_namespace(module, plan, args, current):
    """Retain separately identified raw evidence; never invent old artifact hashes."""
    original, old_system = raw_declarations(args.before_raw, module)
    updated, new_system = raw_declarations(args.after_raw, module)
    style.require(old_system == new_system, 'module system changed')
    receipt = {'schema': 1, 'kind': 'namespace-route', 'module': module,
               'lean_toolchain': current['lean_toolchain'],
               'route': {'from': args.rename_from, 'to': args.rename_to},
               'before_source_sha256': contracts.file_digest(args.before_source),
               'before_raw_sha256': contracts.file_digest(args.before_raw),
               'before_provenance': 'retained pre-rename raw export and source; historical artifacts not retained',
               'original': original, 'current': updated, 'module_system': old_system}
    baseline_path = args.snapshot_dir / 'baseline' / (module + '.json')
    before = read_snapshot(baseline_path)['contract'] if baseline_path.is_file() else None
    count = validate_namespace_receipt(receipt, module, before, current)
    destination = args.rename_evidence / (module + '.json')
    style.atomic_write(destination, json.dumps(receipt, ensure_ascii=False, separators=(',', ':')) + '\n')
    return [f'recorded {count} verified namespace/name-hygiene changes: {module}; '
            + ('matches captured baseline' if before else 'standalone retained pre-rename raw evidence')], False


ORIGIN_ARTIFACT_SUFFIXES = ('.olean', '.olean.private', '.olean.server', '.ir')
_ORIGIN_SOURCE_RECORDS = {}
_ORIGIN_SOURCE_LOCK = Lock()


def origin_source_record(revision, relative):
    """Share immutable Git source hashes/import tuples within this process.

    Callers validate the exact commit first. A future per repository/commit/path
    prevents concurrent graph traversals from parsing the same source twice.
    Failed reads are not retained; current files and artifacts are never cached.
    """
    key = (str(ROOT.resolve()), str(contracts.ROOT.resolve()), revision, relative)
    with _ORIGIN_SOURCE_LOCK:
        pending = _ORIGIN_SOURCE_RECORDS.get(key)
        owner = pending is None
        if owner:
            pending = Future()
            _ORIGIN_SOURCE_RECORDS[key] = pending
    if owner:
        try:
            text = contracts.run('git', 'show', revision + ':' + relative)
            imports = tuple(dict.fromkeys(row['module'] for row in style.inventory(text)['imports']))
            pending.set_result((style.digest(text), imports))
        except BaseException as error:
            pending.set_exception(error)
            with _ORIGIN_SOURCE_LOCK:
                del _ORIGIN_SOURCE_RECORDS[key]
            raise
    return pending.result()


def origin_revision_graph(module, revision):
    """Read the entire reachable project import graph at an exact Git commit."""
    style.require(re.fullmatch('[0-9a-f]{40,64}', revision) is not None,
                  'origin revision must be an exact Git commit ID')
    resolved = contracts.run('git', 'rev-parse', revision + '^{commit}').strip()
    style.require(resolved == revision, 'origin revision is not a canonical commit ID')
    tracked = set(contracts.run('git', 'ls-tree', '-r', '--name-only', revision).splitlines())
    graph = {}
    def visit(name):
        if name in graph:
            return
        relative = name.replace('.', '/') + '.lean'
        style.require(relative in tracked, f'origin project source is absent: {relative}')
        source_sha256, retained_imports = origin_source_record(revision, relative)
        imports = list(retained_imports)
        project = [item for item in imports if item.replace('.', '/') + '.lean' in tracked]
        graph[name] = {'path': relative, 'source_sha256': source_sha256,
                       'imports': imports, 'project_imports': project}
        for dependency in project:
            visit(dependency)
    visit(module)
    toolchain = contracts.run('git', 'show', revision + ':lean-toolchain').strip()
    manifest = contracts.run('git', 'show', revision + ':lake-manifest.json')
    style.require(toolchain == (ROOT / 'lean-toolchain').read_text().strip(),
                  'origin revision uses another Lean toolchain')
    style.require(style.digest(manifest) == contracts.file_digest(ROOT / 'lake-manifest.json'),
                  'origin revision dependency manifest differs from the pinned working tree')
    return graph, toolchain, style.digest(manifest)


def origin_compiler_identity():
    """Bind reconstruction to the executable selected by the pinned toolchain."""
    executable = Path(contracts.run('lake', 'env', 'which', 'lean').strip())
    return {'version': contracts.run(str(executable), '--version').strip(),
            'sha256': contracts.file_digest(executable)}


def validate_origin_receipt(receipt, module, before, after):
    """Require original declarations, optionally with separately verified hygiene.

    Original compiled bytes are hashed and freshly exported when recording.
    Subsequent checks verify their retained evidence against Git and every
    current declaration. Schema 2 composes the existing strict hygiene validator
    with the complete authentic original records; no proof changes are admitted.
    """
    fields = {'schema', 'kind', 'module', 'source_revision', 'lean_toolchain',
              'dependency_manifest_sha256', 'compiler', 'export_tools', 'graph',
              'original_artifacts', 'original', 'module_system',
              'original_raw_sha256', 'intermediate_contract_sha256'}
    if receipt.get('schema') == 2:
        fields.add('hygiene')
    style.keys(receipt, fields, fields, 'original-commit receipt')
    style.require(receipt['schema'] in {1, 2} and receipt['kind'] == 'original-commit' and
                  receipt['module'] == module, 'invalid original-commit receipt identity')
    style.require(before['schema'] == after['schema'] == 2 and
                  receipt['intermediate_contract_sha256'] == style.digest(style.encoded(before)),
                  'original-commit receipt does not bind this intermediate baseline')
    style.require(receipt['source_revision'] == before['source_revision'],
                  'origin commit differs from the historical capture revision')
    graph, toolchain, manifest = origin_revision_graph(module, receipt['source_revision'])
    style.require(receipt['graph'] == graph, 'original project dependency graph or source hashes changed')
    style.require(receipt['lean_toolchain'] == before['lean_toolchain'] == after['lean_toolchain'] == toolchain and
                  receipt['dependency_manifest_sha256'] == manifest and
                  receipt['compiler'] == origin_compiler_identity(), 'original toolchain identity mismatch')
    style.require(receipt['export_tools'] == after['tool_sha256'], 'original export tools changed')
    artifacts = receipt['original_artifacts']
    style.require(set(artifacts) == set(graph), 'incomplete original artifact closure')
    for hashes in artifacts.values():
        style.keys(hashes, set(ORIGIN_ARTIFACT_SUFFIXES), set(ORIGIN_ARTIFACT_SUFFIXES), 'original artifacts')
        style.require(all(isinstance(value, str) and re.fullmatch('[0-9a-f]{64}', value)
                          for value in hashes.values()), 'missing or invalid original artifact hash')
    original = receipt['original']
    style.require(isinstance(original, dict) and original and
                  all(name == row['name'] for name, row in original.items()), 'invalid original raw declarations')
    style.require(receipt['original_raw_sha256'] == style.digest(style.encoded(original)),
                  'original raw declaration digest mismatch')
    style.require(receipt['module_system'] == before['module_system'][module] == after['module_system'][module],
                  'original module-system identity changed')
    original_hashes = {name: hashed_record(row) for name, row in original.items()}
    if receipt['schema'] == 1:
        style.require(original_hashes == after['declarations'][module],
                      'current declarations differ from the original commit')
    else:
        original_capture = {**after, 'declarations': {module: original_hashes}}
        accepted, _ = validate_hygiene_receipt(receipt['hygiene'], module, original_capture, after)
        style.require(accepted == set(contracts.differences(original_capture, after)),
                      'current declarations contain changes beyond verified original-commit hygiene')
    style.require(before['declarations'][module] != after['declarations'][module],
                  'original-commit evidence does not correct an intermediate declaration difference')
    return len(original)


def record_origin(module, args, before, after):
    """Check reconstructed sources/artifacts and freshly export their raw records."""
    import os
    import subprocess
    import tempfile
    revision = contracts.run('git', 'rev-parse', args.origin_revision + '^{commit}').strip()
    graph, toolchain, manifest = origin_revision_graph(module, revision)
    artifacts = {}
    for name, entry in graph.items():
        source = args.origin_source_root / entry['path']
        style.require(contracts.file_digest(source) == entry['source_sha256'],
                      f'reconstructed source differs from original commit: {name}')
        relative = name.replace('.', '/')
        artifacts[name] = {suffix: contracts.file_digest(args.origin_artifact_root / (relative + suffix))
                           for suffix in ORIGIN_ARTIFACT_SUFFIXES}
        style.require(all(artifacts[name].values()), f'missing original compiled artifacts: {name}')
    original, system = raw_declarations(args.before_raw, module)
    # Import through the complete reconstructed project closure, with package
    # artifacts still selected by the exact pinned dependency manifest.
    command, env = contracts.contract_invocation(module, args.origin_artifact_root)
    exported = subprocess.run(command, cwd=ROOT, env=env, text=True,
                              capture_output=True, check=True).stdout
    with tempfile.TemporaryDirectory(prefix='module-style-origin-') as temporary:
        raw_path = Path(temporary) / 'export.jsonl'
        raw_path.write_text(exported)
        checked, checked_system = raw_declarations(raw_path, module)
    style.require(original == checked and system == checked_system,
                  'original raw records differ from the reconstructed artifacts')
    for name, entry in graph.items():
        style.require(contracts.file_digest(args.origin_source_root / entry['path']) == entry['source_sha256'] and
                      artifacts[name] == {suffix: contracts.file_digest(args.origin_artifact_root /
                          (name.replace('.', '/') + suffix)) for suffix in ORIGIN_ARTIFACT_SUFFIXES},
                      f'original reconstruction changed during export: {name}')
    receipt = {'schema': 1, 'kind': 'original-commit', 'module': module,
               'source_revision': revision, 'lean_toolchain': toolchain,
               'dependency_manifest_sha256': manifest, 'compiler': origin_compiler_identity(),
               'export_tools': after['tool_sha256'], 'graph': graph, 'original_artifacts': artifacts,
               'original': original, 'module_system': system,
               'original_raw_sha256': style.digest(style.encoded(original)),
               'intermediate_contract_sha256': style.digest(style.encoded(before))}
    original_hashes = {name: hashed_record(row) for name, row in original.items()}
    if original_hashes != after['declarations'][module]:
        # Recapture the current raw records and bind them to the existing capture.
        # The original records above have already been freshly authenticated
        # against the complete, unchanged reconstruction of the original graph.
        current_command, current_env = contracts.contract_invocation(module, args.artifact_root)
        exported_current = subprocess.run(current_command, cwd=ROOT, env=current_env,
                                         text=True, capture_output=True, check=True).stdout
        with tempfile.TemporaryDirectory(prefix='module-style-origin-hygiene-') as temporary:
            current_path = Path(temporary) / 'current.jsonl'
            current_path.write_text(exported_current)
            original_capture = {**after, 'declarations': {module: original_hashes}}
            receipt['hygiene'] = make_hygiene_receipt(
                module, original_capture, after, args.before_raw, current_path)
        receipt['schema'] = 2
    count = validate_origin_receipt(receipt, module, before, after)
    destination = args.origin_evidence / (module + '.json')
    style.atomic_write(destination, json.dumps(receipt, ensure_ascii=False, separators=(',', ':')) + '\n')
    return [f'recorded original-commit restoration: {module}: {count} declarations'
            + origin_hygiene_summary(receipt) + '; historical baseline retained'], False


def origin_hygiene_summary(receipt):
    """Describe the already validated, narrowly admitted hygiene changes."""
    if receipt['schema'] == 1:
        return '; exact match'
    count = sum(len(entry['binder_names']) + len(entry.get('metadata_positions', []))
                for entry in receipt['hygiene']['entries'])
    return f'; {count} verified binder-name/source-position changes'


def selected_plans(inputs):
    """Resolve plan files and reject duplicate module ownership."""
    files = set()
    for value in inputs:
        if value.is_dir():
            files.update(value.rglob('*.json'))
        elif value.is_file():
            files.add(value)
        else:
            raise ValueError(f'plan path does not exist: {value}')
    plans = {}
    for path in sorted(files):
        plan = style.read_json(path)
        style.validate_plan(plan)
        source = style.source_path(plan)
        module = '.'.join(source.relative_to(ROOT).with_suffix('').parts)
        if module in plans:
            raise ValueError(f'duplicate module plan: {module}')
        plans[module] = plan
    if not plans:
        raise ValueError('no module-style plans selected')
    return plans


def input_state(module, artifact_root):
    """Bind a reusable capture to source, compiled bytes, and capture tools."""
    relative = Path(*module.split('.'))
    source = ROOT / relative.with_suffix('.lean')
    olean = artifact_root / relative.with_suffix('.olean')
    if not source.is_file() or not olean.is_file():
        raise FileNotFoundError(f'missing source or compiled artifact for {module}; build first')
    artifacts = {suffix or '.olean': contracts.file_digest(Path(str(olean) + suffix))
                 for suffix in contracts.ARTIFACT_SUFFIXES}
    return {
        'module': module,
        'source_sha256': contracts.file_digest(source),
        'artifacts': artifacts,
        'artifact_root': str(artifact_root),
        'lean_toolchain': (ROOT / 'lean-toolchain').read_text().strip(),
        'source_revision': contracts.run('git', 'rev-parse', 'HEAD').strip(),
        'tools': {str(path.relative_to(ROOT)): contracts.file_digest(path) for path in
                  (Path(__file__).resolve(), DRIVER.resolve(), *contracts.reader_tool_paths(),
                   ROOT / 'scripts/module_style/core.py', ROOT / 'scripts/run-lake.sh')},
    }


def read_snapshot(path, state=None):
    """Check a completed snapshot before reusing its declaration hashes."""
    value = style.read_json(path)
    if value.get('schema') != 1 or value.get('key') != style.digest(style.encoded(value.get('inputs'))):
        raise ValueError(f'invalid snapshot provenance: {path}')
    if value.get('contract_sha256') != style.digest(style.encoded(value.get('contract'))):
        raise ValueError(f'invalid snapshot contract digest: {path}')
    if state is not None and value['inputs'] != state:
        raise ValueError(f'snapshot input mismatch: {path}')
    contract = value['contract']
    inputs = value['inputs']
    module = inputs['module']
    if (contract['schema'] != 2 or contract['modules'] != [module]
            or contract['sources'][module]['sha256'] != inputs['source_sha256']
            or contract['artifacts'][module] != inputs['artifacts']
            or contract['lean_toolchain'] != inputs['lean_toolchain']
            or contract['source_revision'] != inputs['source_revision']
            or contract['tool_sha256']['driver'] != inputs['tools'][str(DRIVER.relative_to(ROOT))]
            or contract['tool_sha256']['lean'] != contracts.digest(json.dumps({
                str(path.relative_to(ROOT)): inputs['tools'][str(path.relative_to(ROOT))]
                for path in contracts.reader_tool_paths()}, sort_keys=True, separators=(',', ':')).encode())):
        raise ValueError(f'inconsistent snapshot contract provenance: {path}')
    return value


def current_capture(module, artifact_root, directory, state):
    """Reuse a complete matching capture or atomically retain a new one."""
    key = style.digest(style.encoded(state))
    path = directory / 'cache' / module / (key + '.json')
    if path.is_file():
        return read_snapshot(path, state), True
    contract = contracts.capture([module], artifact_root, False, schema=2)
    if input_state(module, artifact_root) != state:
        raise ValueError(f'source, artifacts, or tools changed during capture: {module}')
    value = {'schema': 1, 'key': key, 'inputs': state, 'contract': contract,
             'contract_sha256': style.digest(style.encoded(contract))}
    style.atomic_write(path, style.encoded(value))
    return read_snapshot(path, state), False


def process_module(module, plan, args):
    """Capture one baseline or compare one rebuilt module against its baseline."""
    baseline_path = args.snapshot_dir / 'baseline' / (module + '.json')
    state = input_state(module, args.artifact_root)
    expected = plan['source_sha256'] if args.command == 'capture' else plan.get('prepared', {}).get('result_sha256')
    if args.command == 'capture' and state['source_sha256'] != expected and args.prior_plans:
        prior_path = args.prior_plans / Path(plan['path']).with_suffix('.json')
        if prior_path.is_file():
            prior = style.read_json(prior_path)
            source = style.source_path(plan).read_text()
            if prior['source_sha256'] == plan['source_sha256'] and style.apply_plan(prior, source) == source:
                expected = prior['prepared']['result_sha256']
    if not expected or state['source_sha256'] != expected:
        phase = 'reviewed original' if args.command == 'capture' else 'prepared result'
        raise ValueError(f'{module}: source does not match the plan\'s {phase} '
                         f'(expected {expected}, found {state["source_sha256"]}); '
                         + ('capture before applying the plan' if args.command == 'capture' else
                            'update the reviewed plan for integration edits and rebuild before checking'))
    if plan['source_sha256'] == plan.get('prepared', {}).get('result_sha256'):
        return [f'no source changes: {module}'], False
    if args.command == 'capture' and baseline_path.is_file():
        baseline = read_snapshot(baseline_path)
        if baseline['inputs'] != state:
            raise ValueError(f'{module}: baseline already exists for different inputs; use a new snapshot directory')
        return [f'reused baseline: {module}'], False
    rename_path = args.rename_evidence / (module + '.json') if args.rename_evidence else None
    if args.command not in {'capture', 'record-rename'} and not baseline_path.is_file() and not (rename_path and rename_path.is_file()):
        raise FileNotFoundError(f'missing baseline: {baseline_path}; capture before applying plans')
    current, reused = current_capture(module, args.artifact_root, args.snapshot_dir, state)
    if args.command == 'capture':
        style.atomic_write(baseline_path, style.encoded(current))
        return [f'captured {len(current["contract"]["declarations"][module])} declarations: {module}'
                + (' (reused capture)' if reused else '')], False
    after = current['contract']
    if args.command == 'record-rename':
        return record_namespace(module, plan, args, after)
    before = read_snapshot(baseline_path)['contract'] if baseline_path.is_file() else None
    if args.command == 'record-origin':
        return record_origin(module, args, before, after)
    origin_path = args.origin_evidence / (module + '.json') if args.origin_evidence else None
    if args.command == 'check' and origin_path and origin_path.is_file():
        receipt = style.read_json(origin_path)
        count = validate_origin_receipt(receipt, module, before, after)
        return [f'verified original-commit restoration: {module}: {count} declarations'
                + origin_hygiene_summary(receipt) + '; historical baseline retained'], False
    if args.command == 'check' and rename_path and rename_path.is_file():
        count = validate_namespace_receipt(style.read_json(rename_path), module, before, after)
        return [f'verified namespace route and hygiene: {module}: {count} changes; '
                + ('captured baseline' if before else 'standalone pre-rename raw evidence')], False
    if args.command == 'record-hygiene':
        receipt = make_hygiene_receipt(module, before, after, args.before_raw, args.after_raw)
        destination = args.hygiene_evidence / (module + '.json')
        # Store each original raw record once, followed by only its checked name edits.
        style.atomic_write(destination, json.dumps(receipt, ensure_ascii=False, separators=(',', ':')) + '\n')
        _, count = validate_hygiene_receipt(receipt, module, before, after)
        return [f'recorded {count} verified binder-name/source-position changes: {module} ({destination})'], False
    changes = contracts.differences(before, after)
    hygiene = []
    if changes and args.hygiene_evidence:
        receipt_path = args.hygiene_evidence / (module + '.json')
        if receipt_path.is_file():
            accepted, count = validate_hygiene_receipt(style.read_json(receipt_path), module, before, after)
            style.require(accepted <= set(changes), 'hygiene evidence does not describe current differences')
            changes = [change for change in changes if change not in accepted]
            hygiene = [f'hygiene-only: {module}: {count} verified binder-name/source-position changes in {len(accepted)} expression fields']
    lines = ['declaration\t' + '\t'.join(change) for change in changes]
    if before['module_system'] != after['module_system']:
        lines.append(f'module-system\t{module}\tchanged')
    failed = bool(lines)
    lines = hygiene + lines
    lines.append(f'{"changed" if failed else "unchanged except verified hygiene" if hygiene else "unchanged"}: {module}'
                 + (' (reused capture)' if reused else ''))
    return lines, failed


def main(argv=None):
    """Run independent captures with bounded, configurable concurrency."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('command', choices=('capture', 'check', 'record-hygiene', 'record-rename', 'record-origin'))
    parser.add_argument('--plans', nargs='+', type=Path, required=True,
                        help='plan JSON files or directories containing plans')
    parser.add_argument('--snapshot-dir', type=Path, default=ROOT / '.lake/module-style-contracts')
    parser.add_argument('--prior-plans', type=Path,
                        help='validated import-only plans already applied before full review')
    parser.add_argument('--artifact-root', type=Path, default=ROOT / '.lake/build/lib/lean')
    parser.add_argument('--jobs', type=int, default=4)
    parser.add_argument('--hygiene-evidence', type=Path,
                        help='explicit directory of verified binder-macro-scope receipts')
    parser.add_argument('--before-raw', type=Path,
                        help='record-hygiene: recovered original complete raw JSONL records')
    parser.add_argument('--after-raw', type=Path,
                        help='record-hygiene: current complete raw JSONL records')
    parser.add_argument('--rename-evidence', type=Path, help='explicit directory of strict namespace-route receipts')
    parser.add_argument('--before-source', type=Path, help='record-rename: retained pre-rename source')
    parser.add_argument('--rename-from', help='record-rename: exact old namespace prefix')
    parser.add_argument('--rename-to', help='record-rename: exact new namespace prefix')
    parser.add_argument('--origin-evidence', type=Path, help='explicit directory of exact original-commit restoration receipts')
    parser.add_argument('--origin-revision', help='record-origin: original Git commit')
    parser.add_argument('--origin-source-root', type=Path, help='record-origin: reconstructed exact original project sources')
    parser.add_argument('--origin-artifact-root', type=Path, help='record-origin: complete rebuilt original project artifact closure')
    args = parser.parse_args(argv)
    if args.jobs < 1:
        parser.error('--jobs must be positive')
    args.snapshot_dir = args.snapshot_dir.resolve()
    args.artifact_root = args.artifact_root.resolve()
    plans = selected_plans(args.plans)
    if args.command == 'record-hygiene' and (len(plans) != 1 or not args.before_raw or
                                            not args.after_raw or not args.hygiene_evidence):
        parser.error('record-hygiene requires one module, --before-raw, --after-raw and --hygiene-evidence')
    if args.command == 'record-rename' and (len(plans) != 1 or not all([args.before_raw, args.after_raw, args.before_source, args.rename_from, args.rename_to, args.rename_evidence])):
        parser.error('record-rename requires one plan, --before-raw, --after-raw, --before-source, --rename-from, --rename-to and --rename-evidence')
    if args.command == 'record-origin' and (len(plans) != 1 or not all([args.origin_evidence, args.origin_revision, args.origin_source_root, args.origin_artifact_root, args.before_raw])):
        parser.error('record-origin requires one plan, --origin-evidence, --origin-revision, --origin-source-root, --origin-artifact-root and --before-raw')
    if args.command != 'record-origin' and any([args.origin_revision, args.origin_source_root, args.origin_artifact_root]):
        parser.error('original reconstruction inputs require record-origin')
    if args.command not in {'record-hygiene', 'record-rename', 'record-origin'} and (args.before_raw or args.after_raw):
        parser.error('--before-raw and --after-raw require a record command')
    if args.command != 'record-rename' and any([args.before_source, args.rename_from, args.rename_to]):
        parser.error('--before-source, --rename-from and --rename-to require record-rename')
    failed = False
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        futures = {pool.submit(process_module, module, plan, args): module
                   for module, plan in plans.items()}
        for future in as_completed(futures):
            try:
                lines, changed = future.result()
                failed |= changed
                print('\n'.join(lines), flush=True)
            except Exception as exc:
                failed = True
                print(f'{futures[future]}: {exc}', file=sys.stderr, flush=True)
    return int(failed)


if __name__ == '__main__':
    try:
        raise SystemExit(main())
    except (ValueError, KeyError, OSError) as error:
        raise SystemExit(str(error)) from error
