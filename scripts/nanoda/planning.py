"""Plan one shared ordinary graph and separate conflicting script environments."""

from pathlib import Path
import json

from scripts.verification.environments import configured_entrypoints, entrypoint_importers
from .artifact_inputs import identity


def plan(modules, context, repository):
    """Preserve exact selected module coverage without round-robin duplication."""
    if not modules or len(modules) != len(set(modules)) or any(not name for name in modules):
        raise ValueError('empty or duplicate selected modules')
    if context['selected_modules'] != modules or context['inventory']['roots'] != modules:
        raise ValueError('compiled inputs do not bind the selected modules')
    nodes = context['inventory']['modules']
    imports = {node['name']: node['imports'] for node in nodes}
    if len(imports) != len(nodes) or any(name not in imports for name in modules):
        raise ValueError('incomplete compiled import inventory')
    isolated = entrypoint_importers(imports, configured_entrypoints(repository))
    ordinary = [name for name in modules if name not in isolated]
    groups = ([ordinary] if ordinary else []) + [[name] for name in modules if name in isolated]
    if sorted(name for group in groups for name in group) != sorted(modules):
        raise ValueError('native group plan lost or repeated a selected module')
    return groups


def group_inputs(context, modules):
    """Retain complete compiled dependencies and exact artifact bytes for one group."""
    nodes = {node['name']: node for node in context['inventory']['modules']}
    if not modules or len(modules) != len(set(modules)):
        raise ValueError('empty or duplicate group modules')
    reached, pending = set(), list(modules)
    while pending:
        name = pending.pop()
        if name in reached:
            continue
        if name not in nodes:
            raise ValueError(f'missing compiled group dependency: {name}')
        reached.add(name)
        pending.extend(nodes[name]['imports'])
    selected = sorted((node for node in context['inventory']['modules'] if node['name'] in reached),
                      key=lambda node: node['name'])
    paths = {str(Path(path).resolve()) for node in selected for path in node['files']}
    paths.update(str(Path(node['files'][0]).resolve().with_suffix('.ir'))
                 for node in selected if len(node['files']) == 3)
    if not paths <= context['files'].keys():
        raise ValueError('group compiled input binding omits emitted artifacts')
    return {'schema': context['schema'], 'selected_modules': modules,
            'inventory': {'schema': 1, 'roots': modules, 'modules': selected},
            'files': {path: context['files'][path] for path in sorted(paths)}}


def canonical_inputs(value):
    """Normalize only inventory presentation, preserving roots and import edge order."""
    nodes = value['inventory']['modules']
    if len({node['name'] for node in nodes}) != len(nodes):
        raise ValueError('duplicate cached compiled inventory module')
    return dict(value, inventory=dict(value['inventory'], modules=sorted(nodes, key=lambda node: node['name'])))


def retained_inputs(directory):
    """Index content-bound old inputs so completed groups survive unrelated scope additions."""
    retained = {}
    for path in sorted(Path(directory).glob('*.json')):
        value = json.loads(path.read_text())
        if path.stem != identity(value) or value.get('schema') != 2:
            raise ValueError(f'corrupt compiled input receipt: {path}')
        canonical = canonical_inputs(value)
        retained.setdefault(identity(canonical), value)
    return retained


def reusable_inputs(incoming, retained):
    """Reuse the exact old protocol only when every field except node listing order agrees."""
    canonical = canonical_inputs(incoming)
    saved = retained.get(identity(canonical))
    if saved is None:
        return canonical
    if canonical_inputs(saved) != canonical:
        raise ValueError('cached compiled input identity disagrees with complete records')
    return saved
