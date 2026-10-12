"""Identify configured standalone owners and their compiled import consumers."""

from pathlib import Path
import tomllib


def configured_entrypoints(root):
    """Select all executable roots and operational library roots from Lake."""
    config = Path(root) / 'lakefile.toml'
    targets = tomllib.loads(config.read_text())
    roots = set()
    for kind in ('lean_lib', 'lean_exe'):
        for target in targets.get(kind, []):
            names = target.get('roots', []) + ([target['root']] if 'root' in target else [])
            roots.update(name for name in names
                         if kind == 'lean_exe' or name.startswith('scripts.'))
    return roots


def entrypoint_importers(imports, entrypoints):
    """Find standalone environments using the complete retained import graph."""
    containing = set(entrypoints) & imports.keys()
    reverse = {}
    for name, dependencies in imports.items():
        for dependency in dependencies:
            if dependency not in imports:
                raise ValueError(f'missing compiled import inventory: {name} -> {dependency}')
            reverse.setdefault(dependency, []).append(name)
    pending = list(containing)
    while pending:
        for parent in reverse.get(pending.pop(), []):
            if parent not in containing:
                containing.add(parent)
                pending.append(parent)
    return containing
