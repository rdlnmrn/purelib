"""Independently select source roots using the authoritative artifact predicate."""

from scripts.lean_module_data.audit import AuditObservation
from scripts.lean_module_data.audit_metadata import RootMetadata, audit_root


def authoritative_roots(modules, search):
    """Retain scanned identity and first owner for every distinct kernel root."""
    observation = AuditObservation(modules, search)
    metadata = RootMetadata(observation)
    roots, seen = [], set()
    for module in modules:
        names, _ = observation.inventory(module)
        for name in names:
            ref = observation.by_name.get(name)
            identity = module, name
            if ref is None or identity in seen:
                continue
            seen.add(identity)
            if audit_root(name, ref, metadata):
                roots.append({'scanned_module': module, 'owner': observation.owners.get(name),
                              'name': observation.text(name), 'phase': 'kernel'})
    return {'schema': 2, 'selected_modules': modules, 'roots': roots}


def validate_roots(candidate, expected):
    """Require exact independent root records rather than a producer root count."""
    if candidate != expected:
        raise ValueError('native selected-root inventory differs from the authoritative artifact predicate')
