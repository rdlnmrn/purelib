"""Retain actual compiled first owners for independent module scheduling."""

import fcntl
import json
import os
from pathlib import Path
import tempfile

from scripts.lean_module_data.audit import AuditObservation
from scripts.paths import ROOT
from .artifact_inputs import digest, identity, verify_inputs


def name_key(parts):
    """Encode exact name components without ambiguity from dots or quoting."""
    return ''.join('s' + value.encode('utf-8').hex() + ';' if tag == 1 else f'n{value};'
                   for tag, value in parts)


def prepare(context, cache, search):
    """Cache ownership under the complete compiled environment and reader bytes."""
    helpers = [Path(__file__), *sorted((ROOT / 'scripts/lean_module_data').glob('*.py'))]
    binding = {'schema': 1, 'compiled_inputs': context,
               'helpers': {str(path): digest(path) for path in helpers}}
    folder = Path(cache) / 'module-owners' / identity(binding)
    folder.mkdir(parents=True, exist_ok=True)
    with (folder / 'prepare.lock').open('w') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        verify_inputs(context, search)
        marker, output = folder / 'complete.json', folder / 'owners.tsv'
        if marker.exists():
            receipt = json.loads(marker.read_text())
            if receipt.get('binding') != binding or receipt.get('sha256') != digest(output):
                raise ValueError('invalid compiled module ownership receipt')
            return output
        observation = AuditObservation(context['selected_modules'], search)
        seen = set()
        with tempfile.NamedTemporaryFile(mode='w', dir=folder, delete=False) as pending:
            for name in observation.by_name:
                owner = observation.owners.get(name)
                if owner is None or '\t' in owner or '\n' in owner:
                    raise ValueError('compiled declaration has no unambiguous module owner')
                key = name_key(name[1])
                if not key or key in seen:
                    raise ValueError('duplicate structural name in compiled ownership inventory')
                seen.add(key)
                pending.write(owner + '\t' + key + '\n')
        verify_inputs(context, search)
        os.replace(pending.name, output)
        with tempfile.NamedTemporaryFile(mode='w', dir=folder, delete=False) as pending:
            json.dump({'binding': binding, 'sha256': digest(output), 'declarations': len(seen)}, pending,
                      sort_keys=True)
            pending.write('\n')
        os.replace(pending.name, marker)
        return output
