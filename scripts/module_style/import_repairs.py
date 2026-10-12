#!/usr/bin/env python3
"""Prepare direct proof-tactic imports without claiming a full module review.

Only authored sources with an unquoted tactic identifier are selected. Existing
imports, references and documentation are preserved; full reviewed plans take
precedence. This helper prepares ordinary module_style plans and never applies
them. The primary reviewer inspects and applies the resulting plans.
"""
from __future__ import annotations

import argparse
from pathlib import Path

from scripts.module_style import core as style

OWNERS = {'ring1': 'Purelib.Tactic.Ring',
          'omega': 'Purelib.Tactic.QuotientFreeOmega',
          'omega0': 'Purelib.Tactic.QuotientFreeOmega'}


def prepare_repair(path: str, text: str, prior=None, previous=None):
    """Extend checked prior instructions against their retained original source.

    A previously applied repair is inverted and verified before adding imports;
    its original hash and existing import decisions remain authoritative.
    """
    if prior is not None:
        style.require(prior['path'] == path, 'prior repair belongs to another source')
        if style.digest(text) not in {prior['source_sha256'], prior['prepared']['result_sha256']}:
            style.require(previous is not None and previous['path'] == path and
                          previous['source_sha256'] == prior['source_sha256'],
                          'source is not the prior plan result; supply its retained previous repair')
            text = style.recover_original(previous, text)
            style.apply_plan(prior, text)
        elif style.digest(text) != prior['source_sha256']:
            text = style.recover_original(prior, text)
        else:
            style.apply_plan(prior, text)
        plan = {key: value for key, value in prior.items() if key != 'prepared'}
        decisions = [dict(row) for row in plan['imports']]
    else:
        plan = dict(schema=1, path=path, source_sha256=style.digest(text),
                    review='Direct proof-tactic dependency repair only. Namespace and documentation review remains pending.',
                    opens=[], rewrites=[], docstrings={})
        decisions = []
        for row in style.inventory(text)['imports']:
            existing = next((item for item in decisions if item['module'] == row['module']), None)
            if existing is None:
                decisions.append(dict(module=row['module'], mode=row['mode'],
                                      reason='Preserve the existing import pending the separate full module review.'))
            elif row['mode'] != existing['mode']:
                existing['also'] = list(dict.fromkeys([*existing.get('also', []), row['mode']]))
    identifiers = {token.text for token in style.inventory(text)['tokens'] if token.kind == 'ident'}
    present = {row['module'] for row in decisions if row['mode'] != 'remove'}
    module = path.removesuffix('.lean').replace('/', '.')
    needed = {}
    for tactic, owner in OWNERS.items():
        if tactic in identifiers and owner not in present and owner != module:
            needed.setdefault(owner, []).append(tactic)
    if not needed:
        return None
    for owner, tactics in needed.items():
        style.require(not any(row['module'] == owner for row in decisions),
                      f'existing decision explicitly removes needed tactic owner: {owner}')
        decisions.append(dict(module=owner, mode='import',
                              reason=f'This source invokes {", ".join(tactics)}; import its proof-tactic owner directly.'))
    plan['imports'] = decisions
    prepared, result = style.prepare(plan, text)
    style.require(style.apply_plan(prepared, result) == result, f'non-idempotent repair: {path}')
    return prepared


def retain_previous(history: Path, plan):
    """Keep a checked prior result in immutable storage outside plan traversal."""
    destination = history / Path(plan['path']).with_suffix('') / (plan['prepared']['result_sha256'] + '.json')
    if destination.exists():
        style.require(style.read_json(destination) == plan, f'prior repair history conflicts: {destination}')
    else:
        style.atomic_write(destination, style.encoded(plan))
    return destination


def prepare_repairs(manifest: Path, output: Path, history: Path):
    """Prepare authored missing imports while preserving existing applied plans."""
    count = 0
    for entry in style.read_json(manifest)['files']:
        if entry['classification'] != 'authored':
            continue
        relative = Path(entry['path']).with_suffix('.json')
        if (style.ROOT / 'docs/module-style/plans' / relative).exists():
            continue
        destination = output / relative
        prior = style.read_json(destination) if destination.exists() else None
        text = (style.ROOT / entry['path']).read_text()
        previous_path = history / Path(entry['path']).with_suffix('') / (style.digest(text) + '.json')
        previous = style.read_json(previous_path) if previous_path.exists() else None
        prepared = prepare_repair(entry['path'], text, prior, previous)
        if prepared is not None:
            if prior is not None:
                retain_previous(history, prior)
            style.atomic_write(destination, style.encoded(prepared))
            count += 1
    return count


def main():
    """Prepare plans from the explicit authored-source manifest."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--manifest', type=Path, default=style.ROOT / 'docs/module-style/manifest.json')
    parser.add_argument('--output', type=Path, default=style.ROOT / 'docs/module-style/import-repairs')
    parser.add_argument('--history', type=Path, default=style.ROOT / 'docs/module-style/import-repair-history',
                        help='immutable previous plans kept outside the active repair directory')
    args = parser.parse_args()
    print(f'Prepared {prepare_repairs(args.manifest, args.output, args.history)} import-only plans; no sources changed.')


if __name__ == '__main__':
    main()
