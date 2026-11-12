"""Produce the experimental finite-search derivation deterministically.

This producer is untrusted. Its output must pass the separate first-order
checker, which does not import this module or call its construction helpers.
"""

import argparse
import json
from pathlib import Path


def proof(rule, **fields):
    """Build one explicit inference node without claiming it is valid."""
    return {'rule': rule, **fields}


def variable(name):
    """Construct an object-variable expression."""
    return ('var', name)


def statement(values, target):
    """Write the intended successful-search claim independently of the checker."""
    return ('imp', ('eq', ('find', values), ('some', target)),
            ('and', ('mem', target, values), ('eq', ('test', target), ('true',))))


def assume(name):
    """Refer to a named local premise."""
    return proof('assume', name=name)


def trans(left, right):
    """Compose two proposed equality derivations."""
    return proof('trans', left=left, right=right)


def search_equation(head, tail, accepted):
    """Unfold the search once and substitute the displayed Boolean branch."""
    branch = ('true',) if accepted else ('false',)
    return trans(
        proof('definition', term=('find', ('cons', head, tail))),
        trans(proof('cong', symbol='branch', arguments=[
            assume('accepted' if accepted else 'rejected'),
            proof('refl', term=('some', head)),
            proof('refl', term=('find', tail))]),
            proof('definition', term=('branch', branch, ('some', head), ('find', tail)))))


def certificate():
    """Build one induction proof covering every finite input list and target."""
    head, tail, target = variable('head'), variable('tail'), variable('target')
    nil, cons = ('nil',), ('cons', head, tail)
    base = proof('imp_intro', name='found', premise=statement(nil, target)[1],
                 body=proof('false_elim', conclusion=statement(nil, target)[2],
                            proof=proof('constructor_clash', proof=trans(
                                proof('sym', proof=proof('definition', term=('find', nil))),
                                assume('found')))))
    source_equal = proof('some_injective', proof=trans(
        proof('sym', proof=search_equation(head, tail, True)), assume('found')))
    witness = variable('witness')
    positive = proof('and_intro',
        left=proof('substitute', equality=source_equal, variable='witness',
                   template=('mem', witness, cons),
                   proof=proof('member_head', head=head, tail=tail)),
        right=proof('substitute', equality=source_equal, variable='witness',
                    template=('eq', ('test', witness), ('true',)), proof=assume('accepted')))
    tail_found = trans(proof('sym', proof=search_equation(head, tail, False)), assume('found'))
    tail_claim = proof('imp_elim', function=assume('induction'), argument=tail_found)
    negative = proof('and_intro',
        left=proof('member_tail', head=head, proof=proof('and_left', proof=tail_claim)),
        right=proof('and_right', proof=tail_claim))
    step = proof('imp_intro', name='found', premise=statement(cons, target)[1],
                 body=proof('bool_cases', term=('test', head),
                            true_name='accepted', true=positive,
                            false_name='rejected', false=negative))
    root = proof('list_induction', subject=variable('xs'), variable='items',
                 head='head', tail='tail', hypothesis='induction',
                 schema=statement(variable('items'), target), base=base, step=step)
    return {'schema': 1, 'claim': statement(variable('xs'), target), 'proof': root}


def serialized():
    """Serialize within an explicit source-size budget for this finite pilot."""
    result = json.dumps(certificate(), indent=2, sort_keys=True) + '\n'
    if len(result.encode()) > 65536:
        raise ValueError('finite pilot certificate exceeds its 64 KiB source budget')
    return result


def main():
    """Write the candidate derivation, or check exact reproducibility."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    expected = serialized()
    if args.check:
        if args.output.read_text() != expected:
            parser.exit(1, 'candidate certificate differs from deterministic producer\n')
    else:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(expected)


if __name__ == '__main__':
    main()
