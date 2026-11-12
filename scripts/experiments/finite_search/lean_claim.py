"""Bind the pilot's first-order claim to a previously checked Lean export.

This intentionally narrow projection checks the selected algorithm's body and
the complete concrete theorem type. It does not translate Lean proof bodies or
establish the soundness of Lean's exported datatype implementation. Run nanoda
on the exact stream separately before treating it as checked Lean evidence.
"""

import argparse
import hashlib
import json
from pathlib import Path

from .check import Checker, Rejected, goal, require


PREFIX = 'KernelSurvey.FiniteSearch.'


class Export:
    """Read names and expression references from this bounded pilot stream."""

    def __init__(self, path):
        self.names, self.expressions, self.declarations = {0: ''}, {}, {}
        for line in Path(path).read_text().splitlines():
            row = json.loads(line)
            if 'in' in row:
                value = row.get('str', row.get('num'))
                prefix = self.names[value['pre']]
                suffix = str(value.get('str', value.get('i')))
                require(row['in'] not in self.names, 'duplicate exported name index')
                self.names[row['in']] = prefix + ('.' if prefix else '') + suffix
            elif 'ie' in row:
                require(row['ie'] not in self.expressions, 'duplicate exported expression index')
                self.expressions[row['ie']] = {k: v for k, v in row.items() if k != 'ie'}
            else:
                for kind in ('def', 'thm'):
                    if kind in row:
                        data = row[kind]
                        name = self.names[data['name']]
                        require(name not in self.declarations, 'duplicate exported declaration')
                        self.declarations[name] = (kind, data)

    def node(self, index):
        """Ignore expression metadata while preserving its actual expression."""
        value = self.expressions[index]
        while 'mdata' in value:
            value = self.expressions[value['mdata']['expr']]
        return value

    def application(self, index):
        """Decompose a retained application into its literal constant and arguments."""
        arguments = []
        value = self.node(index)
        while 'app' in value:
            arguments.append(value['app']['arg'])
            value = self.node(value['app']['fn'])
        require('const' in value, 'expected a constant-headed application')
        return self.names[value['const']['name']], list(reversed(arguments))

    def is_constant(self, index, name):
        """Check a literal constant without unfolding unknown aliases."""
        return self.application(index) == (name, [])

    def is_nat_list(self, index):
        """Check the concrete list carrier and its original natural element type."""
        name, args = self.application(index)
        return name == 'List' and len(args) == 1 and self.is_constant(args[0], 'Nat')

    def term(self, index, context):
        """Project only the pilot's specified data and original selected functions."""
        value = self.node(index)
        if 'bvar' in value:
            offset = value['bvar']
            require(type(offset) is int and 0 <= offset < len(context)
                    and context[offset] is not None, 'invalid object variable reference')
            return context[offset]
        name, args = self.application(index)
        if name in (PREFIX + 'selected', PREFIX + 'accepts') and len(args) == 1:
            symbol = 'find' if name.endswith('selected') else 'test'
            return symbol, self.term(args[0], context)
        if name == 'Option.some' and len(args) == 2 and self.is_constant(args[0], 'Nat'):
            return 'some', self.term(args[1], context)
        if name == 'Bool.true' and not args:
            return ('true',)
        raise Rejected('unsupported Lean term: ' + name)

    def formula(self, index, context):
        """Project the exact equality, membership and conjunction in the source claim."""
        name, args = self.application(index)
        if name == 'Eq' and len(args) == 3:
            left, right = self.term(args[1], context), self.term(args[2], context)
            sort = Checker().term(left, {'xs': 'ListNat', 'target': 'Nat'})
            owner, inputs = self.application(args[0])
            require((sort in ('Nat', 'Bool') and owner == sort and not inputs)
                    or (sort == 'OptionNat' and owner == 'Option' and len(inputs) == 1
                        and self.is_constant(inputs[0], 'Nat')), 'equality carrier changed')
            return 'eq', left, right
        if name == 'And' and len(args) == 2:
            return 'and', self.formula(args[0], context), self.formula(args[1], context)
        if name == 'Membership.mem' and len(args) == 5:
            require(self.is_constant(args[0], 'Nat') and self.is_nat_list(args[1]),
                    'membership carrier changed')
            instance, inputs = self.application(args[2])
            require(instance == 'List.instMembership' and len(inputs) == 1
                    and self.is_constant(inputs[0], 'Nat'), 'membership instance changed')
            return 'mem', self.term(args[4], context), self.term(args[3], context)
        raise Rejected('unsupported Lean formula: ' + name)

    def claim(self):
        """Bind the original algorithm and both object binders before the logical premise."""
        kind, selected = self.declarations[PREFIX + 'selected']
        require(kind == 'def', 'selected algorithm is not a definition')
        body = self.node(selected['value'])
        require('lam' in body and self.is_nat_list(body['lam']['type']),
                'selected algorithm input changed')
        name, args = self.application(body['lam']['body'])
        require(name == 'List.find?' and len(args) == 3
                and self.is_constant(args[0], 'Nat')
                and self.is_constant(args[1], PREFIX + 'accepts')
                and self.node(args[2]) == {'bvar': 0},
                'selected algorithm no longer uses the original list search and predicate')
        kind, declaration = self.declarations[PREFIX + 'selected_sound']
        require(kind == 'thm', 'source claim is not a theorem')
        value = self.node(declaration['type'])
        require('forallE' in value and self.is_nat_list(value['forallE']['type']),
                'source input-list binder changed')
        value = self.node(value['forallE']['body'])
        require('forallE' in value and self.is_constant(value['forallE']['type'], 'Nat'),
                'source target binder changed')
        value = self.node(value['forallE']['body'])
        require('forallE' in value, 'missing successful-result premise')
        context = [('var', 'target'), ('var', 'xs')]
        premise = self.formula(value['forallE']['type'], context)
        conclusion = self.formula(value['forallE']['body'], [None, *context])
        result = 'imp', premise, conclusion
        require(result == goal(('var', 'xs'), ('var', 'target')),
                'exported theorem is a different first-order claim')
        return result


def main():
    """Check the certificate and its source claim, retaining the consumed stream hash."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('stream', type=Path)
    parser.add_argument('certificate', type=Path)
    args = parser.parse_args()
    try:
        document = json.loads(args.certificate.read_text())
        result = Checker().certificate(document)
        Export(args.stream).claim()
    except (Rejected, OSError, KeyError, json.JSONDecodeError) as error:
        parser.exit(1, 'rejected: ' + str(error) + '\n')
    result['lean_stream_sha256'] = hashlib.sha256(args.stream.read_bytes()).hexdigest()
    print(json.dumps(result, sort_keys=True))


if __name__ == '__main__':
    main()
