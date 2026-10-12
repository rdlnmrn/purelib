"""Compare complete bounded-fixture declarations after exact identifier remapping.

Both streams share one structural interning table. This compares complete
serialized records, including types, bodies, universes and recursor rules,
without hash-based expression equality or dependence on traversal order.
It does not compare raw ConstantInfo records or establish checker success.
"""

import argparse
import json
from pathlib import Path


class Structures:
    """Intern exact typed JSON structures in one table shared by both exports."""

    def __init__(self):
        self.identities = {}

    def intern(self, category, value):
        """Assign a stable identity using literal structural equality."""
        key = category, self.freeze(value)
        return self.identities.setdefault(key, len(self.identities))

    def freeze(self, value):
        """Distinguish JSON booleans from integers and arrays from objects."""
        if isinstance(value, dict):
            return 'object', tuple((key, self.freeze(item)) for key, item in sorted(value.items()))
        if isinstance(value, list):
            return 'array', tuple(self.freeze(item) for item in value)
        return type(value).__name__, value


class Stream:
    """Resolve names, universes and expressions using a stream's own identifiers."""

    def __init__(self, structures):
        self.structures = structures
        self.names = {0: structures.intern('name', {'anonymous': True})}
        self.text = {0: ''}
        self.levels = {0: structures.intern('level', {'zero': True})}
        self.expressions = {}

    def expression(self, tag, data):
        """Remap every reference in one expression without expanding its DAG."""
        if tag in ('bvar', 'natVal', 'strVal'):
            return data
        if tag == 'sort':
            return self.levels[data]
        if tag == 'const':
            return dict(data, name=self.names[data['name']], us=[self.levels[u] for u in data['us']])
        if tag == 'app':
            return dict(data, fn=self.expressions[data['fn']], arg=self.expressions[data['arg']])
        if tag in ('lam', 'forallE', 'letE'):
            fields = dict(data, name=self.names[data['name']],
                          type=self.expressions[data['type']], body=self.expressions[data['body']])
            if tag == 'letE':
                fields['value'] = self.expressions[data['value']]
            return fields
        if tag == 'proj':
            return dict(data, typeName=self.names[data['typeName']], struct=self.expressions[data['struct']])
        raise ValueError(f'unsupported expression tag: {tag}')

    def declaration(self, tag, data):
        """Remap a complete declaration, retaining all other serialized fields."""
        fields = dict(data, name=self.names[data['name']],
                      levelParams=[self.names[n] for n in data['levelParams']],
                      type=self.expressions[data['type']])
        for key in ('value',):
            if key in data:
                fields[key] = self.expressions[data[key]]
        for key in ('induct',):
            if key in data:
                fields[key] = self.names[data[key]]
        for key in ('all', 'ctors'):
            if key in data:
                fields[key] = [self.names[n] for n in data[key]]
        if 'rules' in data:
            fields['rules'] = [dict(rule, ctor=self.names[rule['ctor']], rhs=self.expressions[rule['rhs']])
                               for rule in data['rules']]
        return tag, self.structures.freeze(fields)

    def read(self, path):
        """Read a bounded stream and return complete canonical declarations."""
        declarations = {}
        with path.open() as source:
            for line in source:
                record = json.loads(line)
                if 'meta' in record:
                    continue
                if 'in' in record:
                    tag = 'str' if 'str' in record else 'num'
                    data = record[tag]
                    fields = dict(data, pre=self.names[data['pre']])
                    self.names[record['in']] = self.structures.intern('name', {tag: fields})
                    prefix = self.text[data['pre']]
                    suffix = str(data.get('str', data.get('i')))
                    self.text[record['in']] = prefix + ('.' if prefix else '') + suffix
                elif 'il' in record:
                    tag, data = next((k, v) for k, v in record.items() if k != 'il')
                    fields = self.names[data] if tag == 'param' else (
                        [self.levels[n] for n in data] if tag in ('max', 'imax') else self.levels[data])
                    self.levels[record['il']] = self.structures.intern('level', {tag: fields})
                elif 'ie' in record:
                    tag, data = next((k, v) for k, v in record.items() if k != 'ie')
                    self.expressions[record['ie']] = self.structures.intern('expr', {tag: self.expression(tag, data)})
                else:
                    for tag, data in record.items():
                        if tag == 'inductive':
                            values = [(kind, item) for kind in ('types', 'ctors', 'recs') for item in data[kind]]
                        else:
                            values = [(tag, data)]
                        for kind, item in values:
                            name = self.names[item['name']]
                            if name in declarations:
                                raise ValueError(f'duplicate declaration in stream: {self.text[item["name"]]}')
                            declarations[name] = self.declaration(kind, item), self.text[item['name']]
        return declarations


def compare(left, right):
    """Require exact remapped records for the same complete declaration set."""
    structures = Structures()
    inventories = []
    for paths in (left, right):
        inventory = {}
        for path in paths:
            for name, value in Stream(structures).read(path).items():
                if name in inventory and inventory[name] != value:
                    raise ValueError(f'inconsistent repeated declaration: {value[1]}')
                inventory[name] = value
        inventories.append(inventory)
    a, b = inventories
    if set(a) != set(b):
        raise ValueError(f'declaration coverage differs: left-only {[a[n][1] for n in a.keys()-b.keys()]}; '
                         f'right-only {[b[n][1] for n in b.keys()-a.keys()]}')
    changed = [a[n][1] for n in a if a[n][0] != b[n][0]]
    if changed:
        raise ValueError(f'complete declaration records differ: {changed}')
    return len(a)


def main():
    """Compare explicit lists of reference and candidate fixture streams."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--reference', type=Path, nargs='+', required=True)
    parser.add_argument('--candidate', type=Path, nargs='+', required=True)
    args = parser.parse_args()
    print(f'complete remapped declarations agree: {compare(args.reference, args.candidate)}')


if __name__ == '__main__':
    main()
