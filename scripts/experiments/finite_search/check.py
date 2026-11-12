"""Check one finite-search proof in an explicit first-order fragment.

This experimental checker is independent of Lean and the certificate producer.
Free object variables have universal closure. Formula schemas belong to the
checker syntax: propositions, predicates, functions and types are not objects.
"""

import argparse
from collections import Counter
import json
from pathlib import Path


class Rejected(ValueError):
    """A malformed expression or invalid inference has been rejected."""


SIGNATURE = {
    'nil': ((), 'ListNat'),
    'cons': (('Nat', 'ListNat'), 'ListNat'),
    'none': ((), 'OptionNat'),
    'some': (('Nat',), 'OptionNat'),
    'true': ((), 'Bool'),
    'false': ((), 'Bool'),
    'test': (('Nat',), 'Bool'),
    'find': (('ListNat',), 'OptionNat'),
    'branch': (('Bool', 'OptionNat', 'OptionNat'), 'OptionNat'),
}


def require(condition, message):
    """Reject invalid input even when Python assertions are disabled."""
    if not condition:
        raise Rejected(message)


def freeze(value):
    """Give JSON expression arrays structural tuple identity."""
    return tuple(map(freeze, value)) if isinstance(value, list) else value


def substitute(value, variable, replacement):
    """Replace an object variable in the quantifier-free schema syntax."""
    if value == ('var', variable):
        return replacement
    if isinstance(value, tuple):
        return tuple(substitute(item, variable, replacement) for item in value)
    return value


def goal(values, target):
    """State membership and acceptance of this exact successful search result."""
    return ('imp', ('eq', ('find', values), ('some', target)),
            ('and', ('mem', target, values), ('eq', ('test', target), ('true',))))


class Checker:
    """Infer each proof node's conclusion using only the written rules."""

    def __init__(self):
        """Count only inference nodes visited by this checker instance."""
        self.rules = Counter()

    def term(self, value, variables):
        """Check a term's first-order arity and object sorts."""
        require(isinstance(value, tuple) and value, 'expected a term')
        symbol, *arguments = value
        require(isinstance(symbol, str), 'invalid term symbol')
        if symbol == 'var':
            require(len(arguments) == 1 and isinstance(arguments[0], str)
                    and arguments[0] in variables, 'unknown object variable')
            return variables[arguments[0]]
        require(symbol in SIGNATURE, 'unknown first-order symbol: ' + symbol)
        inputs, output = SIGNATURE[symbol]
        require(len(inputs) == len(arguments), 'wrong term arity')
        require(tuple(self.term(arg, variables) for arg in arguments) == inputs,
                'term sort mismatch')
        return output

    def formula(self, value, variables):
        """Check formulas built only from equality, membership and connectives."""
        require(isinstance(value, tuple) and value, 'expected a formula')
        if value[0] == 'eq' and len(value) == 3:
            require(self.term(value[1], variables) == self.term(value[2], variables),
                    'equality sort mismatch')
        elif value[0] == 'mem' and len(value) == 3:
            require(self.term(value[1], variables) == 'Nat'
                    and self.term(value[2], variables) == 'ListNat',
                    'membership sort mismatch')
        elif value[0] in ('and', 'imp') and len(value) == 3:
            self.formula(value[1], variables)
            self.formula(value[2], variables)
        else:
            require(value == ('falsehood',), 'unknown formula constructor')

    @staticmethod
    def fresh(name, existing):
        """Check an eigenvariable or assumption label before extending context."""
        require(isinstance(name, str) and name.isidentifier() and name not in existing,
                'context name is not fresh')

    @staticmethod
    def equality(value):
        """Require an equality premise and return its two endpoints."""
        require(len(value) == 3 and value[0] == 'eq', 'expected equality premise')
        return value[1:]

    def infer(self, node, variables, assumptions):
        """Check a finite derivation, including induction and case side conditions."""
        require(isinstance(node, dict) and isinstance(node.get('rule'), str),
                'expected a proof node')
        rule = node['rule']
        shapes = {
            'assume': 'name', 'refl': 'term', 'sym': 'proof',
            'trans': 'left right', 'cong': 'symbol arguments', 'definition': 'term',
            'imp_intro': 'name premise body', 'imp_elim': 'function argument',
            'and_intro': 'left right', 'and_left': 'proof', 'and_right': 'proof',
            'member_head': 'head tail', 'member_tail': 'head proof',
            'some_injective': 'proof', 'constructor_clash': 'proof',
            'false_elim': 'proof conclusion',
            'substitute': 'equality variable template proof',
            'bool_cases': 'term true_name true false_name false',
            'list_induction': 'subject variable head tail hypothesis schema base step',
        }
        require(rule in shapes, 'unknown inference rule: ' + rule)
        require(set(node) == {'rule', *shapes[rule].split()}, 'wrong proof fields')
        self.rules[rule] += 1
        infer = lambda key: self.infer(node[key], variables, assumptions)
        expr = lambda key: freeze(node[key])

        if rule == 'assume':
            require(isinstance(node['name'], str) and node['name'] in assumptions,
                    'unknown assumption')
            result = assumptions[node['name']]
        elif rule == 'refl':
            value = expr('term')
            self.term(value, variables)
            result = ('eq', value, value)
        elif rule == 'sym':
            left, right = self.equality(infer('proof'))
            result = ('eq', right, left)
        elif rule == 'trans':
            left, middle = self.equality(infer('left'))
            other, right = self.equality(infer('right'))
            require(middle == other, 'equality endpoints do not compose')
            result = ('eq', left, right)
        elif rule == 'cong':
            require(isinstance(node['symbol'], str) and node['symbol'] in SIGNATURE
                    and isinstance(node['arguments'], list), 'invalid congruence')
            pairs = [self.equality(self.infer(arg, variables, assumptions))
                     for arg in node['arguments']]
            left = (node['symbol'], *(pair[0] for pair in pairs))
            right = (node['symbol'], *(pair[1] for pair in pairs))
            self.term(left, variables)
            self.term(right, variables)
            result = ('eq', left, right)
        elif rule == 'definition':
            value = expr('term')
            self.term(value, variables)
            if value == ('find', ('nil',)):
                reduced = ('none',)
            elif value[0] == 'find' and value[1][0] == 'cons':
                _, head, tail = value[1]
                reduced = ('branch', ('test', head), ('some', head), ('find', tail))
            elif value[0] == 'branch' and value[1] in (('true',), ('false',)):
                reduced = value[2] if value[1] == ('true',) else value[3]
            else:
                raise Rejected('no defining equation applies')
            result = ('eq', value, reduced)
        elif rule == 'imp_intro':
            self.fresh(node['name'], assumptions)
            premise = expr('premise')
            self.formula(premise, variables)
            body = self.infer(node['body'], variables, {**assumptions, node['name']: premise})
            result = ('imp', premise, body)
        elif rule == 'imp_elim':
            function, argument = infer('function'), infer('argument')
            require(function[0] == 'imp' and function[1] == argument,
                    'implication premise mismatch')
            result = function[2]
        elif rule == 'and_intro':
            result = ('and', infer('left'), infer('right'))
        elif rule in ('and_left', 'and_right'):
            both = infer('proof')
            require(both[0] == 'and', 'expected conjunction premise')
            result = both[1 if rule == 'and_left' else 2]
        elif rule == 'member_head':
            head, tail = expr('head'), expr('tail')
            result = ('mem', head, ('cons', head, tail))
        elif rule == 'member_tail':
            member = infer('proof')
            require(member[0] == 'mem', 'expected membership premise')
            result = ('mem', member[1], ('cons', expr('head'), member[2]))
        elif rule == 'some_injective':
            left, right = self.equality(infer('proof'))
            require(left[0] == right[0] == 'some', 'expected two some constructors')
            result = ('eq', left[1], right[1])
        elif rule == 'constructor_clash':
            left, right = self.equality(infer('proof'))
            require({left[0], right[0]} == {'none', 'some'}, 'no constructor clash')
            result = ('falsehood',)
        elif rule == 'false_elim':
            require(infer('proof') == ('falsehood',), 'expected falsehood premise')
            result = expr('conclusion')
        elif rule == 'substitute':
            left, right = self.equality(infer('equality'))
            name, template = node['variable'], expr('template')
            self.fresh(name, variables)
            self.formula(template, {**variables, name: self.term(left, variables)})
            require(infer('proof') == substitute(template, name, left),
                    'substitution premise mismatch')
            result = substitute(template, name, right)
        elif rule == 'bool_cases':
            value = expr('term')
            require(self.term(value, variables) == 'Bool', 'case subject is not Boolean')
            self.fresh(node['true_name'], assumptions)
            self.fresh(node['false_name'], {**assumptions, node['true_name']: None})
            positive = self.infer(node['true'], variables,
                                  {**assumptions, node['true_name']: ('eq', value, ('true',))})
            negative = self.infer(node['false'], variables,
                                  {**assumptions, node['false_name']: ('eq', value, ('false',))})
            require(positive == negative, 'case conclusions differ')
            result = positive
        elif rule == 'list_induction':
            subject, schema = expr('subject'), expr('schema')
            require(self.term(subject, variables) == 'ListNat', 'induction subject is not a list')
            variable, head, tail = node['variable'], node['head'], node['tail']
            self.fresh(variable, variables)
            self.fresh(head, {**variables, variable: None})
            self.fresh(tail, {**variables, variable: None, head: None})
            self.fresh(node['hypothesis'], assumptions)
            self.formula(schema, {**variables, variable: 'ListNat'})
            require(infer('base') == substitute(schema, variable, ('nil',)),
                    'induction base mismatch')
            step = self.infer(node['step'], {**variables, head: 'Nat', tail: 'ListNat'},
                              {**assumptions, node['hypothesis']:
                               substitute(schema, variable, ('var', tail))})
            require(step == substitute(schema, variable, ('cons', ('var', head), ('var', tail))),
                    'induction step mismatch')
            result = substitute(schema, variable, subject)
        self.formula(result, variables)
        return result

    def certificate(self, document):
        """Require a closed proof of the fixed search claim for arbitrary input data."""
        require(isinstance(document, dict) and set(document) == {'schema', 'claim', 'proof'}
                and type(document['schema']) is int and document['schema'] == 1,
                'invalid certificate envelope')
        variables = {'xs': 'ListNat', 'target': 'Nat'}
        expected = goal(('var', 'xs'), ('var', 'target'))
        require(freeze(document['claim']) == expected, 'certificate claims a different theorem')
        conclusion = self.infer(document['proof'], variables, {})
        require(conclusion == expected, 'proof concludes a different theorem')
        return {'checked_nodes': sum(self.rules.values()), 'rules': dict(sorted(self.rules.items()))}


def main():
    """Check a supplied certificate without invoking its producer or Lean."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('certificate', type=Path)
    args = parser.parse_args()
    try:
        result = Checker().certificate(json.loads(args.certificate.read_text()))
    except (Rejected, OSError, json.JSONDecodeError) as error:
        parser.exit(1, 'rejected: ' + str(error) + '\n')
    print(json.dumps(result, sort_keys=True))


if __name__ == '__main__':
    main()
