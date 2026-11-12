"""Exercise accepted derivations and invalid rules in the finite-search pilot."""

import copy
import json
from pathlib import Path
import subprocess
import sys
import unittest

from scripts.experiments.finite_search.check import Checker, Rejected, goal
from scripts.experiments.finite_search.produce import certificate, serialized
from scripts.experiments.finite_search.lean_claim import Export, PREFIX
from scripts.paths import ROOT


class FiniteSearchTests(unittest.TestCase):
    """Check complete proofs, object sorts and inference side conditions."""

    def assert_rejected(self, document):
        """Require an actual invalid-proof rejection rather than another exception."""
        with self.assertRaises(Rejected):
            Checker().certificate(document)

    def test_uniform_proof_and_retained_artifact(self):
        document = certificate()
        result = Checker().certificate(document)
        self.assertEqual(result['rules']['list_induction'], 1)
        self.assertEqual(result['rules']['bool_cases'], 1)
        self.assertGreater(result['checked_nodes'], 50)
        path = ROOT / 'docs/foundations/finite-search.certificate.json'
        self.assertEqual(path.read_text(), serialized())
        self.assertEqual(Checker().certificate(json.loads(path.read_text())), result)

    def test_weaker_claim_is_rejected(self):
        document = certificate()
        document['claim'] = ('eq', ('true',), ('true',))
        self.assert_rejected(document)

    def test_distinct_certificates_need_no_proof_identity_rule(self):
        document = certificate()
        alternate = copy.deepcopy(document)
        alternate['proof'] = {
            'rule': 'substitute',
            'equality': {'rule': 'refl', 'term': ('var', 'xs')},
            'variable': 'original',
            'template': goal(('var', 'original'), ('var', 'target')),
            'proof': alternate['proof'],
        }
        self.assertNotEqual(document, alternate)
        first = Checker().certificate(document)
        second = Checker().certificate(alternate)
        self.assertEqual(second['checked_nodes'], first['checked_nodes'] + 2)

    def test_falsehood_cannot_be_assumed(self):
        document = certificate()
        document['proof'] = {'rule': 'assume', 'name': 'falsehood'}
        self.assert_rejected(document)

    def test_unsupported_postulate_is_rejected(self):
        document = certificate()
        document['proof'] = {'rule': 'axiom', 'name': 'search_is_correct'}
        self.assert_rejected(document)

    def test_propositions_and_types_are_not_object_sorts(self):
        checker = Checker()
        for malformed in [('forall_prop', 'p', ('falsehood',)),
                          ('eq', ('Prop',), ('Prop',)),
                          ('eq', ('Type',), ('Type',)),
                          ('eq', ('apply', ('var', 'target'), ('true',)), ('true',))]:
            with self.subTest(malformed=malformed), self.assertRaises(Rejected):
                checker.formula(malformed, {'target': 'Nat'})

    def test_induction_cannot_reuse_outer_variable_as_head(self):
        document = certificate()
        document['proof']['head'] = 'target'
        self.assert_rejected(document)

    def test_induction_schema_cannot_depend_on_step_eigenvariable(self):
        document = certificate()
        document['proof']['schema'] = goal(('var', 'items'), ('var', 'head'))
        self.assert_rejected(document)

    def test_missing_induction_base_is_rejected(self):
        document = certificate()
        document['proof']['base'] = {'rule': 'assume', 'name': 'induction'}
        self.assert_rejected(document)

    def test_induction_does_not_assume_its_conclusion(self):
        document = certificate()
        document['proof']['step'] = {'rule': 'assume', 'name': 'induction'}
        self.assert_rejected(document)

    def test_boolean_cases_require_both_branches(self):
        document = certificate()
        del document['proof']['step']['body']['false']
        self.assert_rejected(document)

    def test_boolean_case_assumptions_cannot_leak(self):
        document = certificate()
        document['proof']['step']['body']['false'] = copy.deepcopy(
            document['proof']['step']['body']['true'])
        self.assert_rejected(document)

    def test_wrong_input_owner_is_rejected(self):
        document = certificate()
        document['proof']['subject'] = ('nil',)
        self.assert_rejected(document)

    def test_substitution_cannot_capture_outer_object(self):
        document = certificate()
        substitution = document['proof']['step']['body']['true']['left']
        substitution['variable'] = 'target'
        self.assert_rejected(document)

    def test_object_sort_mismatch_is_rejected(self):
        document = certificate()
        document['proof']['subject'] = ('true',)
        self.assert_rejected(document)

    def test_equation_requires_composing_endpoints(self):
        document = certificate()
        equation = document['proof']['base']['body']['proof']['proof']
        equation['left'] = {'rule': 'refl', 'term': ('true',)}
        self.assert_rejected(document)

    def test_constructor_clash_requires_distinct_constructors(self):
        node = {'rule': 'constructor_clash', 'proof': {'rule': 'refl', 'term': ('none',)}}
        with self.assertRaises(Rejected):
            Checker().infer(node, {}, {})

    def test_substitution_requires_evidence_for_the_original_formula(self):
        document = certificate()
        document['proof']['step']['body']['true']['left']['proof'] = {
            'rule': 'member_head', 'head': ('var', 'target'), 'tail': ('var', 'tail')}
        self.assert_rejected(document)

    def test_zero_length_list_is_not_a_success(self):
        document = certificate()
        document['proof']['base']['body'] = {
            'rule': 'and_intro',
            'left': {'rule': 'member_head', 'head': ('var', 'target'), 'tail': ('nil',)},
            'right': {'rule': 'refl', 'term': ('true',)}}
        self.assert_rejected(document)

    def test_cli_does_not_import_its_producer(self):
        """The checker runs by file path with only its own directory on sys.path."""
        script = ROOT / 'scripts/experiments/finite_search/check.py'
        result = subprocess.run([sys.executable, '-I', str(script),
                                 str(ROOT / 'docs/foundations/finite-search.certificate.json')],
                                cwd=Path('/tmp'), capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertGreater(json.loads(result.stdout)['checked_nodes'], 50)


class LeanClaimTests(unittest.TestCase):
    """Check the concrete claim projection without importing or executing Lean."""

    def fixture(self):
        """Build a small explicit expression graph for the actual bridge signature."""
        export = Export.__new__(Export)
        export.names, export.expressions, export.declarations = {}, {}, {}

        def expression(tag, data):
            index = len(export.expressions)
            export.expressions[index] = {tag: data}
            return index

        def constant(name):
            index = len(export.names)
            export.names[index] = name
            return expression('const', {'name': index, 'us': []})

        def application(name, *arguments):
            index = constant(name)
            for argument in arguments:
                index = expression('app', {'fn': index, 'arg': argument})
            return index

        nat, boolean = constant('Nat'), constant('Bool')
        list_nat, option_nat = application('List', nat), application('Option', nat)
        zero, one, two = (expression('bvar', index) for index in range(3))
        selected_body = application('List.find?', nat, constant(PREFIX + 'accepts'), zero)
        export.declarations[PREFIX + 'selected'] = ('def', {
            'value': expression('lam', {'type': list_nat, 'body': selected_body})})
        found = application('Eq', option_nat, application(PREFIX + 'selected', one),
                            application('Option.some', nat, zero))
        member = application('Membership.mem', nat, list_nat,
                             application('List.instMembership', nat), two, one)
        accepted = application('Eq', boolean, application(PREFIX + 'accepts', one), constant('Bool.true'))
        conclusion = application('And', member, accepted)
        body = expression('forallE', {'type': found, 'body': conclusion})
        body = expression('forallE', {'type': nat, 'body': body})
        body = expression('forallE', {'type': list_nat, 'body': body})
        export.declarations[PREFIX + 'selected_sound'] = ('thm', {'type': body})
        return export, {'algorithm': selected_body, 'member': member, 'accepted': accepted,
                        'conclusion': conclusion, 'statement': body, 'zero': zero, 'one': one}

    def test_exact_claim_and_algorithm_are_recognized(self):
        export, _ = self.fixture()
        self.assertEqual(export.claim(), goal(('var', 'xs'), ('var', 'target')))

    def test_replaced_algorithm_is_rejected(self):
        export, keys = self.fixture()
        export.expressions[keys['algorithm']] = {'bvar': 0}
        with self.assertRaises(Rejected):
            export.claim()

    def test_changed_input_carrier_is_rejected(self):
        export, keys = self.fixture()
        export.expressions[keys['statement']]['forallE']['type'] = keys['zero']
        with self.assertRaises(Rejected):
            export.claim()

    def test_weaker_conclusion_is_rejected(self):
        export, keys = self.fixture()
        export.expressions[keys['conclusion']] = copy.deepcopy(export.expressions[keys['accepted']])
        with self.assertRaises(Rejected):
            export.claim()

    def test_input_owner_and_target_cannot_be_swapped(self):
        export, keys = self.fixture()
        export.expressions[keys['member']]['app']['arg'] = keys['zero']
        with self.assertRaises(Rejected):
            export.claim()

    def test_source_proof_argument_cannot_become_object_data(self):
        export, keys = self.fixture()
        export.expressions[keys['accepted']]['app']['arg'] = keys['zero']
        with self.assertRaises(Rejected):
            export.claim()

    def test_axiom_cannot_replace_source_theorem(self):
        export, _ = self.fixture()
        _, declaration = export.declarations[PREFIX + 'selected_sound']
        export.declarations[PREFIX + 'selected_sound'] = ('axiom', declaration)
        with self.assertRaises(Rejected):
            export.claim()


if __name__ == '__main__':
    unittest.main()
