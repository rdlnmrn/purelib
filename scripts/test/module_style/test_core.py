#!/usr/bin/env python3
"""Check reviewed edits preserve Lean syntax identities and reject stale plans."""
import copy
import unittest
from scripts.module_style import core as style

SOURCE = '''module
public import Alpha -- retained import comment
public import Beta

namespace Example
/-! Mention Alpha.API.value without changing the prose. -/
/-- Existing documentation. -/
@[simp]
def result : Nat := Alpha.API.value + Alpha.API.value

def label := { Alpha.API.value := Alpha.API.value }
def literal := "Alpha.API.value"
def raw := r#"Alpha.API.value"#
-- Alpha.API.value
/- outer /- Alpha.API.value -/ comment -/
end Example
'''


def plan(text=SOURCE):
    return {'schema': 1, 'path': 'Test/Example.lean', 'source_sha256': style.digest(text),
            'imports': [{'module': 'Alpha', 'mode': 'import', 'reason': 'Implementation dependency.'},
                        {'module': 'Beta', 'mode': 'public import', 'reason': 'Deliberate API facade.'}],
            'opens': [{'namespace': 'Alpha.API', 'names': ['value'], 'scope': 'file', 'reason': 'Scalar readback.'}],
            'rewrites': [{'from': 'Alpha.API.value', 'to': 'value', 'scope': 'file', 'count': 3, 'reason': 'Selective opening.'}],
            'docstrings': {'Example.result': 'The sum of two scalar readbacks.\n\nBoth terms use the same retained value.',
                           'Example.label': 'Package the scalar readback.'},
            'review': 'Test fixture.'}


class EditingTests(unittest.TestCase):
    def test_type_rhs_quantified_have_and_nested_header_lets(self):
        source = '''module
import Alpha
theorem quantified : True := by
  have ordinary : ∀ vector : Vector Nat,
      cross vector axis = Alpha.API.zero := by
    exact proof
  exact finish ordinary
theorem translated :
    let translated := convert Alpha.API.input
    let ball := map translated
    precision ball < Alpha.API.target :=
  retainedProof
'''
        selected = {t.text for t in style.lex(source)
                    if t.start in style.type_rhs_identifiers(source, style.lex(source))}
        self.assertEqual(selected, {'Alpha.API.zero', 'Alpha.API.target'})
        request = plan(source)
        request.update(imports=[dict(module='Alpha', mode='import', reason='Fixture.')],
                       opens=[], docstrings={}, rewrites=[
                           dict(**{'from': name, 'to': name.removeprefix('Alpha.')},
                                scope='file', count=1, reason='Reviewed type endpoint.')
                           for name in ('Alpha.API.zero', 'Alpha.API.target')])
        with self.assertRaisesRegex(ValueError, 'found 0'):
            style.prepare(request, source)
        request['rewrite_type_rhs'] = True
        prepared, result = style.prepare(request, source)
        self.assertIn('cross vector axis = API.zero := by', result)
        self.assertIn('precision ball < API.target :=', result)
        self.assertEqual(style.apply_plan(prepared, result), result)
        self.assertEqual(style.recover_original(prepared, result), source)

    def test_type_rhs_preserves_header_let_names_and_nested_labels(self):
        source = '''module
theorem sample :
    let Alpha.API.local := { Alpha.API.field := by exact value }
    let second := f (Alpha.API.argument := by exact value)
    (fun x => x) second ≤ Alpha.API.endpoint := by
  have relation : ∀ x : Nat,
      f (Alpha.API.haveArgument := by exact value) x = Alpha.API.haveEndpoint := by
    let Alpha.API.proofLocal := value
    exact proof
  have Alpha.API.untyped := by exact proof
  exact finish
'''
        tokens = style.lex(source)
        selected = {t.text for t in tokens if t.start in style.type_rhs_identifiers(source, tokens)}
        self.assertEqual(selected, {'Alpha.API.endpoint', 'Alpha.API.haveEndpoint'})
        labels = style.assignment_labels(source, tokens, rewrite_type_rhs=True)
        protected = {t.text for t in tokens if t.start in labels}
        self.assertTrue({'Alpha.API.local', 'Alpha.API.field', 'Alpha.API.argument',
                         'Alpha.API.haveArgument', 'Alpha.API.proofLocal', 'Alpha.API.untyped'} <= protected)

    def test_type_rhs_rejects_untyped_bindings_quotes_and_unsupported_lets(self):
        sources = [
            'theorem sample : True := by\n  have Alpha.API.value := by exact proof\n  exact proof\n',
            'theorem sample : True := by\n  let Alpha.API.value := by exact proof\n  exact proof\n',
            'theorem sample : True := by\n  exact `(tactic|\n    have named : ∀ x, x = Alpha.API.value := by exact proof)\n',
            'theorem sample : True := by\n  have named : ∀ x, x = `Alpha.API.value := by exact proof\n',
            'theorem sample : let x := 1; x = Alpha.API.value := by exact proof\n',
            'theorem sample :\n    let x := f (Alpha.API.value := by exact proof)\n    True := by exact proof\n',
            'theorem sample : True := by\n  exact { Alpha.API.value := by exact proof }\n',
            'theorem sample : True := by\n  exact "have x : ∀ y, y = Alpha.API.value := proof"\n',
        ]
        for source in sources:
            with self.subTest(source=source):
                text = 'module\n' + source
                tokens = style.lex(text)
                selected = {t.text for t in tokens if t.start in style.type_rhs_identifiers(text, tokens)}
                self.assertNotIn('Alpha.API.value', selected)

    def test_signature_rhs_is_opt_in_and_preserves_nested_assignments(self):
        source = '''module
import Alpha
theorem sample :
    left = by
      letI : DecidableEq Nat := inferInstance
      let record := { Alpha.API.field := by exact value }
      have localProof : True := by
        exact f (Alpha.API.argument := by exact value)
      exact f record fun value => value ≠ Alpha.API.zero := by
  exact finish
'''
        tokens = style.lex(source)
        selected = {t.text for t in tokens if t.start in style.type_rhs_identifiers(source, tokens)}
        self.assertEqual(selected, {'Alpha.API.zero'})
        request = plan(source)
        request.update(imports=[dict(module='Alpha', mode='import', reason='Fixture.')],
                       opens=[], docstrings={}, rewrites=[dict(**{'from': 'Alpha.API.zero', 'to': 'API.zero'},
                           scope='sample', count=1, reason='Header exact term, not a field label.')])
        with self.assertRaisesRegex(ValueError, 'found 0'):
            style.prepare(request, source)
        request['rewrite_type_rhs'] = True
        prepared, result = style.prepare(request, source)
        self.assertIn('value ≠ API.zero := by', result)
        self.assertIn('Alpha.API.field := by', result)
        self.assertIn('Alpha.API.argument := by', result)
        self.assertEqual(style.apply_plan(prepared, result), result)
        self.assertEqual(style.recover_original(prepared, result), source)
        request['rewrite_type_rhs'] = 'yes'
        with self.assertRaisesRegex(ValueError, 'rewrite_type_rhs: expected a boolean'):
            style.prepare(request, source)

    def test_signature_rhs_rejects_proof_bodies_local_bindings_and_quotations(self):
        sources = [
            'theorem sample : True := by\n  exact Alpha.API.zero := by\n exact proof\n',
            'theorem sample : left = by\n    let Alpha.API.zero := by\n      exact value\n    exact other := by\n  exact proof\n',
            'theorem sample : left = by\n    have local : True := by\n      exact Alpha.API.zero := by\n    exact proof\n',
            'theorem sample : left = by\n    exact f (Alpha.API.zero := by\n      exact value) := by\n  exact proof\n',
            'theorem sample : left = by\n    exact { Alpha.API.zero := by\n      exact value } := by\n  exact proof\n',
            'theorem sample : left = by\n    exact `Alpha.API.zero := by\n  exact proof\n',
            'theorem sample : left = by\n    exact `(term| { Alpha.API.zero := by exact value }) := by\n  exact proof\n',
            'theorem sample : left = by\n    exact let Alpha.API.zero := by\n      exact value\n    other := by\n  exact proof\n',
            'theorem sample : left = by\n    exact have Alpha.API.zero := by\n      exact value\n    other := by\n  exact proof\n',
            'def sample := "theorem fake : left = by\\n exact Alpha.API.zero := by"\n',
        ]
        for source in sources:
            with self.subTest(source=source):
                text = 'module\n' + source
                tokens = style.lex(text)
                selected = {t.text for t in tokens if t.start in style.type_rhs_identifiers(text, tokens)}
                self.assertNotIn('Alpha.API.zero', selected)

    def test_calc_rhs_is_opt_in_and_idempotent(self):
        source = '''module
import Alpha
theorem sample : True := by
  have bound := calc
    first = Alpha.API.value := firstProof
    _ ≤ Alpha.API.value := secondProof
    _ < Alpha.API.value := thirdProof
  exact finish bound
'''
        request = plan(source)
        request.update(imports=[dict(module='Alpha', mode='import', reason='Fixture.')],
                       opens=[], docstrings={}, rewrites=[])
        old, unchanged = style.prepare(request, source)
        self.assertEqual(unchanged, source)
        request['rewrites'] = [dict(**{'from': 'Alpha.API.value', 'to': 'API.value'},
                                   scope='sample', count=3, reason='Reviewed calc constants.')]
        with self.assertRaisesRegex(ValueError, 'found 0'):
            style.prepare(request, source)
        request['rewrite_calc_rhs'] = False
        with self.assertRaisesRegex(ValueError, 'found 0'):
            style.prepare(request, source)
        request['rewrite_calc_rhs'] = True
        prepared, result = style.prepare(request, source)
        self.assertEqual(result.count('API.value := '), 3)
        self.assertNotIn('Alpha.API.value', result)
        self.assertEqual(style.apply_plan(prepared, result), result)
        self.assertEqual(style.recover_original(prepared, result), source)
        self.assertEqual(style.apply_plan(old, source), source)
        for invalid in (0, 1, 'yes', None):
            request['rewrite_calc_rhs'] = invalid
            with self.assertRaisesRegex(ValueError, 'rewrite_calc_rhs: expected a boolean'):
                style.prepare(request, source)

    def test_calc_rhs_preserves_nested_record_and_named_argument_labels(self):
        source = '''module
def sample := by
  have result := calc
    (make (Alpha.API.named := 1)) =
        { Alpha.API.field := 1, other := (f (Alpha.API.nested := 2)) } := by
      let held := { Alpha.API.proofField := 3 }
      exact proof held
    _ = f (Alpha.API.argument := 4) Alpha.API.finish := by
      exact proof
  let after := { Alpha.API.after := 5 }
  exact after
'''
        tokens = style.lex(source)
        labels = style.assignment_labels(source, tokens, rewrite_calc_rhs=True)
        found = {t.text for t in tokens if t.start in labels}
        self.assertTrue({'Alpha.API.named', 'Alpha.API.field', 'Alpha.API.nested',
                         'Alpha.API.proofField', 'Alpha.API.argument', 'Alpha.API.after'} <= found)
        self.assertNotIn('Alpha.API.finish', found)

    def test_calc_rhs_multiline_nested_calcs_comments_and_quotes(self):
        source = '''module
def sample := by
  have result := calc
    first =
      Alpha.API.first /- := { Fake.label := } -/ := by
        have nested := calc
          a ≥ Alpha.API.inner := innerProof
          _ > Alpha.API.last := lastProof
        exact nested
    _ ≠ Alpha.API.outer := outerProof
  let quoted := `Alpha.API.quoted
  let literal := "calc first = Alpha.API.string := proof"
  let escaped := «calc =»
  exact result
'''
        tokens = style.lex(source)
        selected = {t.text for t in tokens if t.start in style.calc_rhs_identifiers(source, tokens)}
        self.assertEqual(selected, {'Alpha.API.first', 'Alpha.API.inner', 'Alpha.API.last', 'Alpha.API.outer'})
        quoted = 'module\ndef sample := calc first = `Alpha.API.quoted := proof\n'
        self.assertEqual(style.calc_rhs_identifiers(quoted, style.lex(quoted)), set())

    def test_calc_rhs_does_not_escape_into_proofs_or_following_commands(self):
        source = '''module
def sample := by
  have relation := calc
    first = Alpha.API.value := by
      let Alpha.API.local := 1
      have proposition : first = Alpha.API.type := proof
      exact proposition
  let Alpha.API.after := 2
  exact relation
def later := { Alpha.API.field := 3 }
'''
        tokens = style.lex(source)
        labels = style.assignment_labels(source, tokens, rewrite_calc_rhs=True)
        found = {t.text for t in tokens if t.start in labels}
        self.assertTrue({'Alpha.API.local', 'Alpha.API.after', 'Alpha.API.field'} <= found)
        self.assertNotIn('Alpha.API.value', found)
        self.assertNotIn('Alpha.API.type', found)  # Existing explicit annotation behavior.
        ordinary = 'module\ndef f := { Alpha.API.field := 1 }\ndef g := f (Alpha.API.arg := 2)\n'
        self.assertEqual(style.assignment_labels(ordinary, style.lex(ordinary)),
                         style.assignment_labels(ordinary, style.lex(ordinary), rewrite_calc_rhs=True))

    def test_calc_rhs_unknown_control_forms_remain_protected(self):
        for body in ('calc if test then left else Alpha.API.value := proof',
                     'calc show left = Alpha.API.value := proof',
                     'calc first = let x := 1; Alpha.API.value := proof',
                     'calc first = (make (Alpha.API.value := proof))',
                     '`calc\nAlpha.API.value := proof'):
            source = 'module\ndef sample := ' + body + '\n'
            with self.subTest(body=body):
                self.assertEqual(style.calc_rhs_identifiers(source, style.lex(source)), set())

    def test_explicit_whitespace_cleanup_preserves_literals_and_lineage(self):
        source = 'module\nimport Alpha\ndef value := 1  \n/-- Retained comment.  \nMore. -/\ndef text := "literal  \ntext"  \n'
        request = plan(source)
        request.update(imports=[dict(module='Alpha', mode='import', reason='Fixture.')],
                       opens=[], rewrites=[], docstrings={}, trim_trailing_whitespace=True)
        prepared, result = style.prepare(request, source)
        self.assertIn('def value := 1\n', result)
        self.assertIn('Retained comment.  \n', result)
        self.assertIn('"literal  \ntext"\n', result)
        self.assertEqual(style.apply_plan(prepared, result), result)
        self.assertEqual(style.recover_original(prepared, result), source)
        request['trim_trailing_whitespace'] = 'yes'
        with self.assertRaisesRegex(ValueError, 'expected a boolean'):
            style.prepare(request, source)

    def test_manifest_defers_explicit_generated_example(self):
        from pathlib import Path
        from scripts.module_style import manifest as manifest
        source = "module\n-- This file is generated by scripts/example-generator.py.\n"
        self.assertEqual(manifest.classify(Path('Purelib/Examples/Example.lean'), source, set())[0], 'deferred-generated')
        self.assertEqual(manifest.classify(Path('Test/Certificate.lean'), source, set())[0], 'authored')

    def test_tactic_import_repair_extends_applied_plan_from_original(self):
        from pathlib import Path
        from scripts.module_style import import_repairs as repairs
        source = 'module\nimport Alpha\ndef proof : True := by omega; omega0\n'
        prior = plan(source)
        prior.update(imports=[dict(module='Alpha', mode='import', reason='Original dependency.'),
                              dict(module='Beta', mode='import', reason='Retained earlier repair.')],
                     opens=[], rewrites=[], docstrings={})
        prior, applied = style.prepare(prior, source)
        repaired = repairs.prepare_repair('Test/Example.lean', applied, prior)
        self.assertEqual(repaired['source_sha256'], style.digest(source))
        self.assertEqual(repaired['imports'][:2], prior['imports'])
        self.assertEqual([r['module'] for r in repaired['imports']].count('Purelib.Tactic.QuotientFreeOmega'), 1)
        result = style.apply_plan(repaired, source)
        self.assertIsNone(repairs.prepare_repair('Test/Example.lean', result, repaired))
        self.assertIsNone(repairs.prepare_repair('Test/Example.lean', source, repaired))
        self.assertIsNone(repairs.prepare_repair('Test/Example.lean', applied, repaired, prior))
        import tempfile
        with tempfile.TemporaryDirectory() as temporary:
            retained = repairs.retain_previous(Path(temporary), prior)
            self.assertEqual(style.read_json(retained), prior)
            self.assertEqual(repairs.retain_previous(Path(temporary), prior), retained)
            changed = copy.deepcopy(prior)
            changed['review'] = 'Changed instruction'
            with self.assertRaisesRegex(ValueError, 'history conflicts'):
                repairs.retain_previous(Path(temporary), changed)
        with self.assertRaisesRegex(ValueError, 'source is not the prior plan result'):
            repairs.prepare_repair('Test/Example.lean', applied + '-- changed\n', prior)
        self.assertIsNone(repairs.prepare_repair('Test/Quoted.lean', 'module\n-- omega\ndef s := "omega0"\n'))

    def test_explicit_declaration_rename_preserves_body_and_docs(self):
        source = 'module\nnamespace Example\n/-- A recursive constant. -/\ndef old : Nat → Nat\n  | 0 => 0\n  | n + 1 => Example.old n\nend Example\n'
        p = plan(source)
        p.update(imports=[], opens=[], docstrings={},
                 declaration_renames=[dict(**{'from': 'Example.old', 'to': 'Example.New.old'}, reason='Authorized owner rename.')],
                 rewrites=[dict(**{'from': 'Example.old', 'to': 'Example.New.old'}, scope='file', count=1, reason='Migrate the recursive reference.')])
        prepared, result = style.prepare(p, source)
        self.assertIn('def _root_.Example.New.old : Nat', result)
        self.assertIn('| n + 1 => Example.New.old n', result)
        self.assertIn('/-- A recursive constant. -/', result)
        self.assertEqual(style.apply_plan(prepared, result), result)

    def test_declaration_rename_rejects_collisions_and_missing_sources(self):
        p = plan()
        p['declaration_renames'] = [dict(**{'from': 'Example.result', 'to': 'Example.label'}, reason='Invalid collision.')]
        with self.assertRaisesRegex(ValueError, 'target already exists'):
            style.prepare(p, SOURCE)
        p['declaration_renames'][0]['from'] = 'Example.missing'
        with self.assertRaisesRegex(ValueError, 'unknown declaration rename source'):
            style.prepare(p, SOURCE)

    def test_equation_branch_let_is_not_a_declaration_body(self):
        source = 'module\nimport Alpha\ndef f : Nat → Nat\n  | 0 => 0\n  | n + 1 =>\n    let a := Alpha.value\n    a + Alpha.value\n'
        p = plan(source)
        p.update(imports=[p['imports'][0]], docstrings={},
                 opens=[dict(namespace='Alpha', names=['value'], scope='proof:f', reason='Test scoped helper.')],
                 rewrites=[])
        with self.assertRaisesRegex(ValueError, 'equation clauses'):
            style.prepare(p, source)

    def test_checked_prior_plan_composition(self):
        prior = plan()
        prior.update(opens=[], rewrites=[], docstrings={})
        prior, intermediate = style.prepare(prior, SOURCE)
        final, expected = style.prepare(plan(), SOURCE)
        original = style.reviewed_input(final, intermediate, prior)
        self.assertEqual(style.apply_plan(final, original), expected)
        self.assertEqual(style.reviewed_input(final, expected, prior), expected)
        with self.assertRaises(ValueError):
            style.reviewed_input(final, intermediate + '-- unrelated change\n', prior)
        unrelated = copy.deepcopy(prior)
        unrelated['path'] = 'Test/Other.lean'
        with self.assertRaisesRegex(ValueError, 'same file'):
            style.reviewed_input(final, intermediate, unrelated)

    def test_documentation_gate_includes_members(self):
        source = 'module\n/-- A point. -/\nstructure Point where\n  coordinate : Nat\n'
        with self.assertRaisesRegex(ValueError, 'Point.coordinate'):
            style.require_documentation(source)
        style.require_documentation(source.replace('  coordinate', '  /-- The natural coordinate. -/ coordinate'))

    def test_identity_and_idempotence(self):
        prepared, result = style.prepare(plan(), SOURCE)
        self.assertIn('import Alpha -- retained import comment', result)
        self.assertIn('public import Beta', result)
        self.assertIn('def result : Nat := value + value', result)
        self.assertIn('{ Alpha.API.value := value }', result)
        self.assertIn('"Alpha.API.value"', result)
        self.assertIn('r#"Alpha.API.value"#', result)
        self.assertIn('/- outer /- Alpha.API.value -/ comment -/', result)
        self.assertIn('value. -/\n@[simp]\ndef result', result)
        self.assertEqual(style.apply_plan(prepared, SOURCE), result)
        self.assertEqual(style.apply_plan(prepared, result), result)

    def test_preserve_declaration_and_quoted_names(self):
        text = SOURCE.replace('def result', 'def _root_.Alpha.API.value').replace('def literal :=', 'def literal :=')
        p = plan(text)
        p['docstrings'] = {}
        prepared, result = style.prepare(p, text)
        self.assertIn('def _root_.Alpha.API.value', result)
        self.assertEqual(style.apply_plan(prepared, result), result)

    def test_return_and_default_types_preserve_assignment_labels(self):
        text = '''module
public import Alpha
public import Beta
def result (x : Alpha.API.value := default) : Alpha.API.value × Alpha.API.value := by
  let local : Alpha.API.value := f (Alpha.API.value := Alpha.API.value)
  have bound : Alpha.API.value := by exact local
  exact { Alpha.API.value := Alpha.API.value,
          second := f (Alpha.API.value := Alpha.API.value) }
'''
        p = plan(text)
        p.update(docstrings={})
        p['rewrites'][0]['count'] = 8
        prepared, result = style.prepare(p, text)
        self.assertIn('(x : value := default) : value × value := by', result)
        self.assertIn('let local : value := f (Alpha.API.value := value)', result)
        self.assertIn('have bound : value := by', result)
        self.assertIn('{ Alpha.API.value := value,', result)
        self.assertIn('second := f (Alpha.API.value := value)', result)
        self.assertEqual(style.apply_plan(prepared, result), result)

    def test_assignment_annotation_boundaries_and_comments(self):
        cases = [
            ('def f : Alpha.Type /- trailing type comment -/ := body', False),
            ('def f : Nat → Alpha.Type := body', False),
            ('def f : (x : Nat) → Alpha.Type := body', False),
            ('def f : Type := g (Alpha.Type /- named argument -/ := body)', True),
            ('def f : F (Alpha.Type := body) := body', True),
            ('def f : Type := { old with Alpha.Type := body }', True),
            ('def f : Type where\n  Alpha.Type := body', True),
            ('def f := { first := (show Nat from 0), Alpha.Type := body }', True),
            ('def f := { first := ":", Alpha.Type := body }', True),
            ('def f := { /- : -/ Alpha.Type := body }', True),
            ('def f := g («x:y» := body) (Alpha.Type := body)', True),
            ('def f := { Alpha.Type := body }', True),
            ('def f := { field : Alpha.Type := body }', False),
        ]
        for text, protected in cases:
            with self.subTest(text=text):
                labels = style.assignment_labels(text, style.lex(text))
                self.assertEqual(text.index('Alpha.Type') in labels, protected)

    def test_local_open_precedes_doc_and_attributes(self):
        p = plan()
        p['opens'][0]['scope'] = 'Example.result'
        p['rewrites'][0].update(scope='Example.result', count=2)
        _, result = style.prepare(p, SOURCE)
        self.assertIn('open Alpha.API (value) in\n/-- The sum', result)
        self.assertIn('{ Alpha.API.value := Alpha.API.value }', result)

    def test_proof_open_and_syntax_quote_identity(self):
        text = SOURCE.replace('def raw :=', 'macro "sample" : command => `(def Alpha.API.value := 1)\n\ndef raw :=')
        p = plan(text)
        p['opens'][0]['scope'] = 'proof:Example.result'
        p['rewrites'][0].update(scope='proof:Example.result', count=2)
        prepared, result = style.prepare(p, text)
        self.assertIn('def result : Nat := open Alpha.API (value) in value + value', result)
        self.assertIn('`(def Alpha.API.value := 1)', result)
        self.assertEqual(style.apply_plan(prepared, result), result)

    def test_syntax_command_expansions_are_protected(self):
        forms = [
            'local notation "read" => Alpha.API.value',
            'scoped notation "read" =>\n  Alpha.API.value',
            'infixl:60 " ++! " => Alpha.API.value',
            'prefix:90 "!read " => Alpha.API.value',
            'postfix:90 " read!" => Alpha.API.value',
            'syntax Alpha.API.value : term',
            'macro "read" : term =>\n  Alpha.API.value',
            'macro_rules\n  | `(read) => Alpha.API.value',
            'elab "read" : term => do\n  pure Alpha.API.value',
            'elab_rules : term\n  | `(read) => pure Alpha.API.value',
        ]
        for command in forms:
            with self.subTest(command=command):
                text = SOURCE.replace('def raw :=', command + '\n\ndef raw :=')
                p = plan(text)
                prepared, result = style.prepare(p, text)
                self.assertIn(command, result)
                self.assertEqual(style.apply_plan(prepared, result), result)
                p['rewrites'][0]['count'] += 1
                with self.assertRaisesRegex(ValueError, 'protected syntax commands'):
                    style.prepare(p, text)

    def test_syntax_command_does_not_hide_following_declaration(self):
        text = SOURCE.replace('def raw :=', 'local notation "read" =>\n'
                              '  Alpha.API.value\n\n/-- Another reading. -/\n'
                              'def afterNotation := Alpha.API.value\n\ndef raw :=')
        p = plan(text)
        p['rewrites'][0]['count'] += 1
        prepared, result = style.prepare(p, text)
        self.assertIn('  Alpha.API.value\n', result)
        self.assertIn('def afterNotation := value', result)
        self.assertEqual(style.apply_plan(prepared, result), result)

    def test_old_prepared_syntax_rewrite_is_rejected_on_original_and_result(self):
        text = 'module\nlocal notation "read" => Alpha.API.value\n'
        p = plan(text)
        p.update(imports=[], opens=[], docstrings={})
        p['rewrites'][0]['count'] = 1
        start = text.index('Alpha.API.value')
        edits = [{'start': start, 'end': start + len('Alpha.API.value'),
                  'before': 'Alpha.API.value', 'after': 'value'}]
        result = style.apply_edits(text, edits)
        p['prepared'] = {'instructions_sha256': style.instructions_hash(p),
                         'result_sha256': style.digest(result), 'edits': edits}
        for source in (text, result):
            with self.subTest(applied=source == result):
                with self.assertRaisesRegex(ValueError, 'protected syntax commands'):
                    style.apply_plan(p, source)

    def test_namespace_scopes_and_multiline_attributes(self):
        text = '''module
import Init
namespace First
namespace _root_.Second
@[simp,
  inline]
def f := 1
end _root_.Second
section
instance : Inhabited Nat := ⟨0⟩
end
def g := 2
end First
'''
        inv = style.inventory(text)
        self.assertEqual([d['name'] for d in inv['declarations']], ['First._root_.Second.f', 'First.instance@10', 'First.g'])
        self.assertEqual(text[inv['declarations'][0]['attribute_start']:][:7], '@[simp,')

    def test_dotted_namespace_partial_end_preserves_outer_components(self):
        text = 'module\nnamespace First.Second\ndef f := 1\nend Second\ndef g := 2\nend First\n'
        self.assertEqual([d['name'] for d in style.inventory(text)['declarations']], ['First.Second.f', 'First.g'])

    def test_named_dotted_section_retains_namespace_and_checks_all_headers(self):
        text = 'module\nnamespace First\nsection Outer.Inner\ndef f := 1\nend Inner\ndef g := 2\nend Outer\nend First\n'
        self.assertEqual([d['name'] for d in style.inventory(text)['declarations']], ['First.f', 'First.g'])
        with self.assertRaisesRegex(ValueError, 'end scope header mismatch'):
            style.inventory(text.replace('end Inner', 'end Different'))

    def test_absolute_declaration_differs_from_literal_root_namespace(self):
        text = 'module\nnamespace First\nnamespace _root_.Second\ndef _root_.Third.f := 1\ndef g := 2\nend _root_.Second\nend First\n'
        self.assertEqual([d['name'] for d in style.inventory(text)['declarations']], ['Third.f', 'First._root_.Second.g'])

    def test_pinned_anonymous_end_rejects_named_namespace_and_section(self):
        for opening in ['namespace A', 'section A']:
            with self.subTest(opening=opening):
                with self.assertRaisesRegex(ValueError, 'end scope header mismatch'):
                    style.inventory('module\n'+opening+'\ndef x := 1\nend\n')
        self.assertEqual(style.inventory('module\nsection\ndef x := 1\nend\n')['declarations'][0]['name'], 'x')

    def test_pinned_named_end_cannot_skip_anonymous_public_section(self):
        with self.assertRaisesRegex(ValueError, 'end scope header mismatch'):
            style.inventory('module\nnamespace A\npublic section\ndef x := 1\nend A\n')
        text = 'module\nnamespace A\npublic section\ndef x := 1\nend\nend A\n'
        self.assertEqual(style.inventory(text)['declarations'][0]['name'], 'A.x')

    def test_weak_namespace_command_requires_elaborator_backed_review(self):
        with self.assertRaisesRegex(ValueError, 'with_weak_namespace requires elaborator'):
            style.inventory('module\nnamespace First\nwith_weak_namespace _root_.Second def f := 1\nend First\n')

    def test_multiline_declaration_names_retain_original_offsets(self):
        text = """module
namespace First
/-- A scalar identity. -/
private theorem
  -- The owner is explicit despite the enclosing namespace.
  _root_.Second.identity : True := by trivial
public def
  retained : Nat := 2
end First
"""
        declarations = style.inventory(text)['declarations']
        self.assertEqual([d['name'] for d in declarations],
                         ['Second.identity', 'First.retained'])
        self.assertEqual([d['line'] for d in declarations], [4, 7])
        self.assertEqual([text[d['name_start']:d['name_end']] for d in declarations],
                         ['_root_.Second.identity', 'retained'])
        self.assertEqual(text[declarations[0]['anchor']:][:4], '/-- ')
        self.assertIn('by trivial', text[declarations[0]['start']:declarations[0]['end']])

    def test_comments_do_not_create_declarations(self):
        text = '/-\ntheorem ghost : False := sorry\n-/\ndef real := "def fake := 1"\n'
        self.assertEqual([d['name'] for d in style.inventory(text)['declarations']], ['real'])

    def test_stale_source_and_changed_instructions(self):
        p, _ = style.prepare(plan(), SOURCE)
        with self.assertRaisesRegex(ValueError, 'source changed'):
            style.apply_plan(p, SOURCE + '\n')
        p['review'] = 'Changed review.'
        with self.assertRaisesRegex(ValueError, 'instructions changed'):
            style.apply_plan(p, SOURCE)

    def test_wrong_counts_unknown_docs_and_missing_import_decisions(self):
        for mutate, error in [
            (lambda p: p['rewrites'][0].update(count=4), 'expected 4'),
            (lambda p: p['docstrings'].update({'Example.missing': 'Not present.'}), 'unknown or ambiguous'),
            (lambda p: p['imports'].pop(), 'missing import decisions'),
            (lambda p: p.update(typo=True), 'unknown keys'),
        ]:
            p = plan(); mutate(p)
            with self.assertRaisesRegex(ValueError, error):
                style.prepare(p, SOURCE)

    def test_conflicting_aliases(self):
        p = plan()
        p['opens'] = [{'namespace': 'Alpha.API', 'renaming': {'value': 'x'}, 'scope': 'file', 'reason': 'Test'},
                      {'namespace': 'Beta.API', 'renaming': {'value': 'x'}, 'scope': 'file', 'reason': 'Test'}]
        with self.assertRaisesRegex(ValueError, 'duplicate alias'):
            style.prepare(p, SOURCE)

    def test_declaration_scope_stops_before_following_commands(self):
        for command in ('#check Alpha.API.value',
                        'attribute [simp] Alpha.API.value',
                        'variable (x : Alpha.API.value)'):
            text = SOURCE.replace('def label :=', command + '\n\ndef label :=')
            p = plan(text)
            p['opens'][0]['scope'] = 'Example.result'
            p['rewrites'][0].update(scope='Example.result', count=2)
            _, result = style.prepare(p, text)
            self.assertIn(command, result)
            self.assertIn('def result : Nat := value + value', result)

    def test_comments_between_docstring_and_declaration(self):
        text = SOURCE.replace('/-- Existing documentation. -/\n@[simp]',
                              '/-- Existing documentation. -/\n-- Keep this implementation comment.\n@[simp]')
        _, result = style.prepare(plan(text), text)
        self.assertNotIn('Existing documentation.', result)
        self.assertIn('-- Keep this implementation comment.', result)
        self.assertEqual(result.count('/-- The sum'), 1)

    def test_compound_or_multiline_declarations_are_safe(self):
        # A lexical editor may reject unsupported syntax, but must never invent
        # the wrong identity or insert documentation inside a modifier prefix.
        for declaration, expected in (
            ('class inductive ReviewSingleton : Type where\n| singleton : ReviewSingleton', 'ReviewSingleton'),
            ('public\ndef reviewValue : Nat := 2', 'reviewValue'),
        ):
            text = 'module\nimport Init\n/-- Existing documentation. -/\n' + declaration + '\n'
            try:
                inv = style.inventory(text)
            except ValueError:
                continue
            self.assertEqual([d['name'] for d in inv['declarations']], [expected])
            self.assertIsNotNone(inv['declarations'][0]['doc'])

    def test_applied_plan_still_validates_prepared_payload(self):
        p, result = style.prepare(plan(), SOURCE)
        p['prepared']['edits'][0]['after'] = 'axiom bad : False'
        with self.assertRaises(ValueError):
            style.apply_plan(p, result)

    def test_forged_result_digest_does_not_skip_pending_edits(self):
        p, _ = style.prepare(plan(), SOURCE)
        p['prepared']['result_sha256'] = style.digest(SOURCE)
        with self.assertRaises(ValueError):
            style.apply_plan(p, SOURCE)

    def test_unsupported_import_layout_is_rejected(self):
        for header in ('public import Alpha Beta', 'public import\n Alpha'):
            text = SOURCE.replace('public import Alpha -- retained import comment', header)
            with self.assertRaises(ValueError):
                style.prepare(plan(text), text)

    def test_duplicate_imports_follow_one_reviewed_decision(self):
        text = SOURCE.replace('public import Beta', 'public import Beta\npublic import Alpha -- second explanation')
        prepared, result = style.prepare(plan(text), text)
        self.assertEqual(result.count('import Alpha'), 1)
        self.assertIn('-- retained import comment', result)
        self.assertIn('-- second explanation', result)
        self.assertEqual(style.apply_plan(prepared, result), result)

    def test_distinct_import_modes_require_explicit_decisions(self):
        text = SOURCE.replace('public import Beta', 'public import Beta\nimport all Alpha -- private body access')
        p = plan(text)
        with self.assertRaisesRegex(ValueError, 'mixed import modes'):
            style.prepare(p, text)
        p['imports'][0].update(mode='public import', also=['import all'])
        prepared, result = style.prepare(p, text)
        self.assertIn('public import Alpha\nimport all Alpha', result)
        self.assertIn('-- private body access', result)
        self.assertEqual(style.apply_plan(prepared, result), result)

    def test_local_and_scoped_anonymous_declarations(self):
        text = 'module\nnamespace Example\nlocal instance (n : Nat) [NeZero n] : Inhabited (Fin n) := inferInstance\nlocal macro "finish" : tactic => `(tactic| rfl)\nscoped instance : Inhabited Nat := ⟨0⟩\nend Example\n'
        p = plan(text)
        p.update(imports=[], opens=[], rewrites=[], docstrings={
            'Example.instance@3': 'Choose the finite index inhabitant.',
            'Example.macro@4': 'Close a reflexive equality.',
            'Example.instance@5': 'Use zero as the natural inhabitant.'})
        prepared, result = style.prepare(p, text)
        self.assertEqual(result.count('/--'), 3)
        self.assertIn('/-- Close a reflexive equality. -/\nlocal macro', result)
        self.assertEqual(style.apply_plan(prepared, result), result)

    def test_exact_rewrite_does_not_shorten_descendants(self):
        text = SOURCE.replace('def literal :=', 'def nested := Alpha.API.value.child\ndef literal :=')
        p = plan(text)
        p['rewrites'][0]['match'] = 'exact'
        prepared, result = style.prepare(p, text)
        self.assertIn('def nested := Alpha.API.value.child', result)
        self.assertEqual(style.apply_plan(prepared, result), result)
        p['rewrites'][0]['match'] = 'unknown'
        with self.assertRaisesRegex(ValueError, 'rewrite.match'):
            style.prepare(p, text)

    def test_field_and_constructor_documentation_targets(self):
        text = """module
import Init
namespace Example
structure Certificate where
  /-- Old field explanation. -/
  value : Nat
  /-- Old inline explanation. -/ valid :
    value = value
  fallback : Nat := by
    exact 0

inductive Result where
  /-- Old constructor explanation. -/
  | success (certificate : Certificate)
  | /-- Old inline constructor. -/ failure (index : Nat)
  | pending : Result
end Example
"""
        p = plan(text)
        p.update(imports=[{'module': 'Init', 'mode': 'import', 'reason': 'Prelude.'}],
                 opens=[], rewrites=[], docstrings={
            'Example.Certificate.value': 'The retained natural value.',
            'Example.Certificate.valid': 'Reflexivity at the retained value.',
            'Example.Certificate.fallback': 'A default natural value.',
            'Example.Result.success': 'Retain a certificate.',
            'Example.Result.failure': 'Retain a failing index.',
            'Example.Result.pending': 'Record an unfinished attempt.'})
        inv = style.inventory(text)
        self.assertEqual(len(inv['declarations']), 2)
        self.assertEqual(len(inv['children']), 6)
        self.assertEqual(inv['unsupported_children'], [])
        self.assertEqual(inv['declarations'][0]['end'], inv['declarations'][1]['anchor'])
        prepared, result = style.prepare(p, text)
        self.assertNotIn('Old ', result)
        self.assertIn('/-- A default natural value. -/ fallback : Nat := by', result)
        self.assertIn('/-- Record an unfinished attempt. -/ | pending : Result', result)
        self.assertEqual(style.apply_plan(prepared, result), result)

    def test_child_declaration_names_are_protected(self):
        text = 'module\nimport Alpha\nstructure Carrier where\n  Alpha.API.value : Nat\n  entry : Alpha.API.value\n'
        p = plan(text)
        p.update(imports=[p['imports'][0]], docstrings={})
        p['rewrites'][0]['count'] = 1
        _, result = style.prepare(p, text)
        self.assertIn('  Alpha.API.value : Nat', result)
        self.assertIn('  entry : value', result)

    def test_compact_constructors_have_separate_doc_targets(self):
        text = '''module
inductive Operation where
  | add | /-- Old subtraction. -/ sub | mul | div
inductive Result where | success (value : Nat) | failure (proof : (fun n => n) 0 = 0)
def final := 0
'''
        p = plan(text)
        p.update(imports=[], opens=[], rewrites=[], docstrings={
            'Operation': 'The four arithmetic operations.',
            'Operation.add': 'Add two values.', 'Operation.sub': 'Subtract two values.',
            'Operation.mul': 'Multiply two values.', 'Operation.div': 'Divide two values.',
            'Result': 'A retained result.', 'Result.success': 'Retain the value.',
            'Result.failure': 'Retain the equality.', 'final': 'The final constant.'})
        inv = style.inventory(text)
        self.assertEqual(inv['unsupported_children'], [])
        self.assertEqual([d['name'] for d in inv['children']],
                         ['Operation.add', 'Operation.sub', 'Operation.mul', 'Operation.div',
                          'Result.success', 'Result.failure'])
        self.assertEqual(len(inv['declarations']), 3)
        prepared, result = style.prepare(p, text)
        self.assertNotIn('Old subtraction', result)
        style.require_documentation(result)
        self.assertEqual(style.apply_plan(prepared, result), result)
        self.assertEqual(style.recover_original(prepared, result), text)

    def test_constructor_type_pipes_are_not_member_heads(self):
        text = '''module
inductive Result where
  | ok (proof : (match 0 with | n => n) = 0) | fallback
'''
        inv = style.inventory(text)
        self.assertEqual(inv['unsupported_children'], [])
        self.assertEqual([d['name'] for d in inv['children']], ['Result.ok', 'Result.fallback'])

    def test_proof_scope_rejects_signature_let_assignment(self):
        for signature in ['let value := 0; value = value',
                          '∀ n : Nat, let value := n; value = value']:
            text = f'module\ntheorem result : {signature} := by rfl\n'
            p = plan(text)
            p.update(imports=[], docstrings={}, rewrites=[],
                     opens=[dict(namespace='Nat', scope='proof:result', reason='Proof helpers.')])
            with self.assertRaisesRegex(ValueError, 'unsupported unparenthesized signature expression'):
                style.prepare(p, text)
        for signature in ['(let value := 0; value = value)',
                          'if True then True else False',
                          '(fun n : Nat => n) = fun n => n']:
            text = f'module\ntheorem result : {signature} := by rfl\n'
            p = plan(text)
            p.update(imports=[], docstrings={}, rewrites=[],
                     opens=[dict(namespace='Nat', scope='proof:result', reason='Proof helpers.')])
            prepared, result = style.prepare(p, text)
            self.assertIn(signature + ' := open Nat in by', result)
            self.assertEqual(style.apply_plan(prepared, result), result)

    def test_unsupported_grouped_fields_are_reported(self):
        text = 'module\nstructure Pair where\n  (left right : Nat)\n  total : Nat\n'
        inv = style.inventory(text)
        self.assertEqual([c['name'] for c in inv['children']], ['Pair.total'])
        self.assertEqual(inv['unsupported_children'][0]['parent'], 'Pair')
        self.assertIn('grouped', inv['unsupported_children'][0]['reason'])

    def test_prepared_edits_are_recomputed(self):
        p, _ = style.prepare(plan(), SOURCE)
        p['prepared']['edits'][0]['after'] = 'axiom bad : False'
        with self.assertRaisesRegex(ValueError, 'do not match'):
            style.apply_plan(p, SOURCE)

    def test_anonymous_examples_are_documented_scoped_and_not_renamable(self):
        text = 'module\nnamespace Checks\ntheorem first : True := by trivial\nexample (n : Nat) : Nat.succ n = n + 1 := rfl\nexample : True := by trivial\nend Checks\n'
        inv = style.inventory(text)
        self.assertEqual([d['key'] for d in inv['declarations']],
                         ['Checks.first', 'Checks.example@4', 'Checks.example@5'])
        first, example, last = inv['declarations']
        self.assertEqual(first['end'], example['anchor'])
        self.assertEqual(example['end'], last['anchor'])
        self.assertEqual(example['name_start'], example['name_end'])
        p = plan(text)
        p.update(imports=[], opens=[dict(namespace='Nat', scope='Checks.example@4', reason='Successor notation.')],
                 rewrites=[dict(**{'from': 'Nat.succ', 'to': 'succ'}, scope='Checks.example@4', count=1, reason='Opened natural namespace.')],
                 docstrings={'Checks.first': 'Truth holds.', 'Checks.example@4': 'Successor agrees with adding one.', 'Checks.example@5': 'Truth also holds here.'})
        prepared, result = style.prepare(p, text)
        style.require_documentation(result)
        self.assertIn('example (n : Nat) : succ n = n + 1', result)
        self.assertEqual(style.apply_plan(prepared, result), result)
        p['declaration_renames'] = [{'from': 'Checks.example@4', 'to': 'Checks.named', 'reason': 'Invalid anonymous rename.'}]
        with self.assertRaises(ValueError):
            style.prepare(p, text)


if __name__ == '__main__':
    unittest.main()
