#!/usr/bin/env python3
"""Check the current-source naming guard's lexical coverage and exclusions."""
from pathlib import Path
import unittest

from scripts.verification import authored_names as checker


class AuthoredNameTests(unittest.TestCase):
    def inspect(self, source):
        return checker.inspect_source("Test/Fixture.lean", source)

    def test_comments_strings_and_nested_comments_are_opaque(self):
        row = self.inspect('module\n/- namespace _Hidden /- bad_public -/ -/\n'
                           'def scalar := "Purelib._Hidden.bad_public"\n-- bad_public\n')
        self.assertEqual(row["owners"], [])
        self.assertEqual(row["references"], [])

    def test_namespace_and_absolute_multiline_owners(self):
        row = self.inspect('module\nnamespace Purelib._First\npublic theorem\n'
                           '  _root_.Purelib._Second.law : True := by trivial\nend Purelib._First\n')
        self.assertEqual([(e["kind"], e["components"]) for e in row["owners"]],
                         [("declaration", ["_Second"]), ("namespace", ["_First"])])

    def test_ordinary_root_namespace_is_a_literal_forbidden_owner(self):
        row = self.inspect('module\nnamespace Purelib.Host\nnamespace _root_.Purelib.Subject\ndef law := 1\nend _root_.Purelib.Subject\nend Purelib.Host\n')
        self.assertEqual([(e['kind'], e['components']) for e in row['owners']],
                         [('declaration', ['_root_']), ('namespace', ['_root_'])])

    def test_only_leading_reference_root_qualifier_is_exempt(self):
        row = self.inspect('module\ndef good := _root_.Purelib.Subject.law\ndef bad := Purelib.Subject._root_.law\n')
        self.assertEqual([e['name'] for e in row['references']], ['Purelib.Subject._root_.law'])

    def test_escaped_components_keep_dots_inside_the_name(self):
        self.assertEqual(checker.components('Purelib.«_owner.with.dot».law'),
                         ('Purelib', '_owner.with.dot', 'law'))
        row = self.inspect('module\ntheorem _root_.Purelib.«_owner.with.dot».law : True := by trivial\n')
        self.assertEqual(row["owners"][0]["components"], ['_owner.with.dot'])

    def test_quoted_names_and_local_suffix_bindings_are_checked(self):
        row = self.inspect('module\nopen Lean\ndef quoted := `Purelib.Subject.law_public\n'
                           'theorem retained (region_public : True) : True := region_public\n')
        self.assertEqual([e["name"] for e in row["references"]],
                         ['Purelib.Subject.law_public', 'region_public', 'region_public'])

    def test_syntax_quotation_references_are_not_masked(self):
        row = self.inspect('module\nopen Lean\nmacro "sample" : term => `(Purelib.Subject.law_public)\n')
        self.assertEqual([e["name"] for e in row["references"]], ['Purelib.Subject.law_public'])

    def test_suffix_inside_qualified_and_method_chains_is_checked(self):
        source = ('module\ndef weak := Purelib.Subject.«law_public».trans\n'
                  'def impossible := witness.nonempty_public.elim\n')
        row = self.inspect(source)
        self.assertEqual([entry["suffix_components"] for entry in row["references"]],
                         [["law_public"], ["nonempty_public"]])
        for entry in row["references"]:
            self.assertEqual(source[entry["start"]:entry["end"]], entry["name"])

    def test_compiler_and_root_markers_are_separate(self):
        row = self.inspect('module\ntheorem _root_.Purelib.Subject.law : True := by trivial\n'
                           'def reprName := `_private.Owner.0.Subject.helper\n'
                           'def compilerMarker := `Stored__public___redArg\n')
        self.assertEqual(row["owners"], [])
        self.assertEqual(row["references"], [])

    def test_anonymous_declaration_keys_are_not_lean_names(self):
        row = self.inspect('module\nnamespace Purelib.Subject\nexample : True := by trivial\n'
                           'instance : Inhabited Nat := ⟨0⟩\nend Purelib.Subject\n')
        self.assertEqual(row["declarations"], 2)
        self.assertEqual(row["owners"], [])

    def test_datatype_name_is_also_its_generated_api_owner(self):
        row = self.inspect('module\nstructure Purelib.Subject.«_Carrier» where\n  value : Nat\n')
        self.assertEqual(row["owners"][0]["components"], ['_Carrier'])

    def test_wordlike_notation_is_not_a_reference_name(self):
        row = self.inspect('module\ndef power := x² + x¹\n')
        self.assertEqual(row["references"], [])

    def test_unterminated_comment_fails_closed(self):
        with self.assertRaises(ValueError):
            self.inspect('module\n/- namespace _Hidden')

    def test_reference_spans_bind_original_text(self):
        source = 'module\ndef proofName := `Purelib.Subject.«law_public»\n'
        row = self.inspect(source)
        entry = row["references"][0]
        self.assertEqual(source[entry["start"]:entry["end"]], entry["name"])
        self.assertEqual(entry["suffix_components"], ['law_public'])
        self.assertEqual(entry["line"], 2)


if __name__ == '__main__':
    unittest.main()
