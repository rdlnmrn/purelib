#!/usr/bin/env python3
"""Regression checks for declaration names and real source contracts."""
from pathlib import Path
import unittest,sys
sys.dont_write_bytecode=True
from scripts.verification import sources as m
from scripts.paths import ROOT
class Parsing(unittest.TestCase):
 def test_mutual_end_retains_enclosing_namespace(self):
  text='namespace Subject\nmutual\n  def first : Nat := 0\n  def second : Nat := first\nend\nnamespace Coefficients\ndef toList : List Nat := []\nend Coefficients\ntheorem scalar : 0 = 0 := rfl\nend Subject\n'
  names=[r[0]for r in m.namespace_and_declarations('Purelib/Subject.lean',text)]
  self.assertEqual(names,['Subject.first','Subject.second','Subject.Coefficients.toList','Subject.scalar'])
 def test_nested_mutual_and_attributed_public_section_keep_actual_owner(self):
  text='module\n@[expose] public section\nnamespace Subject\nmutual\n  def first : Nat := 0\n  def second : Nat := 1\nend\npublic def last : Nat := first\nend Subject\n'
  self.assertEqual([r[0]for r in m.namespace_and_declarations('Purelib/Subject.lean',text)],['Subject.first','Subject.second','Subject.last'])
 def test_universe_annotation_is_not_a_trailing_dot_in_the_name(self):
  text='namespace Subject\npublic structure Payload.{u, v} (x : Type u) where\n  field : x\nend Subject\n'
  self.assertEqual(m.namespace_and_declarations('Purelib/Subject.lean',text),[('Subject.Payload','Payload','structure','public',2)])
 def test_comment_prose_and_strings_do_not_create_declarations_or_scopes(self):
  text='namespace Subject\n/-\nstructure so this is prose.\nnamespace Fake\n/- nested -/\nend Fake\n-/\ndef actual := "theorem fake : False := by contradiction"\nend Subject\n'
  self.assertEqual(m.namespace_and_declarations('Purelib/Subject.lean',text),[('Subject.actual','actual','def','public',8)])
 def test_real_declaration_on_a_docstring_closing_line_is_retained(self):
  text='namespace Subject\n/- Documentation\n-/ public def value : Nat := 2\nend Subject\n'
  self.assertEqual(m.namespace_and_declarations('Purelib/Subject.lean',text),[('Subject.value','value','def','public',3)])
  self.assertEqual(m.declaration_contract(text.splitlines(),3,'def'),'-/ public def value : Nat :=')
 def test_actual_legendre_names_keep_original_universe_and_payload_contracts(self):
  root=ROOT
  cases=[('Purelib/Curves/Legendre/Acquisition/Words/State.lean','Purelib.Curves.Legendre.Acquisition.Words.State.InputPayload'),('Purelib/Curves/Legendre/Acquisition/Words/Report.lean','Purelib.Curves.Legendre.Acquisition.Words.Report.OutcomePayload')]
  for source,name in cases:
   text=(root/source).read_text();rows=m.namespace_and_declarations(source,text);self.assertEqual(sum(x[0]==name for x in rows),1);self.assertFalse(any(x[0]==name+'.'for x in rows))
if __name__=='__main__':unittest.main()
