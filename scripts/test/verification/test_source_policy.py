"""Exercise real source violations, protected inputs and missing inventories."""

from pathlib import Path
import tempfile
import unittest

from scripts.verification import source_policy as policy, sources


class SourcePolicyTests(unittest.TestCase):
    def test_prose_strings_and_quoted_inputs_are_not_executed_commands(self):
        source = '''module
/- admit sorry /- classical -/ noncomputable -/
def text := r#"Classical.choice and native_decide"#
def quoted := `(tactic| classical; sorry)
def name := `Classical.choice
'''
        self.assertEqual(policy.violations(source), [])

    def test_actual_commands_tactics_and_resources_fail(self):
        for source in ('noncomputable def value := 1', 'theorem p : True := by classical; trivial',
                       'example : True := by sorry', 'example : True := by admit',
                       'example : True := by native_decide', 'def x := Classical.choice witness',
                       'set_option maxHeartbeats 0 in\ndef value := 1',
                       'set_option maxRecDepth 1000\ndef value := 1'):
            with self.subTest(source=source):
                self.assertTrue(policy.violations(source))

    def test_current_import_modes_and_completed_route_rejection(self):
        text = 'module\npublic meta import Mathlib.Topology.Basic\nimport Alpha Beta\n'
        self.assertEqual(sources.imports(text), [('Mathlib.Topology.Basic', 'public meta'),
                                               ('Alpha', 'ordinary'), ('Beta', 'ordinary')])
        self.assertTrue(policy.violations(text))
        self.assertEqual(policy.violations('import Purelib.Topology.Polygon\n'), [])

    def test_missing_unreadable_empty_and_malformed_inputs_fail(self):
        with tempfile.TemporaryDirectory() as directory:
            with self.assertRaises(FileNotFoundError):
                policy.check(['missing.lean'], Path(directory))
        with self.assertRaisesRegex(ValueError, 'empty'):
            policy.check([])
        with self.assertRaisesRegex(ValueError, 'unclosed comment'):
            policy.violations('/- unterminated')
        with self.assertRaisesRegex(ValueError, 'quotation'):
            policy.violations('def quoted := `(tactic| sorry')


if __name__ == '__main__':
    unittest.main()
