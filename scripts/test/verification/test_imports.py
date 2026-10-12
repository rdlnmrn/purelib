"""Protect exact Lean header modes and reject imports hidden in source data."""

import unittest

from scripts.verification.sources import imports, namespace_and_declarations


class ImportTests(unittest.TestCase):
    def test_import_modes_and_comments(self):
        source = '''module
import Alpha
public import Beta
meta import Gamma
public meta import Delta
import all Epsilon
-- import Ghost
/- import Phantom
   /- import Shadow -/
-/
import Zeta -- import Trailing
private meta import all Eta Theta
def s := "import Fiction"
/-! import Buried -/
'''
        self.assertEqual(imports(source), [
            ('Alpha', 'ordinary'), ('Beta', 'public'), ('Gamma', 'meta'),
            ('Delta', 'public meta'), ('Epsilon', 'all'), ('Zeta', 'ordinary'),
            ('Eta', 'private meta all'), ('Theta', 'private meta all'),
        ])

    def test_only_header_imports_count(self):
        self.assertEqual(imports('module\nimport Actual\npublic section\n'
                                 'def text := r#"import Fiction"#\nimport Late\n'),
                         [('Actual', 'ordinary')])

    def test_attributed_section_keeps_actual_namespace(self):
        source = '''public section
namespace Example
@[expose] public section
public def retained : Nat := 1
end
def following : Nat := retained
end Example
'''
        self.assertEqual([row[0] for row in namespace_and_declarations('Example.lean', source)],
                         ['Example.retained', 'Example.following'])


if __name__ == '__main__':
    unittest.main()
