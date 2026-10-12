"""Verify private source selection on current isolated compiler fixtures."""

import os
from pathlib import Path
import subprocess
import tempfile
import unittest

from scripts.paths import ROOT
from scripts.lean_module_data.audit_metadata import audit_root
from scripts.lean_module_data.export import Environment
from scripts.lean_module_data.paths import search_path


class RootInventoryTests(unittest.TestCase):
    """Retain private authors with source ranges, including internal namespaces."""

    def test_source_ranges_and_private_roots_match_authoritative_inventory(self):
        module = 'ModuleVerification.Explicit'
        source = (ROOT / 'scripts/test/fixtures/module_verification/Explicit.lean').read_text()
        source += '\nprivate theorem _root_.ModuleVerification._SourceNamespace.retained : True := True.intro\n'
        with tempfile.TemporaryDirectory(prefix='nanoda-root-inventory-') as directory:
            work = Path(directory)
            source_root, output = work / 'sources', work / 'objects'
            path = source_root / 'ModuleVerification/Explicit.lean'
            artifact = output / 'ModuleVerification/Explicit.olean'
            path.parent.mkdir(parents=True)
            artifact.parent.mkdir(parents=True)
            path.write_text(source)
            subprocess.run(['lean', '-R', str(source_root), '-DwarningAsError=true',
                            '-o', str(artifact), str(path)], check=True, capture_output=True)
            env = Environment([module], [output, *search_path()])
            expected = []
            for name in env.observation.inventory(module)[0]:
                ref = env.observation.by_name.get(name)
                if ref is not None and audit_root(name, ref, env.root_metadata):
                    expected.append((module, ref.key))
            actual, _ = env.roots([module])
            self.assertEqual(actual, expected)
            names = {env.text(key) for _, key in actual}
            self.assertTrue(any(name.startswith('_private.') for name in names))
            retained = next(name for name in names
                            if name.endswith('.ModuleVerification._SourceNamespace.retained'))
            self.assertTrue(env.root_metadata.has_range(env.names[env.named(retained)]))


if __name__ == '__main__':
    unittest.main()
