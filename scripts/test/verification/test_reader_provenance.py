"""Protect reader source and artifact provenance."""

from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from scripts.lean_module_data.kernel import Bindings
from scripts.lean_module_data.compact import InvalidArtifact
from scripts.verification import contracts


class ReaderProvenanceTests(unittest.TestCase):
    def test_bound_original_path_cannot_fall_back_to_replacement(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            original = root / 'original.py'
            original.write_text('Retained actual source bytes')
            bindings = Bindings()
            bindings.add(original, 'host-reader-source')
            bindings.verify()
            (root / 'replacement.py').write_bytes(original.read_bytes())
            original.unlink()
            with self.assertRaisesRegex(InvalidArtifact, 'changed invocation input'):
                bindings.verify()

    def test_changed_private_part_and_newly_present_absent_part_invalidate_binding(self):
        with tempfile.TemporaryDirectory() as directory:
            private = Path(directory) / 'Fixture.olean.private'
            bindings = Bindings()
            bindings.add(private, 'selected-artifact')
            bindings.verify()
            private.write_bytes(b'Original proof')
            with self.assertRaises(InvalidArtifact):
                bindings.verify()
            bindings = Bindings()
            bindings.add(private, 'selected-artifact')
            private.write_bytes(b'Changed proof')
            with self.assertRaisesRegex(InvalidArtifact, 'changed consumed input'):
                bindings.add(private, 'import-private')

    def test_current_reader_digest_requires_every_selected_source(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            frontend = root / 'project-module-data.py'
            parts = [root / part for part in ('cli.py', 'typed.py', 'contracts.py')]
            for path in [frontend, *parts]:
                path.write_text('Original decoder bytes: ' + path.name)
            with patch.object(contracts, 'ROOT', root), \
                 patch.object(contracts, 'DAG_HELPER', frontend), \
                 patch.object(contracts, 'READER_PARTS', tuple(parts)):
                before = contracts.reader_digest(2)
                parts[1].write_text('Changed decoder')
                self.assertNotEqual(before, contracts.reader_digest(2))
                parts[1].unlink()
                with self.assertRaises(FileNotFoundError):
                    contracts.reader_digest(2)


if __name__ == '__main__':
    unittest.main()
