#!/usr/bin/env python3
"""Check that compiled contracts detect hidden or opaque public APIs."""

import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch


from scripts.verification import contracts

old = {"kind": "def", "private": False, "internal": False,
       "exported": None, "exposed": None}
new = dict(old, exported=True, exposed=True)
before = {"modules": ["Pilot"], "declarations": {"Pilot": {"Pilot.value": old}}}
after = {"module_system": {"Pilot": True},
         "declarations": {"Pilot": {"Pilot.value": new}}}
assert contracts.public_visibility_regressions(before, after) == []

after["declarations"]["Pilot"]["Pilot.value"] = dict(new, exported=False)
assert contracts.public_visibility_regressions(before, after) == [
    ("Pilot", "Pilot.value", "not-exported")]

after["declarations"]["Pilot"]["Pilot.value"] = dict(new, exposed=False)
assert contracts.public_visibility_regressions(before, after) == [
    ("Pilot", "Pilot.value", "not-exposed")]

after["declarations"]["Pilot"]["Pilot.value"] = dict(new, private=True)
assert contracts.public_visibility_regressions(before, after) == [
    ("Pilot", "Pilot.value", "not-exported")]
print("compiled public visibility contracts passed")


class ArtifactSelectionTests(unittest.TestCase):
    def test_default_host_invocation_remains_lake_env(self):
        with patch.object(contracts, 'run', side_effect=AssertionError('unexpected environment lookup')):
            command, env = contracts.contract_invocation('Example')
            explicit, explicit_env = contracts.contract_invocation(
                'Example', contracts.ROOT / '.lake/build/lib/lean')
        self.assertEqual(command, (contracts.ROOT / 'scripts/run-lake.sh', 'env',
                                   'python3', contracts.DAG_HELPER, 'contracts', '--schema', '2', 'Example'))
        self.assertEqual(explicit, command)
        self.assertIsNone(env)
        self.assertIsNone(explicit_env)

    def test_schema1_uses_the_same_content_bound_host_reader(self):
        with patch.object(contracts, 'run', side_effect=AssertionError('unexpected environment lookup')):
            command, env = contracts.contract_invocation('Example', schema=1)
        self.assertEqual(command, (contracts.ROOT / 'scripts/run-lake.sh', 'env',
                                   'python3', contracts.DAG_HELPER, 'contracts', '--schema', '1', 'Example'))
        self.assertIsNone(env)
        self.assertIsNotNone(contracts.reader_digest(1))
        self.assertEqual(contracts.reader_digest(1), contracts.reader_digest(2))

    def test_selected_missing_artifact_cannot_fall_back_to_default(self):
        with tempfile.TemporaryDirectory() as temporary, \
             patch.object(contracts, 'contract_invocation', side_effect=AssertionError('must reject before loading')):
            with self.assertRaisesRegex(FileNotFoundError, 'missing selected compiled artifact'):
                list(contracts.lean_records(['Purelib.Data.Nat.Addition'], 2, Path(temporary)))

    def test_nondefault_artifacts_are_actually_imported(self):
        """Compile two different bodies under one module name and read each root."""
        executable = contracts.run(contracts.ROOT / 'scripts/run-lake.sh', 'env', 'which', 'lean').strip()
        search = contracts.run(contracts.ROOT / 'scripts/run-lake.sh', 'env', 'printenv', 'LEAN_PATH').strip()
        module = 'ContractArtifactSelectionFixture'
        with tempfile.TemporaryDirectory(prefix='compiled-contract-artifacts-') as temporary:
            roots = [Path(temporary) / 'first', Path(temporary) / 'second']
            declarations = []
            for root, value in zip(roots, [7, 19]):
                root.mkdir()
                source = root / (module + '.lean')
                source.write_text(f'module\n@[expose] public def retainedValue : Nat := {value}\n')
                subprocess.run([executable, '-R', str(root), '-DwarningAsError=true', str(source),
                                '-o', str(source.with_suffix('.olean'))], check=True,
                               env={**os.environ, 'LEAN_PATH': search}, capture_output=True, text=True)
                records = list(contracts.lean_records([module], 2, root))
                self.assertTrue(all('declaration' in row for row in records))
                declarations.append({row['declaration']['name']: row['declaration'] for row in records
                                     if 'declaration' in row})
            self.assertEqual(set(declarations[0]), set(declarations[1]))
            self.assertNotEqual(declarations[0]['retainedValue']['body'],
                                declarations[1]['retainedValue']['body'])
            # Missing private metadata must not borrow the other root or package artifacts.
            (roots[0] / (module + '.olean.private')).unlink()
            with self.assertRaisesRegex(FileNotFoundError, 'missing selected compiled artifact'):
                list(contracts.lean_records([module], 2, roots[0]))

    def test_empty_module_metadata_preserves_capture_provenance(self):
        """Anonymous examples leave no declarations, but must still be captured."""
        executable = contracts.run(contracts.ROOT / 'scripts/run-lake.sh', 'env', 'which', 'lean').strip()
        search = contracts.run(contracts.ROOT / 'scripts/run-lake.sh', 'env', 'printenv', 'LEAN_PATH').strip()
        module = 'EmptyContractFixture'
        with tempfile.TemporaryDirectory(prefix='compiled-contract-empty-') as temporary:
            root = Path(temporary)
            source = root / (module + '.lean')
            source.write_text('module\nexample : 1 = 1 := rfl\n')
            subprocess.run([executable, '-R', str(root), '-DwarningAsError=true', str(source),
                            '-o', str(source.with_suffix('.olean'))], check=True,
                           env={**os.environ, 'LEAN_PATH': search}, capture_output=True, text=True)
            (root / 'lean-toolchain').write_text('test-toolchain\n')
            for schema in (1, 2):
                records = list(contracts.lean_records([module], schema, root, include_metadata=True))
                self.assertEqual(records, [{'module': module, 'module_system': True,
                                            'declaration_count': 0}])
                with patch.object(contracts, 'ROOT', root), \
                     patch.object(contracts, 'lean_records', return_value=iter(records)), \
                     patch.object(contracts, 'run', return_value='test-revision\n'), \
                     patch.object(contracts, 'reader_digest', return_value='fixture-reader-digest'):
                    result = contracts.capture([module], root, False, schema)
                self.assertEqual(result['declarations'], {module: {}})
                self.assertEqual(result['module_system'], {module: True})
                self.assertEqual(result['sources'][module]['sha256'], contracts.file_digest(source))
                self.assertEqual(result['artifacts'][module]['.private'],
                                 contracts.file_digest(root / (module + '.olean.private')))

    def test_missing_duplicate_and_truncated_metadata_fail_closed(self):
        meta = {'module': 'Example', 'module_system': True, 'declaration_count': 0}
        for records in ([], [meta, meta], [dict(meta, declaration_count=1)],
                        [dict(meta, declaration_count=True)], [dict(meta, module_system=1)]):
            with self.subTest(records=records), \
                 patch.object(contracts, 'lean_records', return_value=iter(records)), \
                 self.assertRaises(RuntimeError):
                contracts.capture(['Example'], Path('/unused'), False)


class NativeObservationTests(unittest.TestCase):
    def test_current_runtime_observation_has_bound_native_inputs(self):
        record = contracts.capture(['scripts.observations.ProjectQueryReplay'],
                                   contracts.ROOT / '.lake/build/lib/lean', True)
        self.assertEqual(record['observation'], {
            'module': 'Purelib.Examples.Approximation.Queries.Adaptive.WorkedExamples',
            'questions': [0, 2, 0], 'value': 5, 'replay': {'kind': 'ok', 'value': 5}})
        self.assertEqual(record['observation_inputs']['selected_modules'],
                         ['scripts.observations.ProjectQueryReplay'])
        self.assertEqual(record['tool_sha256']['observation_executable'],
                         contracts.file_digest(contracts.ROOT / '.lake/build/bin/project_query_replay_observation'))

    def test_alternate_artifacts_cannot_use_the_current_native_executable(self):
        with tempfile.TemporaryDirectory() as temporary:
            with self.assertRaisesRegex(ValueError, 'current default build'):
                contracts.capture(['scripts.observations.ProjectQueryReplay'], Path(temporary), True)


if __name__ == '__main__':
    unittest.main()
