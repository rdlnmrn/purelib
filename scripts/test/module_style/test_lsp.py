"""Keep API-reference queries source-aware and prevent dependency writes."""
import asyncio
import json
import os
from pathlib import Path
import tempfile
from types import ModuleType, SimpleNamespace
import unittest
from unittest.mock import patch

from scripts.module_style import lsp


class ReferenceQueryTests(unittest.TestCase):
    def query(self, stale=False):
        calls = []
        aio = ModuleType('leanclient.aio')
        convert = ModuleType('leanclient.aio.convert')
        convert.range_from_utf16 = lambda _lines, value: value

        class Transport:
            async def request(self, method, params, timeout):
                calls.append(('request', method, params))

        class Client:
            def __init__(self, project, **kwargs):
                self._transport = Transport()
                self.request_timeout = 300

            async def start(self):
                calls.append(('environment', dict(os.environ)))

            async def wait_for_ileans(self):
                pass

            async def open(self, path, *, wait, dependency_build_mode):
                calls.append(('open', path, wait, dependency_build_mode))
                return SimpleNamespace(text=source, stale_imports=stale)

            async def _barrier_once(self, path):
                calls.append(('readonly_barrier', path))

            async def barrier(self, path):
                raise AssertionError('ordinary barrier may rebuild dependencies')

            async def diagnostics(self, path, *, fresh):
                return SimpleNamespace(items=[], fatal_error=False, has_errors=False)

            async def references(self, path, line, column, *, fresh):
                calls.append(('references', path, line, column, fresh))
                return [{'uri': 'file:///ExampleConsumer.lean', 'range': {}}]

            async def close(self):
                calls.append(('close',))

        aio.AsyncLeanLSPClient = Client
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            upstream = root / 'upstream'
            (upstream / 'bin').mkdir(parents=True)
            (upstream / 'bin/lean').touch()
            prefix = root / '.lake/core-toolchain'
            prefix.mkdir(parents=True)
            (prefix / 'CORE-PREFIX.json').write_text(json.dumps({'base_sysroot': str(upstream)}))
            path = root / 'Example.lean'
            source = 'module\npublic def example := 1\n'
            path.write_text(source)
            args = SimpleNamespace(mode='references', line=2, column=12)
            with patch.object(lsp, 'ROOT', root), patch.dict(os.environ, clear=True), \
                 patch.dict('sys.modules', {'leanclient.aio': aio, 'leanclient.aio.convert': convert}), \
                 patch.object(lsp.subprocess, 'check_output', side_effect=['artifacts\n', 'sources\n']):
                result, errors = asyncio.run(lsp.query(args, path, source))
            environment = next(row[1] for row in calls if row[0] == 'environment')
            self.assertEqual(environment['LEAN_SRC_PATH'], 'sources')
            self.assertEqual(environment['LEAN_PATH'], str(prefix / 'lib/lean') + ':artifacts')
        self.assertIn(('open', 'Example.lean', False, 'never'), calls)
        self.assertIn(('readonly_barrier', 'Example.lean'), calls)
        self.assertIn(('request', '$/lean/waitForILeans', {}), calls)
        self.assertEqual(calls[-1], ('close',))
        return result, errors

    def test_reference_loader_receives_source_and_artifact_paths(self):
        result, errors = self.query()
        self.assertFalse(errors)
        self.assertTrue(result['reference_index_ready'])
        self.assertEqual(len(result['result']), 1)

    def test_stale_imports_are_reported_without_an_automatic_build(self):
        result, errors = self.query(stale=True)
        self.assertTrue(errors)
        self.assertTrue(result['stale_imports'])


if __name__ == '__main__':
    unittest.main()
