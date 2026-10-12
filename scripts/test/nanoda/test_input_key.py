#!/usr/bin/env python3
"""Exercise import-closure invalidation independently of expensive exports."""
import json
from pathlib import Path
import tempfile
from unittest.mock import patch

from scripts.nanoda import input_key as m


def main():
    with tempfile.TemporaryDirectory() as temporary:
        root = Path(temporary)
        library = root / 'library'
        shadow = root / 'shadow'
        library.mkdir(); shadow.mkdir()
        search = [shadow, library]
        driver = root / 'driver'; driver.write_text('driver-v1');driver.chmod(0o700)
        manifest = root / 'modules'; manifest.write_text('A\n')
        cache = root / 'cache'
        for name, imports in [('A', ['B']), ('B', []), ('Unrelated', []), ('Added', [])]:
            (library / (name + '.olean')).write_text(json.dumps(imports))
        for part in ['server', 'private']:
            (library / ('B.olean.' + part)).write_text(part)
        calls = []

        def produce(command, **kwargs):
            calls.append(command)
            pending, nodes = ['A'], {}
            while pending:
                name = pending.pop()
                if name in nodes:
                    continue
                path = m.resolve(name, search)
                imports = json.loads(path.read_text())
                files = [str(path)]
                if name == 'B':
                    files += [str(path) + '.server', str(path) + '.private']
                nodes[name] = {'name': name, 'imports': imports, 'files': files}
                pending.extend(imports)
            Path(command[-1]).write_text(json.dumps({'schema': 1, 'roots': ['A'], 'modules': list(nodes.values())}))

        def key(policy='policy'):
            return m.input_key(manifest, [str(driver)], cache, search, policy)

        with patch.object(m.subprocess, 'run', side_effect=produce):
            initial, receipt, reused = key()
            assert not reused and len(calls) == 1
            assert key()[0] == initial and key()[2] and len(calls) == 1
            (library / 'Unrelated.olean').write_text('unrelated edit')
            assert key()[0] == initial and len(calls) == 1
            (library / 'B.olean.private').write_text('private change')
            private = key()[0]
            assert private != initial and len(calls) == 2
            assert key('new policy')[0] != private and len(calls) == 2
            (library / 'A.olean').write_text('["B", "Added"]')
            added, receipt, _ = key()
            assert added != private and str(library / 'Added.olean') in json.loads(receipt.read_text())['files']
            (library / 'Added.olean').write_text('["Unrelated"]')
            # Make the newly reachable dependency valid before extracting it.
            (library / 'Unrelated.olean').write_text('[]')
            assert key()[0] != added
            (library / 'A.olean').write_text('["B"]')
            removed = key()[0]; count = len(calls)
            (library / 'Added.olean').write_text('unreachable now')
            assert key()[0] == removed and len(calls) == count
            for suffix in ['', '.server', '.private']:
                (shadow / ('B.olean' + suffix)).write_bytes((library / ('B.olean' + suffix)).read_bytes())
            assert key()[0] != removed
            # An interrupted refresh must not destroy the previous inventory.
            before_key, before_receipt, _ = key()
            old = json.loads(before_receipt.read_text())
            old_bytes = Path(old['inventory']).read_bytes()
            (shadow / 'B.olean.private').write_text('refresh after interruption')
            with patch.object(m.subprocess, 'run', side_effect=RuntimeError('interrupted')):
                try:
                    key()
                except RuntimeError as error:
                    assert str(error) == 'interrupted'
                else:
                    raise AssertionError('interrupted producer accepted')
            assert Path(old['inventory']).read_bytes() == old_bytes
            assert key()[0] != before_key
            # Inputs removed from disk must not become a successful identity.
            private_path = shadow / 'B.olean.private'
            private_bytes = private_path.read_bytes()
            private_path.unlink()
            try:
                key()
            except FileNotFoundError:
                pass
            else:
                raise AssertionError('missing private input accepted')
            private_path.write_bytes(private_bytes)
            driver.write_text('driver-v2')
            changed_driver, receipt, _ = key()
            assert changed_driver != removed
            saved = json.loads(receipt.read_text())
            Path(saved['inventory']).write_text('corrupt inventory')
            try:
                key()
            except ValueError as error:
                assert 'corrupt cached' in str(error)
            else:
                raise AssertionError('corrupt inventory reused')
        print('module-input dependency, private-part, unrelated-edit, resolution, policy and corruption tests passed')


if __name__ == '__main__':
    main()
