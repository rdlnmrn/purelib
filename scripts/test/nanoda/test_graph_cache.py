#!/usr/bin/env python3
"""Check graph producer recovery, corruption and input-change rejection."""
import json
from pathlib import Path
import tempfile
from unittest.mock import patch

from scripts.nanoda import export_graph as m


def main():
    with tempfile.TemporaryDirectory() as temporary:
        root = Path(temporary)
        source = root / 'input.olean'; source.write_text('compiled input')
        files = {str(source): m.inputs.digest(source)}
        identity = {'files': files, 'policy': 'test'}
        directory = root / 'graph'
        output = directory / 'graph.jsonl'
        command = ['producer', str(output)]
        calls = []
        content = '\n'.join(map(json.dumps, [
            {'schema': 1, 'roots': [{'name': 'root', 'owner': 'M'}]},
            {'name': 'root', 'dependencies': ['dep'], 'atomic': [], 'expression_estimate': 1},
            {'name': 'dep', 'dependencies': [], 'atomic': [], 'expression_estimate': 1}])) + '\n'

        def produce(*args, **kwargs):
            calls.append(args)
            output.write_text(content)

        with patch.object(m.subprocess, 'run', side_effect=produce):
            path, reused = m.cached_graph(directory, identity, command, files, {})
            assert path == output and not reused and len(calls) == 1
            assert m.cached_graph(directory, identity, command, files, {})[1] and len(calls) == 1
            receipt_path = directory / 'graph.receipt.json'
            old = json.loads(receipt_path.read_text()); old['validator'] = 'older checks'
            receipt_path.write_text(json.dumps(old))
            assert m.cached_graph(directory, identity, command, files, {})[1] and len(calls) == 1
            assert json.loads(receipt_path.read_text())['validator'] != 'older checks'
            (directory / 'graph.receipt.json').unlink()
            assert m.cached_graph(directory, identity, command, files, {})[1] and len(calls) == 1
            receipt = json.loads((directory / 'graph.receipt.json').read_text())
            assert receipt['recovered_publication'] and receipt['declarations'] == 2
            output.write_text(content.replace('dep', 'bad'))
            try:
                m.cached_graph(directory, identity, command, files, {})
            except ValueError as error:
                assert 'corrupt retained' in str(error)
            else:
                raise AssertionError('corrupt graph retained')
            (directory / 'graph.receipt.json').unlink()
            output.write_text(content.splitlines()[0] + '\n')
            try:
                m.cached_graph(directory, identity, command, files, {})
            except ValueError as error:
                assert 'missing root' in str(error)
            else:
                raise AssertionError('truncated graph recovered')
            output.write_text(content)
            source.write_text('changed during extraction')
            try:
                m.cached_graph(directory, identity, command, files, {})
            except ValueError as error:
                assert 'inputs changed' in str(error)
            else:
                raise AssertionError('mixed input graph certified')
            assert not output.exists() and list(directory.glob('graph-unverified-*.jsonl'))
    print('graph cache replay, atomic-publication recovery, corruption and input-change tests passed')


if __name__ == '__main__':
    main()
