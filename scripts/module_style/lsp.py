#!/usr/bin/env python3
"""Query Lean's language server for source-bound API and module-style evidence."""
from __future__ import annotations

import argparse
import asyncio
from bisect import bisect_right
import json
import os
from pathlib import Path
import subprocess
import sys

from scripts.module_style.core import ROOT, atomic_write, digest, encoded, lex, name, require


def position(starts: list[int], offset: int) -> dict:
    """Return a one-based line and Unicode codepoint column for a source offset."""
    line = bisect_right(starts, offset) - 1
    return {'line': line + 1, 'column': offset - starts[line] + 1}


async def query(args, path: Path, text: str) -> tuple[dict, bool]:
    """Collect a source-bound LSP result without building dependencies or editing."""
    from leanclient.aio import AsyncLeanLSPClient
    from leanclient.aio.convert import range_from_utf16

    relative = path.relative_to(ROOT).as_posix()
    prefix = ROOT / '.lake/core-toolchain'
    receipt = prefix / 'CORE-PREFIX.json'
    server_command = None
    if receipt.is_file():
        # The audited private CLI emits artifacts; the matching upstream
        # executable supplies the language server and its worker protocol.
        upstream = Path(json.loads(receipt.read_text())['base_sysroot']) / 'bin/lean'
        require(upstream.is_file(), 'missing language server for the accepted Core toolchain')
        runner = ROOT / 'scripts/run-lake.sh'
        search_path = subprocess.check_output([str(runner), 'env', 'printenv', 'LEAN_PATH'],
                                              cwd=ROOT, text=True).strip()
        source_path = subprocess.check_output([str(runner), 'env', 'printenv', 'LEAN_SRC_PATH'],
                                              cwd=ROOT, text=True).strip()
        os.environ['LEAN_SYSROOT'] = str(prefix)
        os.environ['LEAN_PATH'] = str(prefix / 'lib/lean') + ':' + search_path
        # The reference loader silently skips modules whose source URI cannot
        # be found, even after a successful waitForILeans barrier.
        os.environ['LEAN_SRC_PATH'] = source_path
        os.environ['LEAN_WORKER_PATH'] = str(upstream)
        os.environ['LAKE'] = str(runner)
        server_command = [str(upstream), '--server', '-Dserver.reportDelayMs=0']
    client = AsyncLeanLSPClient(str(ROOT), max_workers=1, server_command=server_command)

    async def definition_at(line: int, column: int) -> list[dict]:
        """Normalize the origin range left untouched by leanclient's target conversion."""
        locations = await client.goto('definition', relative, line - 1, column - 1, fresh=False)
        for location in locations:
            if 'originSelectionRange' in location:
                location['originSelectionRange'] = range_from_utf16(text.splitlines(), location['originSelectionRange'])
        return locations

    try:
        await client.start()
        if args.mode == 'references':
            await client.wait_for_ileans()
            # leanclient's convenience barrier suppresses transport errors.
            # Require a successful server reply before retaining references.
            await client._transport.request('$/lean/waitForILeans', {}, timeout=client.request_timeout)
        doc = await client.open(relative, wait=False, dependency_build_mode='never')
        # The client's ordinary barrier retries stale imports with builds
        # enabled. A read-only query must report that condition instead.
        await client._barrier_once(relative)
        require(doc.text == text, 'source changed while opening it; run the query again')
        report = await client.diagnostics(relative, fresh=False)
        if args.mode == 'symbols':
            result = await client.document_symbols(relative, fresh=False)
        elif args.mode == 'hover':
            result = await client.hover(relative, args.line - 1, args.column - 1, fresh=False)
        elif args.mode == 'definition':
            result = await definition_at(args.line, args.column)
        elif args.mode == 'references':
            result = await client.references(relative, args.line - 1, args.column - 1, fresh=False)
        else:
            result = []
            starts = [0] + [i + 1 for i, char in enumerate(text) if char == '\n']
            selected = set(args.identifier)
            occurrences = [t for t in lex(text) if t.kind == 'ident' and t.text in selected]
            require(selected <= {t.text for t in occurrences}, 'some selected identifiers do not occur in source code')
            for token in occurrences:
                # Query the final character to select the declaration rather
                # than an earlier namespace component of a qualified name.
                point = position(starts, token.end - 1)
                definitions = await definition_at(point['line'], point['column'])
                result.append({'identifier': token.text, 'source_position': position(starts, token.start),
                               'query_position': point, 'definitions': definitions})
        require(doc.text == text and path.read_text(encoding='utf-8') == text,
                'source changed during query; run it again')
        return {'schema': 1, 'path': relative, 'source_sha256': digest(text), 'mode': args.mode,
                'request_position': ({'line': args.line, 'column': args.column}
                                     if args.mode in {'hover', 'definition', 'references'} else None),
                'positions': {'request_and_snapshot': 'one-based lines and Unicode codepoint columns',
                              'result': ('zero-based lines and UTF-16 columns' if args.mode == 'symbols'
                                         else 'zero-based lines and Unicode codepoint columns'),
                              'diagnostics': 'zero-based lines and Unicode codepoint columns'},
                'diagnostics': report.items, 'fatal_error': report.fatal_error,
                'stale_imports': doc.stale_imports,
                'reference_index_ready': args.mode == 'references', 'result': result}, (
                    report.has_errors or report.fatal_error or doc.stale_imports)
    finally:
        await client.close()


def main(argv=None) -> int:
    """Validate query arguments, then print or atomically save the review evidence."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode', choices=['symbols', 'hover', 'definition', 'references', 'snapshot'])
    parser.add_argument('--file', required=True, type=Path, help='Lean file relative to the repository root')
    parser.add_argument('--line', type=int, help='one-based source line for hover/definition')
    parser.add_argument('--column', type=int, help='one-based Unicode codepoint column')
    parser.add_argument('--identifier', action='append', default=[],
                        help='exact qualified identifier for snapshot; repeat for several names')
    parser.add_argument('--output', type=Path, help='save JSON atomically instead of printing it')
    args = parser.parse_args(argv)
    try:
        path = (ROOT / args.file).resolve()
        require(path.is_relative_to(ROOT) and path.suffix == '.lean', '--file must be a Lean source inside this repository')
        require(args.output is None or args.output.resolve() != path, '--output must not overwrite the Lean source')
        require(args.output is None or args.output.suffix == '.json', '--output must have a .json extension')
        text = path.read_text(encoding='utf-8')
        if args.mode in {'hover', 'definition', 'references'}:
            lines = text.splitlines()
            require(args.line is not None and 1 <= args.line <= len(lines), '--line is required and must be within the source')
            require(args.column is not None and 1 <= args.column <= len(lines[args.line - 1]) + 1,
                    '--column is required and must be within the selected line')
        else:
            require(args.line is None and args.column is None, '--line/--column are only used by hover/definition')
        require(bool(args.identifier) == (args.mode == 'snapshot'), '--identifier is required only for snapshot mode')
        for identifier in args.identifier:
            name(identifier, '--identifier')
            require('.' in identifier, '--identifier must be qualified')
        result, errors = asyncio.run(query(args, path, text))
        if args.output:
            atomic_write(args.output, encoded(result))
        else:
            print(encoded(result), end='')
        return 1 if errors else 0
    except ImportError:
        print('module-style-lsp: use /home/rdl/repos/ccl_lsp/.venv/bin/python (leanclient.aio is required)', file=sys.stderr)
        return 1
    except Exception as error:
        print(f'module-style-lsp: {error}', file=sys.stderr)
        return 1


if __name__ == '__main__':
    raise SystemExit(main())
