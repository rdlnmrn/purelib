#!/usr/bin/env python3
"""Verify that hygiene receipts admit only captured macro binder-name changes."""
import copy
import json
from pathlib import Path
import tempfile
import unittest
from concurrent.futures import ThreadPoolExecutor
from threading import Event
from unittest.mock import patch

from scripts.module_style import contracts as checker
MODULE = 'Example'


def macro(base='x', seed=12, scope=3):
    return ('Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr '
            f'(Lean.Name.mkNum `{base}.«_@».Example {seed}) "_hygCtx") "_hyg") {scope}')


def record():
    expression = {'root': 3, 'nodes': [['sort', 'Lean.Level.zero'], ['const', '`Nat.zero', '[]'],
                                      ['bvar', 0], ['lam', macro(), 0, 2, 'Lean.BinderInfo.default']]}
    return {'name': 'Example.f', 'kind': 'def', 'private': False, 'internal': False,
            'exported': True, 'exposed': True, 'type': expression, 'body': copy.deepcopy(expression),
            'levels': '[]', 'extra': 'safety=Lean.DefinitionSafety.safe'}


def capture(value):
    return {'schema': 2, 'modules': [MODULE], 'lean_toolchain': 'test-pinned-lean', 'module_system': {MODULE: True},
            'declarations': {MODULE: {value['name']: checker.hashed_record(value)}}}


def fixture():
    old = record()
    new = copy.deepcopy(old)
    new['body']['nodes'][3][1] = macro(seed=99, scope=8)
    receipt = {'schema': 1, 'module': MODULE, 'lean_toolchain': 'test-pinned-lean',
               'entries': [{'original': old, 'binder_names': [
                   {'field': 'body', 'node': 3, 'before': macro(), 'after': macro(seed=99, scope=8)}]}]}
    return old, new, receipt


def source_metadata(start=12, end=15, syntax='x', position=12):
    return ('{ entries := [(`_recApp, Lean.DataValue.ofSyntax '
            '(Lean.Syntax.ident (Lean.SourceInfo.original "".toRawSubstring '
            f'{{ byteIdx := {start} }} " ".toRawSubstring {{ byteIdx := {end} }}) '
            f'"{syntax}".toRawSubstring `x [])), '
            f'(`_recAppPos, Lean.DataValue.ofNat {position})] }}')


def pattern_metadata(start=12, end=15, atom='_'):
    location = f'(Lean.SourceInfo.synthetic {{ byteIdx := {start} }} {{ byteIdx := {end} }} false)'
    return ('{ entries := [(`_patWithRef, Lean.DataValue.ofSyntax '
            f'(Lean.Syntax.node {location} `Lean.Parser.Term.hole '
            f'#[Lean.Syntax.atom {location} {json.dumps(atom)}]))] }}')


class OriginSourceCacheTests(unittest.TestCase):
    def setUp(self):
        checker._ORIGIN_SOURCE_RECORDS.clear()

    def test_shared_records_are_immutable_and_keys_include_revision_and_repository(self):
        with tempfile.TemporaryDirectory() as temporary, \
             patch.object(checker.contracts, 'run', return_value='module\nimport Shared\n') as run:
            first = checker.origin_source_record('a' * 40, 'A.lean')
            self.assertEqual(first[1], ('Shared',))
            self.assertIs(first, checker.origin_source_record('a' * 40, 'A.lean'))
            with self.assertRaises(TypeError): first[1][0] = 'Forged'
            checker.origin_source_record('b' * 40, 'A.lean')
            checker.origin_source_record('a' * 40, 'B.lean')
            with patch.object(checker, 'ROOT', Path(temporary)):
                checker.origin_source_record('a' * 40, 'A.lean')
            self.assertEqual(run.call_count, 4)

    def test_concurrent_requests_parse_once_and_failed_reads_can_retry(self):
        started, release = Event(), Event()
        calls = []
        def read(*args):
            calls.append(args)
            started.set()
            self.assertTrue(release.wait(5))
            return 'module\nimport Shared\n'
        with patch.object(checker.contracts, 'run', side_effect=read), \
             patch.object(checker.style, 'inventory', wraps=checker.style.inventory) as inventory, \
             ThreadPoolExecutor(max_workers=8) as pool:
            futures = [pool.submit(checker.origin_source_record, 'a' * 40, 'A.lean') for _ in range(8)]
            self.assertTrue(started.wait(5))
            release.set()
            self.assertEqual(len({future.result() for future in futures}), 1)
            self.assertEqual(len(calls), 1)
            self.assertEqual(inventory.call_count, 1)
        with patch.object(checker.contracts, 'run', side_effect=[RuntimeError('read failed'), 'module\n']) as run:
            with self.assertRaisesRegex(RuntimeError, 'read failed'):
                checker.origin_source_record('b' * 40, 'B.lean')
            self.assertEqual(checker.origin_source_record('b' * 40, 'B.lean')[1], ())
            self.assertEqual(run.call_count, 2)

    def test_graph_mutation_is_local_and_working_pins_are_rechecked(self):
        revision = 'a' * 40
        sources = {'A.lean': 'module\nimport Shared\n', 'B.lean': 'module\nimport Shared\n',
                   'Shared.lean': 'module\n', 'lean-toolchain': 'lean-test', 'lake-manifest.json': '{}'}
        reads = []
        def git(*args):
            if args[1] == 'rev-parse': return revision
            if args[1] == 'ls-tree': return '\n'.join(sources)
            path = args[2].split(':', 1)[1]
            reads.append(path)
            return sources[path]
        with tempfile.TemporaryDirectory() as temporary, patch.object(checker.contracts, 'run', side_effect=git), \
             patch.object(checker, 'ROOT', Path(temporary)):
            root = Path(temporary)
            (root / 'lean-toolchain').write_text('lean-test')
            (root / 'lake-manifest.json').write_text('{}')
            graph, _, _ = checker.origin_revision_graph('A', revision)
            graph['Shared']['imports'].append('Forged')
            graph['A']['source_sha256'] = 'forged'
            next_graph, _, _ = checker.origin_revision_graph('B', revision)
            self.assertEqual(next_graph['Shared']['imports'], [])
            again, _, _ = checker.origin_revision_graph('A', revision)
            self.assertNotEqual(again['A']['source_sha256'], 'forged')
            self.assertEqual(reads.count('Shared.lean'), 1)
            (root / 'lean-toolchain').write_text('changed')
            with self.assertRaisesRegex(ValueError, 'another Lean toolchain'):
                checker.origin_revision_graph('A', revision)
            (root / 'lean-toolchain').write_text('lean-test')
            (root / 'lake-manifest.json').write_text('{"changed":true}')
            with self.assertRaisesRegex(ValueError, 'manifest differs'):
                checker.origin_revision_graph('A', revision)


class OriginTests(unittest.TestCase):
    def test_empty_raw_module_and_metadata_consistency(self):
        metadata = {'module': MODULE, 'module_system': True, 'declaration_count': 0}
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / 'empty.jsonl'
            path.write_text(json.dumps(metadata) + '\n')
            self.assertEqual(checker.raw_declarations(path, MODULE), ({}, True))
            for rows in ([], [metadata, metadata], [dict(metadata, declaration_count=1)],
                         [dict(metadata, module_system=1)]):
                path.write_text(''.join(json.dumps(row) + '\n' for row in rows))
                with self.subTest(rows=rows), self.assertRaises(ValueError):
                    checker.raw_declarations(path, MODULE)

    def fixture(self):
        original = record()
        restored = capture(original)
        restored.update(source_revision='a' * 40, tool_sha256={'driver': 'b' * 64, 'lean': 'c' * 64})
        before = copy.deepcopy(restored)
        before['declarations'][MODULE]['Example.f']['body_sha256'] = 'd' * 64
        graph = {MODULE: {'path': 'Example.lean', 'source_sha256': 'e' * 64,
                          'imports': [], 'project_imports': []}}
        compiler = {'version': 'Lean test', 'sha256': 'f' * 64}
        receipt = {'schema': 1, 'kind': 'original-commit', 'module': MODULE,
                   'source_revision': 'a' * 40, 'lean_toolchain': 'test-pinned-lean',
                   'dependency_manifest_sha256': '1' * 64, 'compiler': compiler,
                   'export_tools': restored['tool_sha256'], 'graph': graph,
                   'original_artifacts': {MODULE: {suffix: '2' * 64 for suffix in checker.ORIGIN_ARTIFACT_SUFFIXES}},
                   'original': {original['name']: original}, 'module_system': True,
                   'original_raw_sha256': checker.style.digest(checker.style.encoded({original['name']: original})),
                   'intermediate_contract_sha256': checker.style.digest(checker.style.encoded(before))}
        return before, restored, receipt, graph, compiler

    def validate(self, before, restored, receipt, graph, compiler):
        from unittest.mock import patch
        with patch.object(checker, 'origin_revision_graph', return_value=(graph, 'test-pinned-lean', '1' * 64)), \
             patch.object(checker, 'origin_compiler_identity', return_value=compiler):
            return checker.validate_origin_receipt(receipt, MODULE, before, restored)

    def test_exact_origin_restoration_retains_intermediate_baseline(self):
        before, restored, receipt, graph, compiler = self.fixture()
        retained = copy.deepcopy(before)
        self.assertEqual(self.validate(before, restored, receipt, graph, compiler), 1)
        self.assertEqual(before, retained)

    def test_origin_rejects_changed_proofs_visibility_and_declaration_sets(self):
        before, restored, receipt, graph, compiler = self.fixture()
        for field, value in [('body_sha256', '3' * 64), ('type_sha256', '3' * 64),
                             ('exported', False), ('exposed', False), ('private', True)]:
            current = copy.deepcopy(restored)
            current['declarations'][MODULE]['Example.f'][field] = value
            with self.subTest(field=field), self.assertRaisesRegex(ValueError, 'current declarations differ'):
                self.validate(before, current, receipt, graph, compiler)
        current = copy.deepcopy(restored)
        current['declarations'][MODULE]['Example.extra'] = current['declarations'][MODULE]['Example.f']
        with self.assertRaisesRegex(ValueError, 'current declarations differ'):
            self.validate(before, current, receipt, graph, compiler)

    def test_origin_rejects_stale_or_incomplete_evidence(self):
        before, restored, receipt, graph, compiler = self.fixture()
        changes = [lambda r: r.__setitem__('source_revision', 'b' * 40),
                   lambda r: r.__setitem__('intermediate_contract_sha256', '3' * 64),
                   lambda r: r['graph'][MODULE].__setitem__('source_sha256', '3' * 64),
                   lambda r: r.__setitem__('lean_toolchain', 'another toolchain'),
                   lambda r: r.__setitem__('original_artifacts', {}),
                   lambda r: r['original_artifacts'][MODULE].__setitem__('.olean.private', None),
                   lambda r: r.__setitem__('original_raw_sha256', '3' * 64),
                   lambda r: r['original']['Example.f'].__setitem__('exported', False)]
        for change in changes:
            mutated = copy.deepcopy(receipt)
            change(mutated)
            with self.subTest(change=change), self.assertRaises(ValueError):
                self.validate(before, restored, mutated, graph, compiler)

    def hygiene_fixture(self):
        before, restored, receipt, graph, compiler = self.fixture()
        old, new, hygiene = fixture()
        self.assertEqual(receipt['original'][old['name']], old)
        restored['declarations'] = capture(new)['declarations']
        receipt.update(schema=2, hygiene=hygiene)
        return before, restored, receipt, graph, compiler

    def test_origin_composes_only_verified_hygiene_with_complete_original(self):
        before, restored, receipt, graph, compiler = self.hygiene_fixture()
        historical = copy.deepcopy(before)
        self.assertEqual(self.validate(before, restored, receipt, graph, compiler), 1)
        self.assertEqual(before, historical)
        self.assertIn('1 verified binder-name/source-position changes',
                      checker.origin_hygiene_summary(receipt))

    def test_origin_hygiene_rejects_semantics_types_visibility_and_auxiliary_changes(self):
        before, restored, receipt, graph, compiler = self.hygiene_fixture()
        for field, value in [('body_sha256', '3' * 64), ('type_sha256', '3' * 64),
                             ('exported', False), ('exposed', False), ('private', True),
                             ('levels_sha256', '3' * 64)]:
            current = copy.deepcopy(restored)
            current['declarations'][MODULE]['Example.f'][field] = value
            with self.subTest(field=field), self.assertRaises(ValueError):
                self.validate(before, current, receipt, graph, compiler)
        for operation in ['add', 'remove']:
            current = copy.deepcopy(restored)
            if operation == 'add':
                current['declarations'][MODULE]['Example.f._proof_1'] = checker.hashed_record(record())
            else:
                current['declarations'][MODULE].clear()
            with self.subTest(operation=operation), self.assertRaises(ValueError):
                self.validate(before, current, receipt, graph, compiler)

    def test_origin_hygiene_rejects_uncovered_declaration_changes(self):
        before, restored, receipt, graph, compiler = self.hygiene_fixture()
        other = record()
        other['name'] = 'Example.unlisted'
        receipt['original'][other['name']] = other
        receipt['original_raw_sha256'] = checker.style.digest(checker.style.encoded(receipt['original']))
        restored['declarations'][MODULE][other['name']] = checker.hashed_record(other)
        self.assertEqual(self.validate(before, restored, receipt, graph, compiler), 2)
        restored['declarations'][MODULE][other['name']]['body_sha256'] = '3' * 64
        with self.assertRaisesRegex(ValueError, 'beyond verified'):
            self.validate(before, restored, receipt, graph, compiler)

    def test_origin_hygiene_cannot_forge_original_or_skip_graph_authentication(self):
        before, restored, receipt, graph, compiler = self.hygiene_fixture()
        changes = [lambda r: r['hygiene']['entries'][0]['original']['body']['nodes'][1].__setitem__(1, '`Nat.one'),
                   lambda r: r['hygiene']['entries'][0]['binder_names'][0].__setitem__('after', macro(base='y')),
                   lambda r: r.__setitem__('original_artifacts', {}),
                   lambda r: r['graph'][MODULE].__setitem__('source_sha256', '3' * 64),
                   lambda r: r.pop('hygiene')]
        for change in changes:
            mutated = copy.deepcopy(receipt)
            change(mutated)
            with self.subTest(change=change), self.assertRaises(ValueError):
                self.validate(before, restored, mutated, graph, compiler)

    def test_origin_hygiene_checks_source_positions_without_ignoring_metadata(self):
        before, restored, receipt, graph, compiler = self.fixture()
        old = receipt['original']['Example.f']
        old['body']['nodes'].append(['mdata', source_metadata(), 3])
        old['body']['root'] = 4
        new = copy.deepcopy(old)
        new['body']['nodes'][4][1] = source_metadata(start=120, end=150, position=120)
        receipt['original_raw_sha256'] = checker.style.digest(checker.style.encoded(receipt['original']))
        receipt.update(schema=2, hygiene={
            'schema': 2, 'module': MODULE, 'lean_toolchain': 'test-pinned-lean',
            'entries': [{'original': copy.deepcopy(old), 'binder_names': [], 'metadata_positions': [
                {'field': 'body', 'node': 4, 'before': old['body']['nodes'][4][1],
                 'after': new['body']['nodes'][4][1]}]}]})
        restored['declarations'] = capture(new)['declarations']
        self.assertEqual(self.validate(before, restored, receipt, graph, compiler), 1)
        new['body']['nodes'][4][1] = source_metadata(start=120, end=150, syntax='another', position=120)
        receipt['hygiene']['entries'][0]['metadata_positions'][0]['after'] = new['body']['nodes'][4][1]
        restored['declarations'] = capture(new)['declarations']
        with self.assertRaisesRegex(ValueError, 'non-position metadata'):
            self.validate(before, restored, receipt, graph, compiler)

    def test_origin_graph_requires_entire_commit_import_closure(self):
        from unittest.mock import patch
        texts = {'Example.lean': 'module\nimport Dependency\npublic def x := Dependency.x\n',
                 'Dependency.lean': 'module\npublic def x := 0\n',
                 'lean-toolchain': 'test-pinned-lean\n', 'lake-manifest.json': '{}\n'}
        revision = 'a' * 40
        def run(*args):
            self.assertEqual(args[0], 'git')
            if args[1] == 'rev-parse': return revision + '\n'
            if args[1] == 'ls-tree': return '\n'.join(texts)
            if args[1] == 'show': return texts[args[2].split(':', 1)[1]]
            self.fail(args)
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            (root / 'lean-toolchain').write_text(texts['lean-toolchain'])
            (root / 'lake-manifest.json').write_text(texts['lake-manifest.json'])
            with patch.object(checker, 'ROOT', root), patch.object(checker.contracts, 'run', side_effect=run):
                graph, _, _ = checker.origin_revision_graph(MODULE, revision)
                self.assertEqual(set(graph), {'Example', 'Dependency'})
                self.assertEqual(graph['Example']['project_imports'], ['Dependency'])
                self.assertEqual(graph['Dependency']['source_sha256'], checker.style.digest(texts['Dependency.lean']))
                (root / 'lake-manifest.json').write_text('{"changed":true}')
                with self.assertRaisesRegex(ValueError, 'dependency manifest'):
                    checker.origin_revision_graph(MODULE, revision)


class HygieneTests(unittest.TestCase):
    def test_exact_scoped_binder_evidence(self):
        old, new, receipt = fixture()
        accepted, count = checker.validate_hygiene_receipt(receipt, MODULE, capture(old), capture(new))
        self.assertEqual(accepted, {(MODULE, 'Example.f', 'body_sha256')})
        self.assertEqual(count, 1)
        self.assertEqual(checker.erased_macro_name(macro()), [('str', 'x')])

    def test_forall_and_let_binder_slots(self):
        for kind, tail in [('forallE', [0, 2, 'Lean.BinderInfo.implicit']), ('letE', [0, 1, 2, True])]:
            old = {'root': 0, 'nodes': [[kind, macro(), *tail]]}
            new = {'root': 0, 'nodes': [[kind, macro(scope=9), *tail]]}
            self.assertEqual(len(checker.binder_changes(old, new, 'type')), 1)

    def test_internal_numeric_name_prefix(self):
        value = ('Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr '
                 '(Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkNum `a.«_@»._internal 0) '
                 '"Example") 123) "_hygCtx") "_hyg") 3')
        self.assertEqual(checker.erased_macro_name(value), [('str', 'a')])

    def test_changed_constant_edges_metadata_and_binder_info_fail(self):
        old, _, _ = fixture()
        for mutate in [lambda e: e['nodes'][1].__setitem__(1, '`Nat.one'),
                       lambda e: e['nodes'][3].__setitem__(3, 1),
                       lambda e: e['nodes'][3].__setitem__(4, 'Lean.BinderInfo.implicit'),
                       lambda e: e.__setitem__('root', 2),
                       lambda e: e['nodes'].append(['mdata', 'changed', 3])]:
            with self.subTest(mutate=mutate):
                changed = copy.deepcopy(old['body'])
                mutate(changed)
                with self.assertRaises(ValueError):
                    checker.binder_changes(old['body'], changed, 'body')
        before = {'root': 0, 'nodes': [['mdata', 'original', 0]]}
        after = {'root': 0, 'nodes': [['mdata', 'changed', 0]]}
        with self.assertRaises(ValueError):
            checker.binder_changes(before, after, 'body')
        before = {'root': 0, 'nodes': [['const', macro(), '[]']]}
        after = {'root': 0, 'nodes': [['const', macro(scope=9), '[]']]}
        with self.assertRaises(ValueError):
            checker.binder_changes(before, after, 'body')

    def test_base_names_and_unscoped_alpha_changes_fail(self):
        for name in [macro(base='y'), '`x', '`y', 'Lean.Name.mkNum `x 1',
                     'Lean.Name.mkNum (Lean.Name.mkStr `x "_hyg") 3',
                     macro() + ' trailing']:
            old, new, receipt = fixture()
            new['body']['nodes'][3][1] = name
            receipt['entries'][0]['binder_names'][0]['after'] = name
            with self.subTest(name=name), self.assertRaises(ValueError):
                checker.validate_hygiene_receipt(receipt, MODULE, capture(old), capture(new))

    def test_forged_old_or_current_records_fail(self):
        old, new, receipt = fixture()
        forged = copy.deepcopy(receipt)
        forged['entries'][0]['original']['body']['nodes'][1][1] = '`Nat.one'
        with self.assertRaisesRegex(ValueError, 'baseline'):
            checker.validate_hygiene_receipt(forged, MODULE, capture(old), capture(new))
        for field in ['body', 'type']:
            forged_current = copy.deepcopy(new)
            forged_current[field]['nodes'][1][1] = '`Nat.one'
            with self.assertRaisesRegex(ValueError, 'current capture'):
                checker.validate_hygiene_receipt(receipt, MODULE, capture(old), capture(forged_current))
        changed_metadata = dict(new, exposed=False)
        with self.assertRaisesRegex(ValueError, 'current capture'):
            checker.validate_hygiene_receipt(receipt, MODULE, capture(old), capture(changed_metadata))

    def test_duplicate_edits_and_wrong_toolchain_fail(self):
        old, new, receipt = fixture()
        receipt['entries'][0]['binder_names'] *= 2
        with self.assertRaisesRegex(ValueError, 'duplicate'):
            checker.validate_hygiene_receipt(receipt, MODULE, capture(old), capture(new))
        old, new, receipt = fixture()
        receipt['lean_toolchain'] = 'different'
        with self.assertRaisesRegex(ValueError, 'toolchain'):
            checker.validate_hygiene_receipt(receipt, MODULE, capture(old), capture(new))

    def test_full_raw_records_verified_before_receipt_creation(self):
        old, new, _ = fixture()
        with tempfile.TemporaryDirectory() as directory:
            paths = [Path(directory) / name for name in ['before.jsonl', 'after.jsonl']]
            for path, value in zip(paths, [old, new]):
                path.write_text(json.dumps({'module': MODULE, 'module_system': True, 'declaration': value}) + '\n')
            receipt = checker.make_hygiene_receipt(MODULE, capture(old), capture(new), *paths)
            self.assertEqual(checker.validate_hygiene_receipt(receipt, MODULE, capture(old), capture(new))[1], 1)
            wrong = copy.deepcopy(old)
            wrong['extra'] = 'different'
            with self.assertRaisesRegex(ValueError, 'captured hashes'):
                checker.make_hygiene_receipt(MODULE, capture(wrong), capture(new), *paths)
            paths[0].write_text(paths[0].read_text() * 2)
            with self.assertRaisesRegex(ValueError, 'duplicate raw'):
                checker.make_hygiene_receipt(MODULE, capture(old), capture(new), *paths)

    def test_source_positions_preserve_all_syntax_and_metadata(self):
        before = source_metadata()
        after = source_metadata(start=101, end=104, position=101)
        self.assertEqual(checker.metadata_position_skeleton(before),
                         checker.metadata_position_skeleton(after))
        old = record()
        old['body']['nodes'].append(['mdata', before, 3])
        old['body']['root'] = 4
        new = copy.deepcopy(old)
        new['body']['nodes'][4][1] = after
        receipt = {'schema': 2, 'module': MODULE, 'lean_toolchain': 'test-pinned-lean',
                   'entries': [{'original': old, 'binder_names': [], 'metadata_positions': [
                       {'field': 'body', 'node': 4, 'before': before, 'after': after}]}]}
        self.assertEqual(checker.validate_hygiene_receipt(
            receipt, MODULE, capture(old), capture(new))[1], 1)
        binders, positions = checker.expression_changes(old['body'], new['body'], 'body')
        self.assertFalse(binders)
        self.assertEqual(len(positions), 1)
        for bad in [after.replace('`x', '`y'), source_metadata(syntax='y'),
                    after.replace('" "', '"  "'), after.replace('_recAppPos', '_other'),
                    after.replace('ofNat 101', 'ofInt 101'),
                    after.replace('Lean.Syntax.ident', 'Lean.Syntax.atom')]:
            bad_current = copy.deepcopy(new)
            bad_current['body']['nodes'][4][1] = bad
            bad_receipt = copy.deepcopy(receipt)
            bad_receipt['entries'][0]['metadata_positions'][0]['after'] = bad
            with self.subTest(bad=bad), self.assertRaises(ValueError):
                checker.validate_hygiene_receipt(
                    bad_receipt, MODULE, capture(old), capture(bad_current))
        # Position-looking text inside an actual syntax string is never erased.
        old_string = source_metadata(syntax='byteIdx := 42')
        new_string = source_metadata(syntax='byteIdx := 43')
        self.assertNotEqual(checker.metadata_position_skeleton(old_string),
                            checker.metadata_position_skeleton(new_string))

    def test_source_position_evidence_cannot_change_edges_or_forge_hashes(self):
        old = {'root': 1, 'nodes': [['const', '`Nat', '[]'], ['mdata', source_metadata(), 0]]}
        new = copy.deepcopy(old)
        new['nodes'][1] = ['mdata', source_metadata(start=30), 1]
        with self.assertRaises(ValueError):
            checker.expression_changes(old, new, 'body')
        for bad in ['{ byteIdx := 42 }', source_metadata().replace('_recApp,', '_other,')]:
            with self.assertRaises(ValueError):
                checker.metadata_position_skeleton(bad)

    def test_pattern_synthetic_positions_preserve_type_body_and_visibility(self):
        old = record()
        for field in ('type', 'body'):
            old[field]['nodes'].append(['mdata', pattern_metadata(), 3])
            old[field]['root'] = 4
        new = copy.deepcopy(old)
        for field in ('type', 'body'):
            new[field]['nodes'][4][1] = pattern_metadata(120, 150)
        with tempfile.TemporaryDirectory() as directory:
            paths = [Path(directory) / name for name in ('before.jsonl', 'after.jsonl')]
            def receipt_for(value):
                for path, row in zip(paths, (old, value)):
                    path.write_text(json.dumps({'module': MODULE, 'module_system': True,
                                                'declaration': row}) + '\n')
                return checker.make_hygiene_receipt(MODULE, capture(old), capture(value), *paths)
            receipt = receipt_for(new)
            self.assertEqual(checker.validate_hygiene_receipt(
                receipt, MODULE, capture(old), capture(new))[1], 2)
            mutations = []
            for field, replacement in [('exported', False), ('exposed', False), ('levels', '[u]')]:
                value = copy.deepcopy(new)
                value[field] = replacement
                mutations.append(value)
            for field in ('type', 'body'):
                for slot, replacement in [(1, ['const', '`Nat.succ', '[]']),
                                          (4, ['mdata', pattern_metadata(120, 150), 2])]:
                    value = copy.deepcopy(new)
                    value[field]['nodes'][slot] = replacement
                    mutations.append(value)
            for bad in [pattern_metadata(120, 150, 'byteIdx := 151'),
                        pattern_metadata(120, 150).replace('false', 'true'),
                        pattern_metadata(120, 150).replace('Term.hole', 'Term.ident'),
                        pattern_metadata(120, 150).replace('_patWithRef', '_other'),
                        pattern_metadata(120, 150).replace('byteIdx := 120', 'byteIdx := -120')]:
                value = copy.deepcopy(new)
                value['body']['nodes'][4][1] = bad
                mutations.append(value)
            for value in mutations:
                with self.subTest(value=value), self.assertRaises(ValueError):
                    receipt_for(value)
        # A byte-index-looking substring in the actual syntax atom stays intact.
        self.assertNotEqual(checker.metadata_position_skeleton(pattern_metadata(atom='byteIdx := 1')),
                            checker.metadata_position_skeleton(pattern_metadata(atom='byteIdx := 2')))


class NamespaceTests(unittest.TestCase):
    def pair(self):
        old = record()
        old['name'] = 'Example._Old.f'
        old['internal'] = True
        old['body']['nodes'][1][1] = '`Example._Old.g'
        new = copy.deepcopy(old)
        new['name'] = 'Example.New.f'
        new['internal'] = False
        new['body']['nodes'][1][1] = '`Example.New.g'
        return old, new

    def check(self, old, new):
        return checker.namespace_record_changes(old, new, MODULE, 'Example._Old', 'Example.New')

    def test_exact_route_and_derived_internal_flag(self):
        old, new = self.pair()
        self.assertEqual(len(self.check(old, new)), 3)
        new['body']['nodes'][3][1] = macro(seed=123)
        self.assertEqual(len(self.check(old, new)), 4)

    def test_only_module_private_wrapper_routes(self):
        old, new = self.pair()
        for row, prefix in [(old, 'Example._Old'), (new, 'Example.New')]:
            row['name'] = '_private.Example.0.' + prefix + '.f'
            row['internal'] = True
        self.check(old, new)
        old['name'] = '_private.Other.0.Example._Old.f'
        new['name'] = '_private.Other.0.Example.New.f'
        with self.assertRaises(ValueError): self.check(old, new)

    def test_substring_and_other_constant_routes_rejected(self):
        for value in ['`Example.NewExtra.g', '`Other.Example.New.g', '`Example.New.h']:
            old, new = self.pair()
            new['body']['nodes'][1][1] = value
            with self.subTest(value=value), self.assertRaises(ValueError): self.check(old, new)

    def test_exposure_kind_levels_and_structure_preserved(self):
        for mutate in [lambda r: r.__setitem__('private', True),
                       lambda r: r.__setitem__('exported', False),
                       lambda r: r.__setitem__('exposed', False),
                       lambda r: r.__setitem__('kind', 'axiom'),
                       lambda r: r.__setitem__('levels', '[`u]'),
                       lambda r: r.__setitem__('extra', 'changed'),
                       lambda r: r.__setitem__('internal', True),
                       lambda r: r['body'].__setitem__('root', 2),
                       lambda r: r['body']['nodes'][1].__setitem__(2, '[Lean.Level.zero]'),
                       lambda r: r['body']['nodes'][3].__setitem__(3, 1)]:
            old, new = self.pair();mutate(new)
            with self.subTest(mutate=mutate), self.assertRaises(ValueError): self.check(old, new)

    def test_literal_and_metadata_strings_not_routed(self):
        for tag in ['lit', 'mdata']:
            old, new = self.pair()
            old['body']['nodes'][1] = [tag, 'Example._Old.g', 0]
            new['body']['nodes'][1] = [tag, 'Example.New.g', 0]
            with self.subTest(tag=tag), self.assertRaises(ValueError): self.check(old, new)

    def test_receipt_binds_complete_maps_and_both_captures(self):
        old, new = self.pair()
        receipt = {'schema': 1, 'kind': 'namespace-route', 'module': MODULE,
                   'lean_toolchain': 'test-pinned-lean',
                   'route': {'from': 'Example._Old', 'to': 'Example.New'},
                   'before_source_sha256': 'a' * 64, 'before_raw_sha256': 'b' * 64,
                   'before_provenance': 'retained pre-rename raw export and source; historical artifacts not retained',
                   'original': {old['name']: old}, 'current': {new['name']: new}, 'module_system': True}
        self.assertEqual(checker.validate_namespace_receipt(receipt, MODULE, capture(old), capture(new)), 3)
        for field in ['original', 'current']:
            forged = copy.deepcopy(receipt)
            row = next(iter(forged[field].values()));row['body']['nodes'][1][1] = '`Nat.one'
            with self.subTest(field=field), self.assertRaises(ValueError):
                checker.validate_namespace_receipt(forged, MODULE, capture(old), capture(new))
        forged = copy.deepcopy(receipt);forged['original'].clear()
        with self.assertRaises(ValueError): checker.validate_namespace_receipt(forged, MODULE, None, capture(new))
        forged = copy.deepcopy(receipt);forged['current']['extra'] = record()
        with self.assertRaises(ValueError): checker.validate_namespace_receipt(forged, MODULE, None, capture(new))



# Four actual immutable schema-2 alias interfaces contain this compiler Name.
LITERAL_ARROW_TYPE_CONTRACTS = json.loads(r'''[
  {
    "name": "Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Basic._PartialCalculus.AutomaticTrace",
    "complete_record_sha256": "64891ee2ef2ac3c6b60cde1811fcc25f5a5ee3cd583b8b43326fe5d2f50b891e",
    "type": {
      "nodes": [
        [
          "const",
          "`Nat",
          "[]"
        ],
        [
          "const",
          "`Purelib.Data.Gaussian.Basic.Canonical",
          "[]"
        ],
        [
          "forallE",
          "Lean.Name.mkNum `a._@._internal._hyg 0",
          0,
          1,
          "Lean.BinderInfo.default"
        ],
        [
          "sort",
          "Lean.Level.succ (Lean.Level.zero)"
        ],
        [
          "forallE",
          "`increment",
          2,
          3,
          "Lean.BinderInfo.default"
        ]
      ],
      "root": 4
    }
  },
  {
    "name": "Purelib.Data.CCL.Encoding.Cylinder.Safe.Projective._MachineContraction.ProjectiveRealizes",
    "complete_record_sha256": "3a208c875b25b04801a617fa84974b1c56603928c52af1c9c34d7ee35e07fef7",
    "type": {
      "nodes": [
        [
          "const",
          "`List",
          "[Lean.Level.zero]"
        ],
        [
          "const",
          "`Purelib.Data.CCL.Encoding.Block.Basic._Redundant.Block",
          "[]"
        ],
        [
          "app",
          0,
          1
        ],
        [
          "const",
          "`Purelib.Geometry.Projective.Line.Basic._CCLGeometryGaussianProjective.Proj",
          "[]"
        ],
        [
          "sort",
          "Lean.Level.zero"
        ],
        [
          "forallE",
          "Lean.Name.mkNum `a._@._internal._hyg 0",
          3,
          4,
          "Lean.BinderInfo.default"
        ],
        [
          "forallE",
          "`blocks",
          2,
          5,
          "Lean.BinderInfo.default"
        ]
      ],
      "root": 6
    }
  },
  {
    "name": "Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State._PartialLogQuotient.Division.Progress",
    "complete_record_sha256": "9b420960fe3d169fe19660eade9dc16ce412ad81da01ba0cff9624bbf2a3f8a7",
    "type": {
      "nodes": [
        [
          "const",
          "`Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed",
          "[]"
        ],
        [
          "const",
          "`Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State.State",
          "[]"
        ],
        [
          "bvar",
          0
        ],
        [
          "app",
          1,
          2
        ],
        [
          "bvar",
          1
        ],
        [
          "app",
          1,
          4
        ],
        [
          "sort",
          "Lean.Level.succ (Lean.Level.zero)"
        ],
        [
          "forallE",
          "Lean.Name.mkNum `a._@._internal._hyg 0",
          5,
          6,
          "Lean.BinderInfo.default"
        ],
        [
          "forallE",
          "Lean.Name.mkNum `a._@._internal._hyg 0",
          3,
          7,
          "Lean.BinderInfo.default"
        ],
        [
          "forallE",
          "`denominator",
          0,
          8,
          "Lean.BinderInfo.implicit"
        ]
      ],
      "root": 9
    }
  },
  {
    "name": "Purelib.Approximation.Gaussian.Name.Coherent.Refinement.LogarithmState._PartialLogQuotient.Log.Progress",
    "complete_record_sha256": "fe3944add1615dd3c5d8539b2ee02067b980c4ccde86e29933da8cfbbb13fbb5",
    "type": {
      "nodes": [
        [
          "const",
          "`Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed",
          "[]"
        ],
        [
          "const",
          "`Purelib.Approximation.Gaussian.Name.Coherent.Refinement.LogarithmState.State",
          "[]"
        ],
        [
          "bvar",
          0
        ],
        [
          "app",
          1,
          2
        ],
        [
          "bvar",
          1
        ],
        [
          "app",
          1,
          4
        ],
        [
          "sort",
          "Lean.Level.zero"
        ],
        [
          "forallE",
          "Lean.Name.mkNum `a._@._internal._hyg 0",
          5,
          6,
          "Lean.BinderInfo.default"
        ],
        [
          "forallE",
          "Lean.Name.mkNum `a._@._internal._hyg 0",
          3,
          7,
          "Lean.BinderInfo.default"
        ],
        [
          "forallE",
          "`target",
          0,
          8,
          "Lean.BinderInfo.implicit"
        ]
      ],
      "root": 9
    }
  }
]''')


class LiteralCompilerNameTests(unittest.TestCase):
    def test_literal_and_quoted_scope_delimiters_are_same_complete_name(self):
        literal = 'Lean.Name.mkNum `a._@._internal._hyg 0'
        quoted = 'Lean.Name.mkNum `a.«_@»._internal._hyg 0'
        expected = [('str', 'a'), ('str', '_@'), ('str', '_internal'),
                    ('str', '_hyg'), ('num', 0)]
        self.assertEqual(checker.name_components(literal), expected)
        self.assertEqual(checker.name_components(quoted), expected)
        self.assertEqual(checker.erased_macro_name(literal), [('str', 'a')])

    def test_actual_four_full_types_retain_every_other_node_and_slot(self):
        self.assertEqual(len(LITERAL_ARROW_TYPE_CONTRACTS), 4)
        for contract in LITERAL_ARROW_TYPE_CONTRACTS:
            with self.subTest(name=contract['name']):
                old = contract['type']
                new = copy.deepcopy(old)
                count = 0
                for node in new['nodes']:
                    if node[0] == 'forallE' and node[1] == 'Lean.Name.mkNum `a._@._internal._hyg 0':
                        node[1] = 'Lean.Name.mkNum `a._@._internal._hyg 1'
                        count += 1
                changes = checker.binder_changes(old, new, 'type')
                self.assertGreater(count, 0)
                self.assertEqual(len(changes), count)
                for change in changes:
                    self.assertEqual(change['field'], 'type')
                    self.assertEqual(old['nodes'][change['node']][2:],
                                     new['nodes'][change['node']][2:])

    def test_mutated_actual_type_parameters_and_universes_reject(self):
        for contract in LITERAL_ARROW_TYPE_CONTRACTS:
            old = contract['type']
            new = copy.deepcopy(old)
            index = next(i for i, node in enumerate(new['nodes']) if node[0] == 'const')
            new['nodes'][index][2] = '[Lean.Level.succ (Lean.Level.zero)]' if old['nodes'][index][2] != '[Lean.Level.succ (Lean.Level.zero)]' else '[]'
            with self.subTest(name=contract['name']), self.assertRaises(ValueError):
                checker.binder_changes(old, new, 'type')

    def test_malformed_literal_delimiters_reject(self):
        for token in ['_@tail', '_@@', '_@/', '_@:', '_@«scope»', '_@._internal.._hyg']:
            with self.subTest(token=token), self.assertRaises(ValueError):
                checker.name_components('Lean.Name.mkNum `a.' + token + ' 0')

    def test_constant_identities_never_inherit_binder_hygiene(self):
        old = {'nodes': [['const', 'Lean.Name.mkNum `a._@._internal._hyg 0', '[]']], 'root': 0}
        new = copy.deepcopy(old)
        new['nodes'][0][1] = 'Lean.Name.mkNum `a._@._internal._hyg 1'
        with self.assertRaises(ValueError):
            checker.binder_changes(old, new, 'body')

if __name__ == '__main__':
    unittest.main()
