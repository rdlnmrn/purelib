"""Check build coverage, standalone runner isolation and reusable boundaries."""

import copy
from pathlib import Path
import tempfile
import unittest

from scripts.verification import modules, surfaces


def project():
    roots = set(surfaces.PUBLICATION_ROOTS) | {
        'Purelib.Library', 'Purelib.Measure', 'Purelib.Riemann', 'Purelib.Geometry',
        'Purelib.Geometry.Rotations', 'Purelib.Curves', 'Purelib.Examples.All', 'TestPurelib.All',
        'papers.CCL.Chapters.Paper', 'papers.CCL.Chapters.Bridge', 'papers.RFAP.Chapters.Paper',
    }
    graph = {root: set() for root in roots}
    graph['papers.CCL.CCL'] = {'papers.CCL.Chapters.Paper', 'papers.CCL.Chapters.Bridge',
                             'papers.RFAP.Chapters.Paper'}
    graph['TestPurelib.Standalone'] = {'TestPurelib.Support'}
    graph['TestPurelib.Support'] = set()
    libraries = [{'name': 'Project', 'roots': sorted(roots), 'globs': ['TestPurelib.+']}]
    executables = [{'name': 'regression', 'root': 'TestPurelib.Standalone'}]
    return {'lean_lib': libraries, 'lean_exe': executables,
            'defaultTargets': ['Project', 'regression']}, graph


class SurfaceTests(unittest.TestCase):
    def test_nested_worktrees_are_independent_source_inventories(self):
        with tempfile.TemporaryDirectory() as directory:
            parent = Path(directory)
            child = parent / '.worktrees/task'
            for root, name in ((parent, 'Parent'), (child, 'Child')):
                source = root / f'Purelib/{name}.lean'
                source.parent.mkdir(parents=True)
                source.write_text('module\n')
            self.assertEqual(modules.discover(root=parent), (['Purelib/Parent.lean'], []))
            self.assertEqual(modules.discover(root=child), (['Purelib/Child.lean'], []))
            (parent / 'Unclassified.lean').write_text('module\n')
            with self.assertRaisesRegex(ValueError, 'unclassified project Lean sources'):
                modules.discover(root=parent)

    def test_mathematical_sources_cannot_import_regressions(self):
        for owner in ("Purelib.Subject", "Purelib.Examples.Subject", "papers.CCL.Examples",
                      "formalisations.Subject.Examples"):
            with self.subTest(owner=owner):
                graph = {owner: {"TestPurelib.Check"}, "TestPurelib.Check": set()}
                with self.assertRaisesRegex(ValueError, owner + " -> TestPurelib.Check"):
                    surfaces.check_test_dependencies(graph)

    def test_tool_indirection_does_not_hide_a_regression_dependency(self):
        graph = {"Purelib.Examples.Subject": {"scripts.Helper"},
                 "scripts.Helper": {"TestPurelib.Check"}, "TestPurelib.Check": set()}
        with self.assertRaisesRegex(ValueError, "Purelib.Examples.Subject -> scripts.Helper -> TestPurelib.Check"):
            surfaces.check_test_dependencies(graph)

    def test_regressions_can_consume_examples_and_verification_tools_can_run_tests(self):
        graph = {"scripts.Verification": {"TestPurelib.Check"},
                 "TestPurelib.Check": {"Purelib.Examples.Subject"},
                 "Purelib.Examples.Subject": {"Purelib.Subject"}, "Purelib.Subject": set()}
        surfaces.check_test_dependencies(graph)

    def test_standalone_import_closure_counts_without_facade_import(self):
        config, graph = project()
        surfaces.check(config, graph)
        self.assertEqual(graph['TestPurelib.All'], set())

    def test_library_glob_does_not_replace_regression_entrypoint_coverage(self):
        config, graph = project()
        graph['TestPurelib.Unreachable'] = set()
        with self.assertRaisesRegex(ValueError, 'omit regressions.*TestPurelib.Unreachable'):
            surfaces.check(config, graph)
        graph['TestPurelib.All'].add('TestPurelib.Unreachable')
        surfaces.check(config, graph)

    def test_each_library_has_distinct_ownership_and_every_target_is_default(self):
        config, graph = project()
        duplicate = copy.deepcopy(config)
        duplicate['lean_lib'].append({'name': 'Other', 'roots': ['Purelib.Library']})
        duplicate['defaultTargets'].append('Other')
        with self.assertRaisesRegex(ValueError, 'overlapping Lake library owners'):
            surfaces.check(duplicate, graph)
        config['defaultTargets'].remove('regression')
        with self.assertRaisesRegex(ValueError, 'defaultTargets'):
            surfaces.check(config, graph)

    def test_reusable_facade_cannot_acquire_publication_dependencies(self):
        config, graph = project()
        graph['Purelib.Library'].add('papers.CCL.CCL')
        with self.assertRaisesRegex(ValueError, 'reusable facade .* reaches'):
            surfaces.check(config, graph)

    def test_missing_roots_and_imports_fail_instead_of_shrinking_coverage(self):
        config, graph = project()
        config['lean_exe'][0]['root'] = 'TestPurelib.Missing'
        with self.assertRaisesRegex(ValueError, 'missing source pattern'):
            surfaces.check(config, graph)
        with self.assertRaisesRegex(ValueError, 'missing project module'):
            surfaces.closure({'Selected': {'Missing'}}, ['Selected'])


if __name__ == '__main__':
    unittest.main()
