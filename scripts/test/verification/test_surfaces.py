"""Check build coverage, standalone runner isolation and reusable boundaries."""

import copy
import unittest

from scripts.verification import surfaces


def project():
    roots = set(surfaces.PUBLICATION_ROOTS) | {
        'Purelib.Library', 'Purelib.Measure', 'Purelib.Riemann', 'Purelib.Geometry',
        'Purelib.Geometry.Rotations', 'Purelib.Curves', 'Purelib.Examples.All', 'Test.All',
        'papers.CCL.Chapters.Paper', 'papers.CCL.Chapters.Bridge', 'papers.RFAP.Chapters.Paper',
    }
    graph = {root: set() for root in roots}
    graph['papers.CCL.CCL'] = {'papers.CCL.Chapters.Paper', 'papers.CCL.Chapters.Bridge',
                             'papers.RFAP.Chapters.Paper'}
    graph['Test.Standalone'] = {'Test.Support'}
    graph['Test.Support'] = set()
    libraries = [{'name': 'Project', 'roots': sorted(roots), 'globs': ['Test.+']}]
    executables = [{'name': 'regression', 'root': 'Test.Standalone'}]
    return {'lean_lib': libraries, 'lean_exe': executables,
            'defaultTargets': ['Project', 'regression']}, graph


class SurfaceTests(unittest.TestCase):
    def test_standalone_import_closure_counts_without_facade_import(self):
        config, graph = project()
        surfaces.check(config, graph)
        self.assertEqual(graph['Test.All'], set())

    def test_library_glob_does_not_replace_regression_entrypoint_coverage(self):
        config, graph = project()
        graph['Test.Unreachable'] = set()
        with self.assertRaisesRegex(ValueError, 'omit regressions.*Test.Unreachable'):
            surfaces.check(config, graph)
        graph['Test.All'].add('Test.Unreachable')
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
        config['lean_exe'][0]['root'] = 'Test.Missing'
        with self.assertRaisesRegex(ValueError, 'missing source pattern'):
            surfaces.check(config, graph)
        with self.assertRaisesRegex(ValueError, 'missing project module'):
            surfaces.closure({'Selected': {'Missing'}}, ['Selected'])


if __name__ == '__main__':
    unittest.main()
