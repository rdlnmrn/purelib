#!/usr/bin/env python3
"""Focused finite regression tests for the untrusted sewing producer."""

import re
from fractions import Fraction
from itertools import permutations
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest


from scripts.paths import ROOT
from scripts.generators import sewing as GENERATOR

FIXTURES = ROOT / "scripts/test/fixtures/sewing"


def leaves(tree):
    return [tree[0]] if len(tree) == 1 else leaves(tree[0]) + leaves(tree[1])


class SewingGeneratorTests(unittest.TestCase):
    @staticmethod
    def rendered_text(text):
        """Compare semantic source fragments independently of reviewed layout."""
        text = re.sub(r"\\\n[ \t]*", "", text)
        text = text.replace("_root_.Purelib.", "").replace("Purelib.", "")
        return " ".join(text.split())

    def assertRenderedIn(self, member, container, msg=None):
        if isinstance(member, str) and isinstance(container, str):
            member, container = self.rendered_text(member), self.rendered_text(container)
        return super().assertIn(member, container, msg)

    def assertRenderedNotIn(self, member, container, msg=None):
        if isinstance(member, str) and isinstance(container, str):
            member, container = self.rendered_text(member), self.rendered_text(container)
        return super().assertNotIn(member, container, msg)

    def check_forest(self, faces, expected_patches):
        patches = GENERATOR.forest(faces)
        self.assertEqual(len(patches), expected_patches)
        self.assertEqual(sorted(index for patch in patches for index in leaves(patch["tree"])), list(range(len(faces))))
        for patch in patches:
            boundary = patch["boundary"]
            self.assertEqual(len(boundary), len(leaves(patch["tree"])) + 2)
            self.assertTrue(all(edge[1] == boundary[(i + 1) % len(boundary)][0] for i, edge in enumerate(boundary)))
        for first, left in enumerate(patches):
            for right in patches[first + 1:]:
                self.assertFalse(any((b, a) in right["boundary"] for a, b in left["boundary"]))
        return patches

    def test_empty(self):
        self.check_forest([], 0)

    def test_disconnected(self):
        self.check_forest([[0, 1, 2], [3, 4, 5]], 2)

    def test_retained_cuts(self):
        patches = self.check_forest([[0, 1, 2], [0, 2, 1]], 1)
        self.assertEqual(GENERATOR.cancellation_counts(patches), (2, 0))

    def test_annulus(self):
        _, faces = GENERATOR.read_mesh(FIXTURES / "annulus.json")
        patches = self.check_forest(faces, 1)
        self.assertEqual(GENERATOR.cancellation_counts(patches), (1, 16))
        self.assertEqual(patches, GENERATOR.forest(faces))

    def test_primitive_assembly_retains_mismatch_and_unused_slots(self):
        faces = [[0, 1, 2], [1, 0, 2]]
        tree = ((0,), (1,), 0, 0)
        sample = GENERATOR.primitive_assembly(faces, tree, [[0, 2, 5], [10, 13, 17]])
        self.assertEqual(sample["values"], [0, 2, 5, 2, 5, 9])
        self.assertEqual(sample["charges"], [25])
        self.assertEqual(sample["contacts"], [[0, 0, 1, 1, 0, 1, 25]])
        self.assertEqual(sample["boundary"], [(1, 2), (2, 0), (0, 5), (5, 1)])
        self.assertNotEqual(sample["values"][0], sample["values"][4])
        self.assertEqual(sample["faces"][1], {"source": 1, "triangle": [1, 0, 5], "errors": [0, -5, 0],
                                            "terms": [[0], [-5], [0]], "depth": 1, "charge": 25, "allowance": 25})
        self.assertEqual((sample["total_allowance"], sample["squared_errors"]), (25, 25))
        self.assertEqual(sample["boundary_readings"], [[1, 2, 0, 0, 1, 2, 3, 0, 0], [2, 0, 0, 0, 2, 0, -5, 0, 0],
                                                     [0, 5, 1, 1, 1, 2, 4, 5, 100], [5, 1, 1, 1, 2, 0, -7, 0, 100]])
        exact = GENERATOR.primitive_assembly(faces, tree, [[0, 2, 5], [10, 8, 15]])
        self.assertEqual(exact["charges"], [0])
        self.assertEqual((exact["total_allowance"], exact["squared_errors"]), (0, 0))
        for values in [[[0, 2]], [[0, 2, 5], [True, 1, 2]]]:
            with self.assertRaises(ValueError):
                GENERATOR.primitive_assembly(faces, tree, values)

    def test_primitive_assembly_face_translations_do_not_change_charges(self):
        _, faces = GENERATOR.read_mesh(FIXTURES / "torus.json")
        patches = GENERATOR.forest(faces)
        values = [[face * 7 + corner * corner for corner in range(3)] for face in range(len(faces))]
        shifted = [[value + 13 * (face + 1) for value in row] for face, row in enumerate(values)]
        for patch in patches:
            original = GENERATOR.primitive_assembly(faces, patch["tree"], values)
            translated = GENERATOR.primitive_assembly(faces, patch["tree"], shifted)
            self.assertEqual(original["charges"], translated["charges"])
            self.assertEqual(original["faces"], translated["faces"])
            self.assertEqual(original["boundary_readings"], translated["boundary_readings"])
            self.assertEqual(original["contacts"], translated["contacts"])
            self.assertEqual(len(original["charges"]) + 1, len(leaves(patch["tree"])))
            shift = 13 * (leaves(patch["tree"])[0] + 1)
            self.assertEqual(translated["values"], [value + shift for value in original["values"]])
            self.assertTrue(any(charge > 0 for charge in original["charges"]))

    def test_face_traces_cover_deep_sewing_and_actual_readings(self):
        _, faces = GENERATOR.read_mesh(FIXTURES / "torus.json")
        values = [[11 * face + corner * corner + 2 * corner - 7 for corner in range(3)] for face in range(len(faces))]
        shifted = [[value + 19 * face for value in row] for face, row in enumerate(values)]
        for patch in GENERATOR.forest(faces, right_nested=True):
            sample = GENERATOR.primitive_assembly(faces, patch["tree"], values)
            translated = GENERATOR.primitive_assembly(faces, patch["tree"], shifted)
            self.assertEqual(sample["faces"], translated["faces"])
            self.assertEqual([trace["source"] for trace in sample["faces"]], leaves(patch["tree"]))
            self.assertGreater(max(trace["depth"] for trace in sample["faces"]), 2)
            self.assertGreater(sample["squared_errors"], 0)
            self.assertEqual(len(sample["contacts"]) + 1, len(sample["faces"]))
            self.assertEqual(sample["mismatches"], [contact[-1] for contact in sample["contacts"]])
            self.assertEqual(sample["contacts"], translated["contacts"])
            for left, first, last, right, right_first, right_last, mismatch in sample["contacts"]:
                self.assertEqual((faces[left][first], faces[left][last]),
                                 (faces[right][right_last], faces[right][right_first]))
                self.assertEqual(mismatch, (values[left][last] - values[left][first] +
                                            values[right][right_last] - values[right][right_first]) ** 2)
            for trace in sample["faces"]:
                actual = [sample["values"][index] for index in trace["triangle"]]
                local = values[trace["source"]]
                self.assertEqual([sample["labels"][index] for index in trace["triangle"]], faces[trace["source"]])
                self.assertEqual(trace["errors"], [actual[i] - actual[0] - local[i] + local[0] for i in range(3)])
                self.assertEqual(trace["allowance"], trace["depth"] * trace["charge"])
                for error, terms in zip(trace["errors"], trace["terms"]):
                    self.assertEqual(len(terms), trace["depth"])
                    self.assertEqual(sum(terms), error)
                    self.assertLessEqual(sum(term * term for term in terms), trace["charge"])
                    self.assertLessEqual(error * error, trace["allowance"])
            self.assertEqual(sample["total_allowance"], sum(t["depth"] * t["charge"] for t in sample["faces"]))
            self.assertEqual(sample["squared_errors"], sum(sum(e * e for e in t["errors"][1:]) for t in sample["faces"]))
            self.assertLessEqual(sample["squared_errors"], 2 * sample["total_allowance"])
            self.assertEqual(len(sample["boundary_readings"]), len(sample["boundary"]))
            for edge, reading in zip(sample["boundary"], sample["boundary_readings"]):
                start, finish, position, source, first, last, increment, error, allowance = reading
                self.assertEqual((start, finish), edge)
                self.assertEqual(sample["faces"][position]["source"], source)
                self.assertEqual([sample["faces"][position]["triangle"][i] for i in (first, last)], list(edge))
                self.assertEqual(increment, values[source][last] - values[source][first])
                self.assertEqual(error, sample["values"][finish] - sample["values"][start] - increment)
                self.assertLessEqual(error * error, allowance)

    def test_deep_constant_faces_have_no_error_floor(self):
        _, faces = GENERATOR.read_mesh(FIXTURES / "annulus.json")
        for patch in GENERATOR.forest(faces, right_nested=True):
            sample = GENERATOR.primitive_assembly(faces, patch["tree"], [[7 * face] * 3 for face in range(len(faces))])
            self.assertEqual((sample["total_allowance"], sample["squared_errors"]), (0, 0))
            self.assertTrue(all(t["errors"] == [0, 0, 0] for t in sample["faces"]))

    def test_geometry_only_sewing_amplification(self):
        self.assertEqual(GENERATOR.sewing_shape((0,)), [0, 0, 1, 0])
        pair = ((0,), (1,), 0, 0)
        self.assertEqual(GENERATOR.sewing_shape(pair), [1, 2, 2, 8])
        self.assertEqual(GENERATOR.sewing_shape((pair, (2,), 0, 0)), [1, 36, 3, 216])
        self.assertEqual(GENERATOR.sewing_shape(((2,), pair, 0, 0)), [2, 36, 3, 432])
        self.assertEqual(GENERATOR.sewing_shape((pair, ((2,), (3,), 0, 0), 0, 0)), [2, 70, 4, 1120])

    def test_whole_tree_local_mismatch_bound_and_requested_budget(self):
        inherited_matters = False
        for fixture in ["sewing-annulus.json", "sewing-torus.json"]:
            _, faces = GENERATOR.read_mesh(FIXTURES / fixture.removeprefix("sewing-"))
            values = [[11 * face + corner * corner + 2 * corner - 7 for corner in range(3)] for face in range(len(faces))]
            for right_nested in [False, True]:
                for patch in GENERATOR.forest(faces, right_nested=right_nested):
                    sample = GENERATOR.primitive_assembly(faces, patch["tree"], values)
                    depth, factor, count, amplification = sample["shape"]
                    maximum = max(sample["mismatches"], default=0)
                    total = sum(sample["charges"])
                    inherited_matters |= total > maximum
                    self.assertEqual(count, len(sample["faces"]))
                    self.assertEqual(depth, max(t["depth"] for t in sample["faces"]))
                    self.assertEqual(amplification, 2 * count * depth * factor)
                    self.assertLessEqual(total, factor * maximum)
                    self.assertLessEqual(sample["squared_errors"], 2 * count * depth * total)
                    self.assertLessEqual(sample["squared_errors"], amplification * maximum)
                    for target in [Fraction(1), Fraction(1, 1000), Fraction(17, 3)]:
                        tolerance = target / (amplification + 1)
                        self.assertGreater(tolerance, 0)
                        self.assertLess(amplification * tolerance, target)
        self.assertTrue(inherited_matters, "regression must detect omission of accumulated seam charges")

    def test_dual_paths(self):
        _, faces = GENERATOR.read_mesh(FIXTURES / "annulus.json")
        paths = GENERATOR.dual_paths(faces)
        self.assertEqual(paths, GENERATOR.dual_paths(faces))
        self.assertTrue(GENERATOR.oriented_unique(faces))
        boundaries = [[(a, b), (b, c), (c, a)] for a, b, c in faces]
        for target, path in enumerate(paths):
            first = 0
            for following, first_position, next_position in path:
                a, b = boundaries[first][first_position]
                self.assertEqual(boundaries[following][next_position], (b, a))
                first = following
            self.assertEqual(first, target)

    def test_boundary_word_preserves_occurrences_and_order(self):
        generators, word = GENERATOR.boundary_word([(0, 1), (1, 2), (2, 1), (1, 0), (0, 3)])
        self.assertEqual(generators, [(0, 3), (0, 1), (1, 2)])
        self.assertEqual(word, [2, 3, -3, -2, 1])
        generators, word = GENERATOR.boundary_word([(0, 1), (0, 1), (1, 0), (1, 0)])
        self.assertEqual(generators, [(0, 1), (0, 1)])
        self.assertEqual(word, [1, 2, -1, -2])

    def test_signature_is_order_sensitive_and_retains_open_total(self):
        total, matrix = GENERATOR.word_signature(2, [1, 2, -1, -2])
        self.assertEqual(total, [0, 0])
        self.assertEqual(matrix, [[0, 2], [-2, 0]])
        self.assertEqual(GENERATOR.word_signature(2, [1, -1, 2, -2]), ([0, 0], [[0, 0], [0, 0]]))
        self.assertEqual(GENERATOR.word_signature(2, [1, 2]), ([1, 1], [[0, 1], [-1, 0]]))
        self.assertEqual(GENERATOR.word_signature(0, []), ([], []))
        for invalid in [0, 3, -3, True]:
            with self.assertRaises(ValueError):
                GENERATOR.word_signature(2, [invalid])

    def test_chord_intervals_preserve_exact_cyclic_occurrences(self):
        chords = GENERATOR.chord_intervals([False, False], [1, 2, -1, -2])
        self.assertEqual([(item["first"], item["inside_length"], item["interval"]) for item in chords],
                         [(0, 1, [1, 2, -1]), (1, 1, [2, -1, -2])])
        self.assertEqual([item["paired"] for item in chords], [[0, 1], [-1, 0]])
        self.assertEqual(GENERATOR.chord_intervals([], []), [])
        for mask, word in [([False], [1]), ([True], [1, -1]), ([False], [1, 1, -1]),
                           ([False], [True, -1]), ([0], [1, -1])]:
            with self.assertRaises(ValueError):
                GENERATOR.chord_intervals(mask, word)

    def test_chord_rows_with_physical_boundary_and_all_cyclic_orders(self):
        mask = [False, False, True]
        physical_seen = wrapped_seen = False
        for word in permutations([1, -1, 2, -2, 3]):
            word = list(word)
            _, matrix = GENERATOR.word_signature(3, word)
            paired, _ = GENERATOR.integral_pairing(mask, matrix)
            for chord in GENERATOR.chord_intervals(mask, word):
                total, _ = GENERATOR.word_signature(3, chord["interval"])
                self.assertEqual(chord["paired"], paired[chord["index"]])
                self.assertEqual(total, [left + right for left, right in zip(chord["paired"], chord["physical"])])
                physical_seen |= any(chord["physical"])
                wrapped_seen |= chord["first"] + len(chord["interval"]) > len(word)
        self.assertTrue(physical_seen)
        self.assertTrue(wrapped_seen)

    def test_annulus_word_signature(self):
        _, faces = GENERATOR.read_mesh(FIXTURES / "annulus.json")
        boundary = self.check_forest(faces, 1)[0]["boundary"]
        generators, word = GENERATOR.boundary_word(boundary)
        total, matrix = GENERATOR.word_signature(len(generators), word)
        self.assertEqual(total, [1] * 16 + [0])
        self.assertEqual(len(word), 18)
        reconstructed = [generators[letter - 1] if letter > 0 else tuple(reversed(generators[-letter - 1])) for letter in word]
        self.assertEqual(reconstructed, boundary)
        for row in range(len(generators)):
            for column in range(len(generators)):
                self.assertEqual(matrix[row][column], -matrix[column][row])

    def test_closed_torus_has_nonzero_balanced_area_matrix(self):
        count, faces = GENERATOR.read_mesh(FIXTURES / "torus.json")
        self.assertEqual(count, 9)
        self.assertTrue(GENERATOR.oriented_unique(faces))
        self.assertIsNotNone(GENERATOR.dual_paths(faces))
        patches = self.check_forest(faces, 1)
        self.assertEqual(GENERATOR.cancellation_counts(patches), (10, 0))
        generators, word = GENERATOR.boundary_word(patches[0]["boundary"])
        total, matrix = GENERATOR.word_signature(len(generators), word)
        self.assertEqual(total, [0] * 10)
        self.assertTrue(any(value != 0 for row in matrix for value in row))
        self.assertTrue(all(value % 2 == 0 for row in matrix for value in row))

    def test_integral_pairing_retains_mixed_boundary_terms(self):
        _, faces = GENERATOR.read_mesh(FIXTURES / "annulus.json")
        generators, word = GENERATOR.boundary_word(GENERATOR.forest(faces)[0]["boundary"])
        total, matrix = GENERATOR.word_signature(len(generators), word)
        paired, remaining = GENERATOR.integral_pairing([value != 0 for value in total], matrix)
        self.assertTrue(all(value == 0 for row in paired for value in row))
        self.assertEqual(remaining, matrix)
        self.assertTrue(any(remaining[row][-1] != 0 for row in range(16)))
        self.assertEqual(GENERATOR.integral_pairing([False, False], [[0, 2], [-2, 0]]),
                         ([[0, 1], [-1, 0]], [[0, 0], [0, 0]]))
        with self.assertRaises(ValueError):
            GENERATOR.integral_pairing([False, False], [[0, 1], [-1, 0]])
        with self.assertRaises(ValueError):
            GENERATOR.integral_pairing([False], [[0, 2], [-2, 0]])

    def test_dual_disconnected_and_empty(self):
        self.assertIsNone(GENERATOR.dual_paths([]))
        self.assertIsNone(GENERATOR.dual_paths([[0, 1, 2], [3, 4, 5]]))

    def test_cycle_rows_and_dual_coordinates_have_the_handle_row_signs(self):
        matrices = [[], [[0, 1, 2], [-1, 0, 3], [-2, -3, 0]],
                    [[0, -1, 2, 3], [1, 0, -1, -2], [-2, 1, 0, 0], [-3, 2, 0, 0]]]
        for matrix in matrices:
            result = GENERATOR.unit_pivot_reduction(matrix)
            rows = GENERATOR.cycle_rows(result)
            count = len(matrix)
            for index in range(count):
                unit = [int(index == j) for j in range(count)]
                self.assertEqual(rows[index], GENERATOR.dual_values(result, unit, backward=True))
            values = [7 * i - 11 for i in range(count)]
            dual = GENERATOR.dual_values(result, values)
            original = [sum(entry * value for entry, value in zip(row, values)) for row in matrix]
            actual = [sum(weight * value for weight, value in zip(row, original)) for row in rows]
            for first, last in result["pivots"]:
                self.assertEqual(actual[first], dual[last])
                self.assertEqual(actual[last], -dual[first])

    def test_unit_reduction_closed_torus(self):
        _, faces = GENERATOR.read_mesh(FIXTURES / "torus.json")
        generators, word = GENERATOR.boundary_word(GENERATOR.forest(faces)[0]["boundary"])
        _, matrix = GENERATOR.word_signature(len(generators), word)
        paired, _ = GENERATOR.integral_pairing([False] * len(generators), matrix)
        result = GENERATOR.unit_pivot_reduction(paired)
        self.assertEqual(result, GENERATOR.unit_pivot_reduction(paired))
        self.assertEqual(result["status"], "normal-form")
        self.assertEqual(len(result["pivots"]), 1)
        self.assertEqual(len(result["available"]), 8)
        first, last = result["pivots"][0]
        self.assertEqual(result["matrix"], [[int(i == first and j == last) - int(i == last and j == first)
                                           for j in range(10)] for i in range(10)])

    def test_weighted_period_rows_include_coefficient_amplification(self):
        self.assertEqual(GENERATOR.weighted_period_rows([], [], [], []), [])
        self.assertEqual(GENERATOR.weighted_period_rows([[]], [], [], []),
                         [{"sample": (0, 0), "mass": 0, "charge": 0}])
        rows = [[0, 0], [20, -10], [-20, 10], [10**30, -10**30]]
        result = GENERATOR.weighted_period_rows(rows, [3, -2], [1, 4], [2, 5])
        self.assertEqual(result[0], {"sample": (0, 0), "mass": 0, "charge": 0})
        self.assertEqual(result[1], {"sample": (80, -20), "mass": 1000, "charge": 2600})
        self.assertEqual(result[2], {"sample": (-80, 20), "mass": 1000, "charge": 2600})
        self.assertEqual(result[3]["sample"], (5 * 10**30, -3 * 10**30))
        self.assertGreater(result[1]["charge"], sum([2, 5]))
        for args in [([[1]], [1, 2], [0, 0], [1, 1]), ([[1]], [1], [0], [-1]),
                     ([[True]], [1], [0], [1]), ([[1]], [1], [], [1])]:
            with self.assertRaises(ValueError):
                GENERATOR.weighted_period_rows(*args)
    def test_unit_reduction_two_handles_and_negative_orientation(self):
        matrix = [[0, -1, 2, 3], [1, 0, -1, -2], [-2, 1, 0, 0], [-3, 2, 0, 0]]
        result = GENERATOR.unit_pivot_reduction(matrix)
        self.assertEqual(result["status"], "normal-form")
        self.assertEqual(len(result["pivots"]), 2)
        self.assertEqual(result["pivots"][0], (1, 0))
        values = [5, -2, 7, 11]
        original = values[:]
        for (first, last), stage in zip(result["pivots"], result["stages"]):
            values = [value + stage["left"][i] * values[first] + stage["right"][i] * values[last]
                      for i, value in enumerate(values)]
        for (first, last), stage in reversed(list(zip(result["pivots"], result["stages"]))):
            values = [value - stage["left"][i] * values[first] - stage["right"][i] * values[last]
                      for i, value in enumerate(values)]
        self.assertEqual(values, original)

    def test_unit_reduction_reports_exact_unresolved_residual(self):
        result = GENERATOR.unit_pivot_reduction([[0, 2], [-2, 0]])
        self.assertEqual(result["status"], "inconclusive-no-unit")
        self.assertEqual(result["pivots"], [])
        self.assertEqual(result["available"], [0, 1])
        self.assertEqual(result["unresolved"], [(0, 1, 2), (1, 0, -2)])
        self.assertEqual(GENERATOR.unit_pivot_reduction([])["status"], "normal-form")
        self.assertEqual(GENERATOR.unit_pivot_reduction([[0]])["status"], "normal-form")
        for invalid in [[[1]], [[0, 1], [1, 0]], [[0, 1]], [[False]]]:
            with self.assertRaises(ValueError):
                GENERATOR.unit_pivot_reduction(invalid)

    def test_dual_values_preserve_pairing_and_have_an_explicit_inverse(self):
        matrix = [[0, 1, 2], [-1, 0, 3], [-2, -3, 0]]
        reduction = GENERATOR.unit_pivot_reduction(matrix)
        left, right = [2, -1, 3], [5, 4, -2]
        self.assertEqual(GENERATOR.dual_values(reduction, left), [-7, 5, 3])
        self.assertEqual(GENERATOR.dual_values(reduction, right), [11, 0, -2])
        for values in (left, right):
            self.assertEqual(GENERATOR.dual_values(reduction, GENERATOR.dual_values(reduction, values), backward=True), values)
        self.assertEqual(sum(matrix[i][j] * left[i] * right[j] for i in range(3) for j in range(3)), -55)
        for invalid in [[1], [False, 2, 3]]:
            with self.assertRaises(ValueError):
                GENERATOR.dual_values(reduction, invalid)

    def test_interlaced_word_reconnection_order(self):
        word = [1, 3, 2, 4, -1, -3, -2, -4]
        step = GENERATOR.interlaced_surgery(word, 0, 1)
        self.assertEqual([step[key] for key in ("u", "v", "w", "x")], [[3], [4], [-3], [-4]])
        self.assertEqual(step["after"], [3, -4, -3, 4])
        rotated = GENERATOR.interlaced_surgery(word[3:] + word[:3], 0, 1)
        self.assertEqual(rotated["before"], word)
        self.assertEqual(rotated["after"], step["after"])
        matrix = GENERATOR.word_signature(4, word)[1]
        reduction = GENERATOR.unit_pivot_reduction([[entry // 2 for entry in row] for row in matrix])
        self.assertEqual(len(reduction["pivots"]), 2)
        surgeries = GENERATOR.word_surgeries(4, word, reduction["pivots"])
        self.assertEqual(surgeries[-1]["after"], [])
        for surgery, stage in zip(surgeries, reduction["stages"]):
            self.assertEqual(surgery["split_matrix"], [[2 * entry for entry in row] for row in stage["matrix"]])

    def test_three_generator_words_exhaustively_match_integer_reduction(self):
        nonzero = 0
        for raw in permutations([1, -1, 2, -2, 3, -3]):
            word = list(raw)
            _, matrix = GENERATOR.word_signature(3, word)
            reduction = GENERATOR.unit_pivot_reduction([[entry // 2 for entry in row] for row in matrix])
            self.assertEqual(reduction["status"], "normal-form")
            nonzero += bool(reduction["pivots"])
            surgeries = GENERATOR.word_surgeries(3, word, reduction["pivots"])
            for surgery, stage in zip(surgeries, reduction["stages"]):
                self.assertEqual(surgery["split_matrix"], [[2 * entry for entry in row] for row in stage["matrix"]])
                self.assertEqual(len(surgery["before"]), len(surgery["after"]) + 4)
        self.assertEqual(nonzero, 480)

    def test_generated_surgeries_compare_automatic_interlacing(self):
        count, faces = GENERATOR.read_mesh(FIXTURES / "torus.json")
        output = GENERATOR.render(count, faces, GENERATOR.forest(faces))
        self.assertIn("import Purelib.Topology.Surface.Word.PairedWord", output)
        self.assertRenderedIn("wordSurgery0Selected := selectWord", output)
        self.assertRenderedIn("match wordSurgery0Selected with", output)
        self.assertRenderedIn("selected.cut.u = wordSurgery0.u", output)
        self.assertRenderedIn("selected.cut.x = wordSurgery0.x", output)
        self.assertRenderedIn("wordSurgery0Normal := normalizeWord", output)
        self.assertRenderedIn("InterlacedWord.afterIntegral wordSurgery0", output)
        self.assertRenderedIn("wordSurgery0Normal.trace.terminalWord", output)

    def test_surgery_rejects_bad_occurrences_orientation_and_balance(self):
        for word, first, last in [([1, 2, -1, -2], 0, 0), ([1, -1, 2, -2], 0, 1),
                                   ([1, 2, -1, -2], 1, 0), ([1, 2, -1], 0, 1),
                                   ([1, 1, 2, -1, -2], 0, 1)]:
            with self.assertRaises(ValueError):
                GENERATOR.interlaced_surgery(word, first, last)
        with self.assertRaises(ValueError):
            GENERATOR.word_surgeries(3, [1, 2, -1, -2, 3], [(0, 1)])
        with self.assertRaises(ValueError):
            GENERATOR.word_surgeries(2, [1, 2, -1, -2, 1, -1], [(0, 1)])

    def test_generated_clients_use_evidence_bearing_checkers(self):
        count, faces = GENERATOR.read_mesh(FIXTURES / "annulus.json")
        output = GENERATOR.render(count, faces, GENERATOR.forest(faces))
        self.assertRenderedIn("SewingForest.checkTrees", output)
        self.assertRenderedIn("DualConnection.checkPaths", output)
        self.assertRenderedIn("SewingForest.SinglePolygon.edgePairing singlePolygon meshNonloop", output)
        self.assertRenderedIn("checkCutPairing singlePolygon", output)
        self.assertRenderedIn("checkCutPairing connectedAutomatic", output)
        self.assertRenderedIn("sample.boundaryArea + sample.jumpSum + sample.defectSum", output)
        self.assertRenderedIn("ProjectedEdgePairing.jumpPaths pairing polygon.patch.cut.closed", output)
        self.assertRenderedIn("CutPath.increment primitive entry.paths.start.cutEdges", output)
        self.assertRenderedIn("edge ∈ original ∨ edge.reverse ∈ original", output)
        self.assertRenderedIn("def expectedWordMatrix", output)
        self.assertRenderedIn("ProjectedEdgePairing.boundaryWord cutPairs", output)
        self.assertRenderedIn("def cutIntegralPairing :=", output)
        self.assertRenderedIn("expectedRemainingMatrix", output)
        self.assertRenderedIn("checkNormalForm cutIntegralPairing.paired reductionPivots", output)
        self.assertRenderedIn("cutNormalForm.reduction.backward_forward", output)
        self.assertRenderedIn("IntegralPairing.wordNormalForm cutIntegralPairing", output)
        self.assertRenderedIn("CutBoundaryWord.pairedLetters cutWord", output)
        self.assertRenderedIn("IntegralPairing.normalForm_paired cutIntegralPairing", output)
        self.assertRenderedIn("def expectedDualLeft", output)
        self.assertRenderedIn("def expectedWeightedRows", output)
        self.assertRenderedIn("coefficients.charge errors", output)
        self.assertRenderedIn("ChordCycleBank.build word polygon.patch.cut.closed", output)
        self.assertRenderedIn("cycleRoutes.sample integral primitive wordSample.values", output)
        self.assertRenderedIn("resampling changed fixed cycle paths or reused stale primitive readings", output)
        self.assertRenderedIn("cutNormalForm.reduction.dualForward", output)
        self.assertRenderedIn("NormalFormArea.build normal.normal wordSample.values", output)
        self.assertRenderedIn("filtering physical-boundary occurrences changed the paired matrix", output)
        self.assertRenderedNotIn("checkedNormalForm.toOption.get", output)
        self.assertRenderedNotIn("paired_zero_of_unique", output)
        self.assertRenderedIn("word extraction dropped or reused a signed occurrence", output)
        self.assertRenderedIn("checkGeneratedWord", output)
        self.assertRenderedIn("wordSample.correction", output)
        self.assertRenderedIn("ProjectedEdgePairing.boundaryWord_provenance pairing", output)
        self.assertRenderedIn("AreaSample.errorTotal_bounded wordSample wordBound", output)
        self.assertRenderedIn("PrimitivePoint.Bounded step.error pairBound ∧ Purelib.Riemann.Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded step.drift totalBound", output)
        self.assertRenderedIn("ChordCycleBank.Sample.errors_bounded cycleBank nonnegative wordBound index", output)
        self.assertRenderedIn("AreaSample.step_drift_bounded wordSample polygon.patch.cut.closed", output)
        self.assertRenderedIn("AreaSample.correction_accurate wordSample polygon.patch.cut.closed", output)
        self.assertRenderedIn("normSq step.correction ≤ weight * pairBound", output)
        self.assertRenderedIn("normSq wordSample.correction < areaTarget", output)
        self.assertRenderedIn("NormalFormErrorBounds.errors_bounded cycleRows rowProfile", output)
        self.assertRenderedIn("NormalFormErrorBounds.errors_accurate cycleRows rowProfile", output)
        self.assertRenderedIn("NormalFormErrorBounds.first_accurate cycleRows evaluated rowProfile", output)
        self.assertRenderedIn("NormalFormErrorBounds.last_accurate cycleRows evaluated rowProfile", output)
        for endpoint in ["first", "last"]:
            self.assertRenderedIn(
                f"NormalFormErrorBounds.{endpoint}_sample_bounded "
                "(jumpBound := fun _ => (2 : AreaCoordinate)) "
                "(errorBound := fun index => (rowProfile.coefficients.get index).mass * totalBound) "
                "cycleRows evaluated sampledRows sampledBound rowErrors pair member",
                " ".join(output.split()),
            )
        self.assertRenderedNotIn("ofTrees?", output)
        self.assertRenderedNotIn("ofPaths?", output)

    def test_punctured_torus_has_handles_with_physical_chord_terms(self):
        count, faces = GENERATOR.read_mesh(FIXTURES / "punctured-torus.json")
        patches = GENERATOR.forest(faces)
        self.assertEqual(count, 9)
        self.assertEqual(len(patches), 1)
        self.assertEqual(GENERATOR.cancellation_counts(patches), (8, 3))
        generators, word = GENERATOR.boundary_word(patches[0]["boundary"])
        totals, matrix = GENERATOR.word_signature(len(generators), word)
        one_sided = [value != 0 for value in totals]
        paired, _ = GENERATOR.integral_pairing(one_sided, matrix)
        reduction = GENERATOR.unit_pivot_reduction(paired)
        self.assertEqual(reduction["status"], "normal-form")
        self.assertEqual(len(reduction["pivots"]), 1)
        physical = [[0] * len(generators) for _ in generators]
        for chord in GENERATOR.chord_intervals(one_sided, word):
            physical[chord["index"]] = chord["physical"]
        rows = GENERATOR.cycle_rows(reduction)
        first, last = reduction["pivots"][0]
        self.assertTrue(any(sum(rows[row][index] * physical[index][column] for index in range(len(generators)))
                            for row in (first, last) for column in range(len(generators))))

    def test_generated_energy_area_uses_conjugacy_and_paid_quadratic_errors(self):
        for fixture in ["sewing-torus.json", "sewing-annulus.json", "sewing-punctured-torus.json"]:
            count, faces = GENERATOR.read_mesh(FIXTURES / fixture.removeprefix("sewing-"))
            output = GENERATOR.render(count, faces, GENERATOR.forest(faces))
            self.assertRenderedIn("DualMagnitude.build normal.normal.reduction", output)
            self.assertRenderedIn("CutBoundaryWord.AreaSample.values_bounded energyWord pairing rfl endpoints", output)
            self.assertRenderedIn("NormalFormArea.conjugate energyEvaluated (Purelib.Topology.Surface.Cut.GeneratorBounds.CutBoundaryWord.AreaSample.values_conjugate energyWord", output)
            self.assertRenderedIn("corrected.accurate energyEvaluated budget bounded conjugate firstBound lastBound", output)
            self.assertRenderedIn("budget.combine referenceArea energyEvaluated.area corrected.area remainder", output)
            self.assertRenderedIn("the area regression did not exercise the product of both perturbations", output)
            self.assertRenderedIn("energyRows pair.1 - (energyCycles.physical pair.1).right", output)
            self.assertRenderedIn("integral.remaining row column) energyWord.values", output)

    def test_degenerate_mesh_does_not_claim_projected_nondegeneracy(self):
        faces = [[0, 0, 1]]
        output = GENERATOR.render(2, faces, GENERATOR.forest(faces))
        self.assertRenderedIn("def singlePolygon", output)
        self.assertRenderedNotIn("theorem meshNonloop", output)
        self.assertRenderedNotIn("def checkCutPairing", output)

    def test_nonmanifold_connectivity_is_insufficient(self):
        faces = [[0, 1, 2], [1, 0, 3], [0, 1, 4]]
        self.assertIsNotNone(GENERATOR.dual_paths(faces))
        self.assertFalse(GENERATOR.oriented_unique(faces))
        patches = self.check_forest(faces, 2)
        self.assertRenderedNotIn("def singlePolygon", GENERATOR.render(5, faces, patches))

    def test_generated_imports_use_current_sources_and_shared_openings(self):
        import re
        for fixture in ["sewing-annulus.json", "sewing-torus.json", "sewing-punctured-torus.json"]:
            count, faces = GENERATOR.read_mesh(FIXTURES / fixture.removeprefix("sewing-"))
            output = GENERATOR.render(count, faces, GENERATOR.forest(faces))
            modules = re.findall(r"^import (\S+)$", output, re.M)
            self.assertEqual(len(modules), len(set(modules)))
            for module in modules:
                self.assertTrue((ROOT / (module.replace(".", "/") + ".lean")).is_file(), module)
            openings = re.findall(r"^open (.+)$", output, re.M)
            self.assertEqual(len(openings), len(set(openings)))
            self.assertTrue(all(not opening.endswith(" in") for opening in openings))
            from scripts.module_style.core import lex
            protected = [token for token in lex(output) if token.kind in ("string", "comment", "doc")]
            code_lines = []
            offset = 0
            for line in output.splitlines():
                if not any(token.start < offset + len(line) + 1 and offset < token.end
                           for token in protected):
                    code_lines.append(line)
                offset += len(line) + 1
            self.assertLessEqual(max(map(len, code_lines)), 120)
            self.assertEqual(output.count("\nopen Purelib\n"), 1)
            self.assertTrue(all(opening == "Purelib" or opening.startswith("_root_.Purelib.")
                                for opening in openings))
            self.assertRegex(output, r"/-- Replay finite sewing,[^\n]+ -/\npublic def main")
            self.assertNotIn("namespace _", output)
            self.assertNotIn("_public", output)

    def test_layout_preserves_strings_and_existing_documentation(self):
        from scripts.module_style.core import lex
        from unittest.mock import patch

        for mesh in ("annulus", "torus", "punctured-torus"):
            count, faces = GENERATOR.read_mesh(FIXTURES / (mesh + ".json"))
            with patch.object(GENERATOR, "format_lean", side_effect=lambda source: source):
                original = GENERATOR.render(count, faces, GENERATOR.forest(faces))
            output = GENERATOR.format_lean(original)
            self.assertEqual([token.text for token in lex(original) if token.kind == "string"],
                             [token.text for token in lex(output) if token.kind == "string"])
            tokens = lex(output)
            self.assertFalse(any(left.kind == right.kind == "doc"
                                 for left, right in zip(tokens, tokens[1:])))
            self.assertNotIn("\\\n", output)

    def test_check_mode_rejects_stale_output(self):
        with tempfile.TemporaryDirectory(prefix="ccl-sewing-test-") as temporary:
            output = Path(temporary) / "Generated.lean"
            command = [sys.executable, "-m", "scripts.generators.sewing", "--input", str(FIXTURES / "annulus.json"), "--output", str(output)]
            subprocess.run(command, check=True, capture_output=True)
            subprocess.run(command + ["--check"], check=True, capture_output=True)
            output.write_text(output.read_text() + "\n")
            result = subprocess.run(command + ["--check"], capture_output=True)
            self.assertNotEqual(result.returncode, 0)

    def test_invalid_index_rejected(self):
        with tempfile.TemporaryDirectory(prefix="ccl-sewing-test-") as temporary:
            source = Path(temporary) / "Invalid.json"
            source.write_text('{"vertex_count": 3, "faces": [[0, 1, 3]]}')
            with self.assertRaises(ValueError):
                GENERATOR.read_mesh(source)


if __name__ == "__main__":
    unittest.main()
