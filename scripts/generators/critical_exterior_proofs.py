#!/usr/bin/env python3
"""Select critical-cylinder proof certificates; Lean checks every selected identity.

The integer coefficient calculations only guide proof selection. The generated
schema applications retain the original alternative order and are verified by
the existing exact scaled-coordinate ring certificates.
"""

from pathlib import Path
import argparse
import re

from scripts.paths import ROOT
SOURCE = ROOT / "Purelib/NumberTheory/Approximation/Dirichlet/Critical/Cylinder/Basic.lean"
UNITS = [(1, 0), (-1, 0), (0, 1), (0, -1)]
DIAGONALS = [(1, 1), (1, -1), (-1, 1), (-1, -1)]
POLYNOMIALS = [((1, -4, 1), "scaledMinus_pos", True),
               ((1, 4, 1), "scaledPlus_pos", True),
               ((5, 0, 1), "scaledFive_pos", False),
               ((6, 4, 2), "scaledSixPlusFour_pos", True),
               ((9, -4, 1), "scaledNineMinusFour_pos", True),
               ((14, 0, 2), "scaledFourteen_pos", False),
               ((6, -8, 2), "scaledSixMinusEight_pos", True),
               ((6, 8, 2), "scaledSixPlusEight_pos", True)]


def choose(left, right):
    a, b = left
    c, d = right
    error = ((2 * a + c) ** 2 + (2 * b + d) ** 2 - 4, 4 * (b * c - a * d), c * c + d * d)
    denominator = ((b + 2 * c) ** 2 + (-a + 2 * d) ** 2 - 4, 4 * (a * c + b * d), a * a + b * b)
    for polynomial, lemma, needs_certificate in POLYNOMIALS:
        for coordinate, actual in (("error", error), ("denominator", denominator)):
            if polynomial == actual:
                premise = "certificate" if needs_certificate else "(value := value)"
                return f"critical_{coordinate} ({lemma} {premise})"
    raise ValueError(f"no certified polynomial for {left}, {right}")


def macro_end(text, start):
    """Leave the following namespace opening untouched, regardless of its scope."""
    match = re.search(r"^open Purelib.NumberTheory.Approximation(?: in)?$", text[start:], re.M)
    if match is None:
        raise ValueError("missing opening after the selected proof schemas")
    return start + match.start()


def proof_end(text, start):
    """Preserve the spacing and scope commands before the next declaration."""
    match = re.search(r"\n\n+(?=/--|open |end(?:\n|$)|section(?:\n|$)|namespace )", text[start:])
    if match is None:
        raise ValueError("missing declaration boundary after a finite proof")
    return start + match.start()


def generated(text):
    # Existing sources before adoption use the search macro; regenerated sources
    # use the two direct schema macros in the same bounded region.
    start = text.index('/-- Prove a critical-cylinder exterior from')
    end = macro_end(text, start)
    macros = ''
    for coordinate in ("error", "denominator"):
        macros += f'''/-- Prove a critical-cylinder exterior from its selected positive polynomial.

The generated finite cases select this schema directly; exact ring checking verifies the coordinate identity.
-/
macro "critical_{coordinate}" positive:term : tactic =>
  `(tactic| first
    | {'left' if coordinate == 'error' else 'right'}
      apply Purelib.Data.Rat.Fraction.Order.Arithmetic.lt_of_sub_pos_direct
      apply Purelib.NumberTheory.Approximation.Dirichlet.Critical.Cylinder.Basic.positive_of_mul_four_positive
      rw [Purelib.NumberTheory.Approximation.Dirichlet.Critical.Cylinder.Basic.{coordinate}_difference_mul_four]
      convert ($positive) using 1 <;> scaled_ring)

'''
    text = text[:start] + macros + text[end:]
    groups = [("unit_unit_coefficients_strictly_exterior", UNITS, UNITS, "leftUnit", "rightUnit"),
              ("unit_diagonal_coefficients_strictly_exterior", UNITS, DIAGONALS, "leftUnit", "rightDiagonal"),
              ("diagonal_unit_coefficients_strictly_exterior", DIAGONALS, UNITS, "leftDiagonal", "rightUnit")]
    groups += [(f"diagonal_diagonal_coefficients_strictly_exterior_left_{i}", [left], DIAGONALS, None,
                "rightDiagonal") for i, left in enumerate(DIAGONALS)]
    for name, lefts, rights, left_premise, right_premise in groups:
        match = re.search(r"\b" + name + r"\s*\n", text)
        if not match:
            raise ValueError(f"missing original theorem: {name}")
        proof = text.index(" := by", match.end()) + len(" := by")
        end = proof_end(text, proof)
        commands = []
        if left_premise:
            commands.append(f"  rcases {left_premise} with rfl | rfl | rfl | rfl <;>")
            commands.append(f"    rcases {right_premise} with rfl | rfl | rfl | rfl")
        else:
            commands.append(f"  rcases {right_premise} with rfl | rfl | rfl | rfl")
        commands += ["  · " + choose(left, right) for left in lefts for right in rights]
        text = text[:proof] + "\n" + "\n".join(commands) + text[end:]
    if len(text.splitlines()) > 1400:
        raise ValueError("generated source exceeds its compact proof-schema budget")
    return text


def generated_two_parameter(text):
    start = text.index('/-- Prove a finite coefficient case lies outside') if '/-- Prove a finite coefficient case lies outside' in text else text.index('/-- Prove a critical-cylinder exterior from')
    end = text.index('/-- The displayed left coefficient', start)
    # Reuse the same two checked schemas with the independent coordinate owner.
    basic_macros = generated(SOURCE.read_text())
    macro_start = basic_macros.index('/-- Prove a critical-cylinder exterior from')
    macros_end = macro_end(basic_macros, macro_start)
    macros = basic_macros[macro_start:macros_end].replace(
        'Cylinder.Basic.', 'Cylinder.TwoParameter.').replace('critical_error', 'two_parameter_error').replace(
        'critical_denominator', 'two_parameter_denominator')
    text = text[:start] + macros + text[end:]
    for family, lefts, rights, premise in (
        ('unit_unit', UNITS, UNITS, 'rightUnit'),
        ('unit_diagonal', UNITS, DIAGONALS, 'rightDiagonal'),
        ('diagonal_unit', DIAGONALS, UNITS, 'rightUnit'),
        ('diagonal_diagonal', DIAGONALS, DIAGONALS, 'rightDiagonal')):
        for index, left in enumerate(lefts):
            name = f'{family}_strictly_exterior_row{index}'
            match = re.search(r'private theorem ' + name + r'\s', text)
            if match is None:
                raise ValueError(f'missing original theorem: {name}')
            proof = re.search(r':=\s*by\n', text[match.end():])
            begin = match.end() + proof.end()
            end = text.index('\n\n/--', begin)
            lines = [f'  rcases {premise} with rfl | rfl | rfl | rfl']
            for right in rights:
                selected = choose(left, right)
                selection = re.fullmatch(r'critical_(error|denominator) \((scaled\w+) (.*)\)', selected)
                coordinate, lemma, argument = selection.groups()
                argument = argument.replace('certificate', coordinate + 'Certificate').replace(
                    'value := value', 'value := ' + coordinate + 'Parameter')
                lines.append(f'  · two_parameter_{coordinate} ({lemma.replace("scaled", "template", 1)} {argument})')
            text = text[:begin] + '\n'.join(lines) + text[end:]
    if len(text.splitlines()) > 2200:
        raise ValueError('generated source exceeds its compact proof-schema budget')
    return text


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path)
    parser.add_argument("--two-parameter", action="store_true")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    source = args.source or (SOURCE.with_name("TwoParameter.lean") if args.two_parameter else SOURCE)
    current = source.read_text()
    expected = generated_two_parameter(current) if args.two_parameter else generated(current)
    if args.output:
        args.output.write_text(expected)
    elif current != expected:
        raise SystemExit("proof selections differ; regenerate with --output")
    else:
        print("Critical-cylinder proof selections are current.")


if __name__ == "__main__":
    main()
