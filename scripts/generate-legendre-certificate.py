#!/usr/bin/env python3
"""Generate exact rational data for an explicit Legendre A- or B-period.

This program is an *untrusted* certificate-data generator.  It follows one
square-root branch numerically only to choose rational boxes.  Every value it
emits is then recomputed with ``fractions.Fraction`` and is intended to be
checked by Lean before it is used by a theorem.

The generated data deliberately contains no floating-point values.  Decimal
square roots select dyadic centres; all residuals, variation bounds,
reciprocals, and aggregate bounds are exact rationals.  JSON output is useful
for inspection; Lean output contains short independently checked chunks for
the final trusted build.
"""

from __future__ import annotations

import argparse
import json
import os
import tempfile
from dataclasses import dataclass, replace
from decimal import Decimal, localcontext, ROUND_HALF_EVEN
from fractions import Fraction
from functools import cache
from math import isqrt
from pathlib import Path
from typing import Iterable, Iterator, Sequence


Q = Fraction


@dataclass(frozen=True)
class GaussianQ:
    re: Q
    im: Q

    def __add__(self, other: "GaussianQ") -> "GaussianQ":
        return GaussianQ(self.re + other.re, self.im + other.im)

    def __sub__(self, other: "GaussianQ") -> "GaussianQ":
        return GaussianQ(self.re - other.re, self.im - other.im)

    def __neg__(self) -> "GaussianQ":
        return GaussianQ(-self.re, -self.im)

    def __mul__(self, other: "GaussianQ") -> "GaussianQ":
        return GaussianQ(
            self.re * other.re - self.im * other.im,
            self.re * other.im + self.im * other.re,
        )

    def scale(self, scalar: Q) -> "GaussianQ":
        return GaussianQ(scalar * self.re, scalar * self.im)

    def norm_sq(self) -> Q:
        return self.re * self.re + self.im * self.im

    def reciprocal(self) -> "GaussianQ":
        denominator = self.norm_sq()
        if denominator == 0:
            raise ZeroDivisionError("zero Gaussian reciprocal")
        return GaussianQ(self.re / denominator, -self.im / denominator)


ZERO = GaussianQ(Q(0), Q(0))
ONE = GaussianQ(Q(1), Q(0))
LAMBDA = GaussianQ(Q(1, 4), Q(2))
STATIONARY_SWITCH_COUNT = 2
SEMANTIC_ALLOWANCE_FACTOR = Q(4)
GENERATED_PATH_CLEARANCE_FLOOR = Q(1, 262144)
SCHEDULE_SLACK = Q(1, 256)


@dataclass(frozen=True)
class Leg:
    name: str
    start: GaussianQ
    finish: GaussianQ


@dataclass(frozen=True)
class Cell:
    position: int
    leg: str
    index: int
    count: int
    start: GaussianQ
    finish: GaussianQ
    radicand: GaussianQ
    root_center: GaussianQ
    root_half_width: Q
    transport_root_half_width: Q
    coefficient: GaussianQ
    root_residual_sq: Q
    radicand_variation_sq: Q
    rouche_left_sq: Q
    rouche_remainder_sq: Q
    root_norm_sq_lower: Q
    coefficient_error_sq: Q
    transport_coefficient_error_sq: Q
    movement_sq: Q

    def contribution(self) -> GaussianQ:
        return self.coefficient * (self.finish - self.start)

    def weighted_allowance(self) -> Q:
        return (
            self.movement_sq
            * SEMANTIC_ALLOWANCE_FACTOR
            * self.coefficient_error_sq
        )


def at_transport_width(cell: Cell) -> Cell:
    """Recompute width-dependent diagnostics for the transport square."""

    width = cell.transport_root_half_width
    center_norm_sq = cell.root_center.norm_sq()
    return replace(
        cell,
        root_half_width=width,
        root_norm_sq_lower=box_norm_sq_lower(cell.root_center, width),
        rouche_left_sq=Q(4) * center_norm_sq * width * width,
        rouche_remainder_sq=Q(3)
        * (cell.root_residual_sq + Q(4) * width**4 + cell.radicand_variation_sq),
        coefficient_error_sq=cell.transport_coefficient_error_sq,
    )


def point(re: Q | int, im: Q | int) -> GaussianQ:
    return GaussianQ(Q(re), Q(im))


def legendre_polynomial(z: GaussianQ) -> GaussianQ:
    return z * (z - ONE) * (z - LAMBDA)


def a_cycle_legs() -> list[Leg]:
    """The raw A-cycle geometry in its actual oriented traversal order."""

    left_anchor = point(Q(-1, 2), Q(-1, 2))
    right_anchor = point(Q(1, 8), Q(3, 2))
    return [
        Leg("forward-bottom", left_anchor, point(Q(1, 8), Q(-1, 2))),
        Leg("forward-right", point(Q(1, 8), Q(-1, 2)), right_anchor),
        Leg("right-boundary-bottom", right_anchor, point(Q(3, 8), Q(3, 2))),
        Leg("right-boundary-right", point(Q(3, 8), Q(3, 2)), point(Q(3, 8), Q(5, 2))),
        Leg("right-boundary-top", point(Q(3, 8), Q(5, 2)), point(Q(1, 8), Q(5, 2))),
        Leg("right-boundary-left", point(Q(1, 8), Q(5, 2)), right_anchor),
        Leg("backward-left", right_anchor, point(Q(1, 8), Q(-1, 2))),
        Leg("backward-bottom", point(Q(1, 8), Q(-1, 2)), left_anchor),
        Leg("left-boundary-bottom", left_anchor, point(Q(1, 16), Q(-1, 2))),
        Leg("left-boundary-right", point(Q(1, 16), Q(-1, 2)), point(Q(1, 16), Q(1, 2))),
        Leg("left-boundary-top", point(Q(1, 16), Q(1, 2)), point(Q(-1, 2), Q(1, 2))),
        Leg("left-boundary-left", point(Q(-1, 2), Q(1, 2)), left_anchor),
    ]


# Effective per-leg depths of the canonical prepared A-cycle at refinement
# zero.  These combine the measured outer schedules in
# ExplicitLegendrePreparedPeriods with the four successful inner-bank depths:
# forward connector, right boundary, reversed connector, and left boundary.
A_CYCLE_CELL_COUNTS = (128, 512, 64, 128, 64, 256, 512, 128, 512, 512, 512, 512)

# The prepared implementation first subdivides each raw leg into these outer
# segments, then applies one common inner mesh to each resulting segment.
# Keeping the two levels visible is mathematically significant: Lean's dense
# Horner variation bound is recomputed on the much shorter outer segment.
A_CYCLE_OUTER_COUNTS = (4, 16, 4, 4, 4, 8, 16, 4, 4, 4, 4, 4)
A_CYCLE_INNER_COUNTS = (32, 32, 16, 32, 16, 32, 32, 32, 128, 128, 128, 128)


def b_cycle_legs() -> list[Leg]:
    """The canonical B connector followed on the opposite sheet in reverse."""

    left_anchor = point(Q(-1, 2), Q(-1, 2))
    right_anchor = point(Q(15, 16), Q(-1, 2))
    return [
        Leg("forward-horizontal", left_anchor, right_anchor),
        Leg("forward-stationary", right_anchor, right_anchor),
        Leg("backward-stationary", right_anchor, right_anchor),
        Leg("backward-horizontal", right_anchor, left_anchor),
    ]


# The scheduled outer refinement keeps the canonical stationary segment once
# in each direction.  Every retained outer segment then receives the measured
# inner depth three, giving 128 + 8 + 8 + 128 moving cells.
B_CYCLE_CELL_COUNTS = (128, 8, 8, 128)
B_CYCLE_OUTER_COUNTS = (16, 1, 1, 16)
B_CYCLE_INNER_COUNTS = (8, 8, 8, 8)


# Active output configuration.  The A values preserve the historical command
# line exactly; ``--cycle b`` switches all geometry and Lean module names
# before any certificate calculation begins.
CYCLE_LEGS: tuple[Leg, ...] = tuple(a_cycle_legs())
CYCLE_CELL_COUNTS = A_CYCLE_CELL_COUNTS
CYCLE_OUTER_COUNTS = A_CYCLE_OUTER_COUNTS
CYCLE_INNER_COUNTS = A_CYCLE_INNER_COUNTS
FIRST_SHEET_LEG_COUNT = 6
EXPECTED_WORKING_SEGMENT_COUNT = 76
ALLOW_STATIONARY_GENERATED_CELLS = False
FLIP_ROOT_AT_SHEET_SWITCH = False
EXPLICIT_CERTIFICATE_PREFIX = "ExplicitLegendreGeneratedCertificate"
EXPLICIT_SEGMENT_CERTIFICATE_PREFIX = "ExplicitLegendreGeneratedSegmentCertificate"
GENERATED_DATA_MODULE = "GeneratedLegendreCertificateData"
GENERATED_SEMANTICS_MODULE = "GeneratedLegendreCertificateSemantics"
GENERATED_LEG_LIST = "generatedALegs"


def configure_cycle(cycle: str) -> None:
    global CYCLE_LEGS
    global CYCLE_CELL_COUNTS, CYCLE_OUTER_COUNTS, CYCLE_INNER_COUNTS
    global FIRST_SHEET_LEG_COUNT, EXPECTED_WORKING_SEGMENT_COUNT
    global ALLOW_STATIONARY_GENERATED_CELLS
    global FLIP_ROOT_AT_SHEET_SWITCH
    global EXPLICIT_CERTIFICATE_PREFIX, EXPLICIT_SEGMENT_CERTIFICATE_PREFIX
    global GENERATED_DATA_MODULE, GENERATED_SEMANTICS_MODULE
    global GENERATED_LEG_LIST, LEAN_NAMESPACE

    if cycle == "a":
        CYCLE_LEGS = tuple(a_cycle_legs())
        CYCLE_CELL_COUNTS = A_CYCLE_CELL_COUNTS
        CYCLE_OUTER_COUNTS = A_CYCLE_OUTER_COUNTS
        CYCLE_INNER_COUNTS = A_CYCLE_INNER_COUNTS
        FIRST_SHEET_LEG_COUNT = 6
        EXPECTED_WORKING_SEGMENT_COUNT = 76
        ALLOW_STATIONARY_GENERATED_CELLS = False
        FLIP_ROOT_AT_SHEET_SWITCH = False
        EXPLICIT_CERTIFICATE_PREFIX = "ExplicitLegendreGeneratedCertificate"
        EXPLICIT_SEGMENT_CERTIFICATE_PREFIX = (
            "ExplicitLegendreGeneratedSegmentCertificate"
        )
        GENERATED_DATA_MODULE = "GeneratedLegendreCertificateData"
        GENERATED_SEMANTICS_MODULE = "GeneratedLegendreCertificateSemantics"
        GENERATED_LEG_LIST = "generatedALegs"
        LEAN_NAMESPACE = "CCL.Riemann.ExplicitLegendreGeneratedCertificate"
        return
    if cycle == "b":
        CYCLE_LEGS = tuple(b_cycle_legs())
        CYCLE_CELL_COUNTS = B_CYCLE_CELL_COUNTS
        CYCLE_OUTER_COUNTS = B_CYCLE_OUTER_COUNTS
        CYCLE_INNER_COUNTS = B_CYCLE_INNER_COUNTS
        FIRST_SHEET_LEG_COUNT = 2
        EXPECTED_WORKING_SEGMENT_COUNT = 34
        ALLOW_STATIONARY_GENERATED_CELLS = True
        FLIP_ROOT_AT_SHEET_SWITCH = True
        EXPLICIT_CERTIFICATE_PREFIX = "ExplicitLegendreGeneratedBCertificate"
        EXPLICIT_SEGMENT_CERTIFICATE_PREFIX = (
            "ExplicitLegendreGeneratedBSegmentCertificate"
        )
        GENERATED_DATA_MODULE = "GeneratedLegendreBCertificateData"
        GENERATED_SEMANTICS_MODULE = "GeneratedLegendreBCertificateSemantics"
        GENERATED_LEG_LIST = "generatedBLegs"
        LEAN_NAMESPACE = "CCL.Riemann.ExplicitLegendreGeneratedBCertificate"
        return
    raise ValueError(f"unknown Legendre cycle: {cycle}")


def decimal_of_fraction(value: Q) -> Decimal:
    return Decimal(value.numerator) / Decimal(value.denominator)


def decimal_complex_sqrt(value: GaussianQ, precision: int) -> tuple[Decimal, Decimal]:
    """Principal complex square root, using Decimal rather than binary float."""

    with localcontext() as context:
        context.prec = precision
        a = decimal_of_fraction(value.re)
        b = decimal_of_fraction(value.im)
        modulus = (a * a + b * b).sqrt()
        real = ((modulus + a) / Decimal(2)).sqrt()
        imaginary_magnitude = ((modulus - a) / Decimal(2)).sqrt()
        imaginary = -imaginary_magnitude if b < 0 else imaginary_magnitude
        return +real, +imaginary


def decimal_distance_sq(
    left: tuple[Decimal, Decimal], right: tuple[Decimal, Decimal]
) -> Decimal:
    re = left[0] - right[0]
    im = left[1] - right[1]
    return re * re + im * im


def dyadic_round(value: Decimal, bits: int) -> Q:
    scale = 1 << bits
    integer = int((value * Decimal(scale)).to_integral_value(rounding=ROUND_HALF_EVEN))
    return Q(integer, scale)


def tracked_root_center(
    radicand: GaussianQ,
    previous: GaussianQ | None,
    bits: int,
    precision: int,
) -> GaussianQ:
    principal = decimal_complex_sqrt(radicand, precision)
    if previous is not None:
        previous_decimal = (
            decimal_of_fraction(previous.re),
            decimal_of_fraction(previous.im),
        )
        negative = (-principal[0], -principal[1])
        if decimal_distance_sq(negative, previous_decimal) < decimal_distance_sq(
            principal, previous_decimal
        ):
            principal = negative
    return GaussianQ(dyadic_round(principal[0], bits), dyadic_round(principal[1], bits))


def dyadic_gaussian(value: GaussianQ, bits: int) -> GaussianQ:
    """Round an exact rational Gaussian value to one fixed dyadic grid."""

    scale = 1 << bits

    def round_fraction(coordinate: Q) -> Q:
        numerator = coordinate.numerator * scale
        quotient, remainder = divmod(abs(numerator), coordinate.denominator)
        twice_remainder = 2 * remainder
        if twice_remainder > coordinate.denominator or (
            twice_remainder == coordinate.denominator and quotient % 2 == 1
        ):
            quotient += 1
        if numerator < 0:
            quotient = -quotient
        return Q(quotient, scale)

    return GaussianQ(round_fraction(value.re), round_fraction(value.im))


def dyadic_ceil(value: Q, bits: int) -> Q:
    """Smallest multiple of 2^-bits which is at least ``value``."""

    if value < 0:
        raise ValueError("dyadic_ceil expects a nonnegative rational")
    scale = 1 << bits
    numerator, remainder = divmod(value.numerator * scale, value.denominator)
    if remainder:
        numerator += 1
    return Q(numerator, scale)


def interval_square_lower(lower: Q, upper: Q) -> Q:
    if lower <= 0 <= upper:
        return Q(0)
    return min(lower * lower, upper * upper)


def box_norm_sq_lower(center: GaussianQ, half_width: Q) -> Q:
    return interval_square_lower(center.re - half_width, center.re + half_width) + (
        interval_square_lower(center.im - half_width, center.im + half_width)
    )


def direct_line_majorant(
    constant: Q, slope: Q, intercept: Q, radius_sq: Q
) -> Q:
    """Exact counterpart of Lean's quadratic side-majorant formula."""

    return max(
        Q(1),
        constant * constant
        + Q(2) * (slope * slope * radius_sq + intercept * intercept),
    )


def vertical_determinant(parameter: GaussianQ, x: Q) -> Q:
    return Q(4) * x * x * (x * x - parameter.re) - parameter.im * parameter.im


def horizontal_determinant(parameter: GaussianQ, y: Q) -> Q:
    return parameter.im * parameter.im - Q(4) * y * y * (y * y + parameter.re)


def direct_vertical_clearance(
    parameter: GaussianQ, center: GaussianQ, half_width: Q, x: Q
) -> Q:
    y_radius_sq = max(
        (center.im - half_width) ** 2,
        (center.im + half_width) ** 2,
    )
    determinant = vertical_determinant(parameter, x)
    return determinant * determinant / direct_line_majorant(
        Q(4) * x * x, Q(2) * x, parameter.im, y_radius_sq
    )


def direct_horizontal_clearance(
    parameter: GaussianQ, center: GaussianQ, half_width: Q, y: Q
) -> Q:
    x_radius_sq = max(
        (center.re - half_width) ** 2,
        (center.re + half_width) ** 2,
    )
    determinant = horizontal_determinant(parameter, y)
    return determinant * determinant / direct_line_majorant(
        Q(4) * y * y, -Q(2) * y, -parameter.im, x_radius_sq
    )


def direct_boundary_clearance(cell: Cell) -> Q:
    """Minimum of the four exact quadratic side-clearance bounds."""

    center = cell.root_center
    width = cell.root_half_width
    return min(
        direct_vertical_clearance(
            cell.radicand, center, width, center.re - width
        ),
        direct_vertical_clearance(
            cell.radicand, center, width, center.re + width
        ),
        direct_horizontal_clearance(
            cell.radicand, center, width, center.im - width
        ),
        direct_horizontal_clearance(
            cell.radicand, center, width, center.im + width
        ),
    )


def polynomial_variation_bound(start: GaussianQ, finish: GaussianQ) -> Q:
    """Exact upper bound for |p(start+t*d)-p(start)|^2 on 0 <= t <= 1.

    The cubic has no constant term after subtraction.  A nested two-term
    squared triangle bound gives ``2*|a1|^2 + 4*(|a2|^2 + |a3|^2)``.  This
    remains especially cheap for Lean's integer checker while avoiding an
    unnecessary split of one canonical prepared-cycle leg.
    """

    displacement = finish - start
    # p(z) = z^3 - (1 + lambda) z^2 + lambda z.
    a3 = displacement * displacement * displacement
    a2 = (start.scale(Q(3)) - (ONE + LAMBDA)) * displacement * displacement
    a1 = (
        start * start.scale(Q(3))
        - start.scale(Q(2)) * (ONE + LAMBDA)
        + LAMBDA
    ) * displacement
    return Q(2) * a1.norm_sq() + Q(4) * (a2.norm_sq() + a3.norm_sq())


def clear_segment_coefficients(leg: Leg) -> tuple[GaussianQ, ...]:
    """High-to-low coefficients of the Legendre cubic along ``leg``."""
    displacement = leg.finish - leg.start
    a3 = displacement * displacement * displacement
    a2 = (leg.start.scale(Q(3)) - (ONE + LAMBDA)) * displacement * displacement
    a1 = (
        leg.start * leg.start.scale(Q(3))
        - leg.start.scale(Q(2)) * (ONE + LAMBDA)
        + LAMBDA
    ) * displacement
    a0 = legendre_polynomial(leg.start)
    return (a3, a2, a1, a0)


def clear_segment_horner_bounds(
    leg: Leg,
) -> list[tuple[Q, Q]]:
    """The four exact value/slope states of Lean's dense-Horner scan."""
    value = Q(0)
    slope = Q(0)
    states: list[tuple[Q, Q]] = []
    # ``parameterAmbient.normSqBound`` is 2.
    for coefficient in clear_segment_coefficients(leg):
        previous_value = value
        value = Q(2) * (value * Q(2) + coefficient.norm_sq())
        slope = Q(2) * (slope * Q(2) + previous_value)
        states.append((value, slope))
    return states


def clear_segment_variation_bound(leg: Leg, cell_count: int) -> Q:
    """Lean's dense-Horner ``variationBound`` for one dyadic leg edge."""

    _value, slope = clear_segment_horner_bounds(leg)[-1]
    return max(Q(1), slope) / (cell_count * cell_count)


def prepared_cell_variation_bound(cell: Cell) -> Q:
    """Actual two-level prepared variation bound for a generated row."""

    leg_index = next(
        index for index, leg in enumerate(CYCLE_LEGS) if leg.name == cell.leg
    )
    outer_count = CYCLE_OUTER_COUNTS[leg_index]
    inner_count = CYCLE_INNER_COUNTS[leg_index]
    outer_index = cell.index // inner_count
    if cell.count != outer_count * inner_count or outer_index >= outer_count:
        raise ValueError(f"invalid two-level geometry at cell {cell.position}")
    raw_leg = CYCLE_LEGS[leg_index]
    outer_start = raw_leg.start + (raw_leg.finish - raw_leg.start).scale(
        Q(outer_index, outer_count)
    )
    outer_finish = raw_leg.start + (raw_leg.finish - raw_leg.start).scale(
        Q(outer_index + 1, outer_count)
    )
    outer_leg = Leg(cell.leg, outer_start, outer_finish)
    return clear_segment_variation_bound(outer_leg, inner_count)


def factorized_source_clearance(cell: Cell) -> Q:
    """Direct rational lower bound for the source quadratic on its box.

    On the boundary, ``|(z-c)(z+c)|^2`` is bounded below by the square
    half-width times the coordinatewise lower bound for ``|z+c|^2``.  The
    weighted identity used in Lean retains 15/16 of that main term and
    charges fifteen copies of the tiny centre residual.
    """

    half_width = cell.root_half_width
    second_factor_lower = box_norm_sq_lower(
        cell.root_center.scale(Q(2)), half_width
    )
    main_lower = half_width * half_width * second_factor_lower
    return Q(15, 16) * main_lower - Q(15) * cell.root_residual_sq


def subdivide(leg: Leg, count: int) -> Iterator[tuple[int, GaussianQ, GaussianQ]]:
    displacement = leg.finish - leg.start
    for index in range(count):
        start = leg.start + displacement.scale(Q(index, count))
        finish = leg.start + displacement.scale(Q(index + 1, count))
        yield index, start, finish


@cache
def working_segments() -> tuple[Leg, ...]:
    """The outer working segments used by the selected prepared path."""

    result: list[Leg] = []
    for leg, count in zip(CYCLE_LEGS, CYCLE_OUTER_COUNTS, strict=True):
        for index, start, finish in subdivide(leg, count):
            result.append(Leg(f"{leg.name}-outer-{index}", start, finish))
    return tuple(result)


def working_segment_of_position(position: int) -> int:
    cell_offset = 0
    segment_offset = 0
    for cell_count, outer_count, inner_count in zip(
        CYCLE_CELL_COUNTS,
        CYCLE_OUTER_COUNTS,
        CYCLE_INNER_COUNTS,
        strict=True,
    ):
        if position < cell_offset + cell_count:
            return segment_offset + (position - cell_offset) // inner_count
        cell_offset += cell_count
        segment_offset += outer_count
    raise ValueError(f"cell position outside selected cycle: {position}")


def build_cells(
    legs: Sequence[Leg],
    counts: Sequence[int],
    root_bits: int,
    coefficient_bits: int,
    allowance_bits: int,
    half_width_bits: int,
    decimal_precision: int,
) -> list[Cell]:
    if len(legs) != len(counts):
        raise ValueError("every selected cycle leg needs one subdivision count")
    half_width = Q(1, 1 << half_width_bits)
    cells: list[Cell] = []
    previous: GaussianQ | None = None
    position = 0
    for leg_index, (leg, count) in enumerate(zip(legs, counts, strict=True)):
        if count <= 0:
            raise ValueError(f"nonpositive subdivision count for {leg.name}")
        if (
            FLIP_ROOT_AT_SHEET_SWITCH
            and leg_index == FIRST_SHEET_LEG_COUNT
            and previous is not None
        ):
            previous = -previous
        for index, start, finish in subdivide(leg, count):
            radicand = legendre_polynomial(start)
            center = tracked_root_center(
                radicand, previous, root_bits, decimal_precision
            )
            previous = center
            residual_sq = (center * center - radicand).norm_sq()
            variation_sq = polynomial_variation_bound(start, finish)
            center_norm_sq = center.norm_sq()
            # On the square boundary, |h|^2 >= delta^2.  Thus the linear
            # term 2*c*h has squared norm at least this value.
            left_sq = Q(4) * center_norm_sq * half_width * half_width
            # |h|^2 <= 2*delta^2, hence |h^2|^2 <= 4*delta^4.  Three times
            # the sum bounds the three-term residual h^2 + (c^2-p0) + dp.
            remainder_sq = Q(3) * (
                residual_sq
                + Q(4) * half_width**4
                + variation_sq
            )
            norm_lower = box_norm_sq_lower(center, half_width)
            if norm_lower <= 0:
                raise ValueError(f"root box reaches zero in {leg.name}[{index}]")
            exact_center_reciprocal = center.reciprocal()
            coefficient = dyadic_gaussian(exact_center_reciprocal, coefficient_bits)
            rounding_error_sq = (coefficient - exact_center_reciprocal).norm_sq()
            box_error_sq = (
                Q(2) * half_width * half_width / (norm_lower * center_norm_sq)
            )
            coefficient_error_sq = dyadic_ceil(
                Q(2) * (rounding_error_sq + box_error_sq), allowance_bits
            )
            cells.append(
                Cell(
                    position=position,
                    leg=leg.name,
                    index=index,
                    count=count,
                    start=start,
                    finish=finish,
                    radicand=radicand,
                    root_center=center,
                    root_half_width=half_width,
                    transport_root_half_width=half_width,
                    coefficient=coefficient,
                    root_residual_sq=residual_sq,
                    radicand_variation_sq=variation_sq,
                    rouche_left_sq=left_sq,
                    rouche_remainder_sq=remainder_sq,
                    root_norm_sq_lower=norm_lower,
                    coefficient_error_sq=coefficient_error_sq,
                    transport_coefficient_error_sq=coefficient_error_sq,
                    movement_sq=(finish - start).norm_sq(),
                )
            )
            position += 1
    return cells


def build_best_width_cells(
    legs: Sequence[Leg],
    counts: Sequence[int],
    root_bits: int,
    coefficient_bits: int,
    allowance_bits: int,
    minimum_half_width_bits: int,
    maximum_half_width_bits: int,
    decimal_precision: int,
) -> list[Cell]:
    """Choose separate sharp coefficient and transport squares per cell.

    The narrow square controls the reciprocal error paid by the literal
    integration model.  A second, generally wider square is used only as the
    continuation owner; its source clearance must carry the actual two-level
    prepared edge.  Keeping those roles separate avoids making a transport
    margin contaminate the numerical period enclosure.
    """

    if maximum_half_width_bits < minimum_half_width_bits:
        raise ValueError("empty half-width bit range")
    variants = [
        build_cells(
            legs,
            counts,
            root_bits,
            coefficient_bits,
            allowance_bits,
            half_width_bits,
            decimal_precision,
        )
        for half_width_bits in range(
            minimum_half_width_bits, maximum_half_width_bits + 1
        )
    ]
    selected: list[Cell] = []
    for position in range(len(variants[0])):
        coefficient_valid = [
            candidate[position]
            for candidate in variants
            if candidate[position].rouche_remainder_sq
            < candidate[position].rouche_left_sq
        ]
        transport_valid = [
            candidate[position]
            for candidate in variants
            if candidate[position].rouche_remainder_sq
            < candidate[position].rouche_left_sq
            and prepared_cell_variation_bound(candidate[position])
            < factorized_source_clearance(candidate[position])
            and Q(1, 1 << 20)
            <= factorized_source_clearance(candidate[position])
        ]
        if not coefficient_valid:
            cell = variants[0][position]
            raise ValueError(
                "no coefficient dyadic root box for "
                f"{cell.leg}[{cell.index}]"
            )
        if not transport_valid:
            cell = variants[0][position]
            raise ValueError(
                "no carrying dyadic root box for "
                f"{cell.leg}[{cell.index}]"
            )
        coefficient_cell = min(
            coefficient_valid,
            key=lambda cell: (cell.coefficient_error_sq, cell.root_half_width),
        )
        # Retain the narrowest box which still carries the complete prepared
        # subedge.  The old widest-box choice maximized unused clearance but
        # made the downstream quotient-variation radius needlessly large.
        transport_cell = min(
            transport_valid, key=lambda cell: cell.root_half_width
        )
        selected.append(
            replace(
                coefficient_cell,
                transport_root_half_width=transport_cell.root_half_width,
                transport_coefficient_error_sq=
                    transport_cell.coefficient_error_sq,
            )
        )
    return selected


def validate_cells(cells: Sequence[Cell]) -> None:
    if not cells:
        raise ValueError("empty certificate")
    sheet_switch_position = sum(
        CYCLE_CELL_COUNTS[:FIRST_SHEET_LEG_COUNT]
    )
    for index, cell in enumerate(cells):
        if legendre_polynomial(cell.start) != cell.radicand:
            raise ValueError(f"radicand mismatch at cell {index}")
        exact_reciprocal = cell.root_center.reciprocal()
        rounding_error_sq = (cell.coefficient - exact_reciprocal).norm_sq()
        box_error_sq = (
            Q(2)
            * cell.root_half_width
            * cell.root_half_width
            / (cell.root_norm_sq_lower * cell.root_center.norm_sq())
        )
        if cell.coefficient_error_sq < Q(2) * (rounding_error_sq + box_error_sq):
            raise ValueError(f"coefficient error mismatch at cell {index}")
        if not cell.rouche_remainder_sq < cell.rouche_left_sq:
            raise ValueError(
                f"Rouche inequality failed at {cell.leg}[{cell.index}]: "
                f"{cell.rouche_remainder_sq} !< {cell.rouche_left_sq}"
            )
        transport = at_transport_width(cell)
        if not cell.root_half_width <= cell.transport_root_half_width:
            raise ValueError(
                f"transport root box is narrower at cell {index}"
            )
        if transport.root_norm_sq_lower <= 0:
            raise ValueError(
                f"transport root box reaches zero at cell {index}"
            )
        if not transport.rouche_remainder_sq < transport.rouche_left_sq:
            raise ValueError(
                "transport Rouche inequality failed at "
                f"{cell.leg}[{cell.index}]"
            )
        source_clearance = factorized_source_clearance(transport)
        if not prepared_cell_variation_bound(transport) < source_clearance:
            raise ValueError(
                f"transport owner does not carry cell {index}"
            )
        if not Q(1, 1 << 20) <= source_clearance:
            raise ValueError(
                f"transport preparation reserve failed at cell {index}"
            )
        if cell.root_norm_sq_lower <= 0:
            raise ValueError(f"zero root lower bound at cell {index}")
        if cell.start == cell.finish and not ALLOW_STATIONARY_GENERATED_CELLS:
            raise ValueError(f"stationary generated cell at {index}")
        if index and cells[index - 1].finish != cell.start:
            raise ValueError(f"path discontinuity before cell {index}")
        if index and not (
            FLIP_ROOT_AT_SHEET_SWITCH and index == sheet_switch_position
        ):
            previous = cells[index - 1]
            overlap_width = previous.root_half_width + cell.root_half_width
            if abs(previous.root_center.re - cell.root_center.re) > overlap_width:
                raise ValueError(f"root boxes are horizontally disjoint before cell {index}")
            if abs(previous.root_center.im - cell.root_center.im) > overlap_width:
                raise ValueError(f"root boxes are vertically disjoint before cell {index}")
    if cells[-1].finish != cells[0].start:
        raise ValueError("generated Legendre path is not closed")
    if not FLIP_ROOT_AT_SHEET_SWITCH:
        closure_width = cells[-1].root_half_width + cells[0].root_half_width
        if abs(cells[-1].root_center.re - cells[0].root_center.re) > closure_width:
            raise ValueError("tracked root boxes do not close horizontally")
        if abs(cells[-1].root_center.im - cells[0].root_center.im) > closure_width:
            raise ValueError("tracked root boxes do not close vertically")


def clearance_diagnostics(cells: Sequence[Cell]) -> dict[str, object]:
    """Summarize the exact margin available to the strengthened owners."""

    cells = [at_transport_width(cell) for cell in cells]
    clearance_values = [direct_boundary_clearance(cell) for cell in cells]
    variation_ratios = [
        clearance / cell.radicand_variation_sq
        for cell, clearance in zip(cells, clearance_values, strict=True)
    ]
    preparation_ratios = [
        clearance / (Q(16) * cell.root_half_width**2 / Q(10240))
        for cell, clearance in zip(cells, clearance_values, strict=True)
    ]
    local_clearance_values = [
        cell.rouche_left_sq - cell.rouche_remainder_sq for cell in cells
    ]
    endpoint_variations = [
        (legendre_polynomial(cell.finish) - cell.radicand).norm_sq()
        for cell in cells
    ]
    prepared_variations = [
        prepared_cell_variation_bound(cell) for cell in cells
    ]
    local_transport_ratios = [
        clearance / variation
        for clearance, variation in zip(
            local_clearance_values, endpoint_variations, strict=True
        )
    ]
    local_preparation_ratios = [
        clearance / (Q(16) * cell.root_half_width**2 / Q(10240))
        for cell, clearance in zip(cells, local_clearance_values, strict=True)
    ]
    source_clearance_values = [
        cell.rouche_left_sq
        - Q(3) * (cell.root_residual_sq + Q(4) * cell.root_half_width**4)
        for cell in cells
    ]
    source_transport_ratios = [
        clearance / variation
        for clearance, variation in zip(
            source_clearance_values, endpoint_variations, strict=True
        )
    ]
    source_prepared_transport_ratios = [
        clearance / variation
        for clearance, variation in zip(
            source_clearance_values, prepared_variations, strict=True
        )
    ]
    source_preparation_ratios = [
        clearance / (cell.root_half_width**2 / Q(5120))
        for cell, clearance in zip(cells, source_clearance_values, strict=True)
    ]
    least_clearance_index = min(
        range(len(cells)), key=lambda index: clearance_values[index]
    )
    least_variation_ratio_index = min(
        range(len(cells)), key=lambda index: variation_ratios[index]
    )
    least_preparation_ratio_index = min(
        range(len(cells)), key=lambda index: preparation_ratios[index]
    )
    least_local_transport_ratio_index = min(
        range(len(cells)), key=lambda index: local_transport_ratios[index]
    )
    least_local_preparation_ratio_index = min(
        range(len(cells)), key=lambda index: local_preparation_ratios[index]
    )
    least_source_transport_ratio_index = min(
        range(len(cells)), key=lambda index: source_transport_ratios[index]
    )
    least_source_preparation_ratio_index = min(
        range(len(cells)), key=lambda index: source_preparation_ratios[index]
    )
    least_source_prepared_transport_ratio_index = min(
        range(len(cells)), key=lambda index: source_prepared_transport_ratios[index]
    )

    def ratio_json(index: int, values: Sequence[Q]) -> dict[str, object]:
        return {
            "position": index,
            "leg": cells[index].leg,
            "local_index": cells[index].index,
            "value": fraction_json(values[index]),
            "decimal": float(values[index]),
        }

    return {
        "least_clearance": ratio_json(least_clearance_index, clearance_values),
        "least_clearance_over_variation": ratio_json(
            least_variation_ratio_index, variation_ratios
        ),
        "least_clearance_over_preparation_upper": ratio_json(
            least_preparation_ratio_index, preparation_ratios
        ),
        "least_local_clearance_over_endpoint_variation": ratio_json(
            least_local_transport_ratio_index, local_transport_ratios
        ),
        "least_local_clearance_over_preparation_upper": ratio_json(
            least_local_preparation_ratio_index, local_preparation_ratios
        ),
        "least_source_clearance_over_endpoint_variation": ratio_json(
            least_source_transport_ratio_index, source_transport_ratios
        ),
        "least_source_clearance_over_prepared_variation": ratio_json(
            least_source_prepared_transport_ratio_index,
            source_prepared_transport_ratios,
        ),
        "least_source_clearance_over_preparation_upper": ratio_json(
            least_source_preparation_ratio_index, source_preparation_ratios
        ),
    }


def sum_gaussians(values: Iterable[GaussianQ]) -> GaussianQ:
    total = ZERO
    for value in values:
        total = total + value
    return total


def ceil_sqrt_fraction(value: Q, bits: int) -> Q:
    if value < 0:
        raise ValueError("cannot take square root of a negative rational")
    scale = 1 << bits
    scaled_numerator = value.numerator * scale * scale
    quotient, remainder = divmod(scaled_numerator, value.denominator)
    candidate = isqrt(quotient)
    if candidate * candidate < quotient or remainder:
        candidate += 1
    while Q(candidate * candidate, scale * scale) < value:
        candidate += 1
    return Q(candidate, scale)


def fraction_json(value: Q) -> dict[str, int]:
    return {"numerator": value.numerator, "denominator": value.denominator}


def gaussian_json(value: GaussianQ) -> dict[str, dict[str, int]]:
    return {"re": fraction_json(value.re), "im": fraction_json(value.im)}


def dyadic_square_radius(target: Q) -> Q:
    """Match ``FiniteGeometric.dyadicSquareRadius`` on a rational target."""

    radius = Q(1)
    while radius * radius >= target:
        radius /= 2
    return radius


@cache
def segment_denominator_lower(segment: Leg) -> Q:
    """Exact exponent-zero denominator floor used by the prepared model."""

    variation = clear_segment_variation_bound(segment, 1)
    radicand_lower = legendre_polynomial(segment.start).norm_sq() / 2 - variation
    midpoint = segment.start + (segment.finish - segment.start).scale(Q(1, 2))
    midpoint_lower = (
        legendre_polynomial(midpoint).norm_sq() / 2 - variation / 4
    )
    local_lower = max(radicand_lower, midpoint_lower)

    residual = min(Q(1), GENERATED_PATH_CLEARANCE_FLOOR / 4) / 8
    magnitude = dyadic_square_radius(GENERATED_PATH_CLEARANCE_FLOOR / 2) / 16
    coordinate_lower = max(residual, magnitude)
    sampled_residual = min(Q(1), radicand_lower / 4) / 8
    sampled_magnitude = (
        dyadic_square_radius(local_lower / 2) / 16
        if local_lower > 0
        else Q(0)
    )
    return max(coordinate_lower, sampled_residual, sampled_magnitude)


@cache
def parent_weighted_allowance_upper(cell: Cell) -> Q:
    """Owner-specific weighted allowance upper bound for one parent row."""

    segment = working_segments()[working_segment_of_position(cell.position)]
    denominator_lower = max(
        segment_denominator_lower(segment),
        box_norm_sq_lower(cell.root_center, cell.transport_root_half_width),
    )
    root_coefficient = Q(2) / (denominator_lower * denominator_lower) + 1
    requested_root_diameter = Q(16) * cell.transport_root_half_width**2
    local_allowance_upper = Q(16) * root_coefficient * requested_root_diameter
    return cell.movement_sq * local_allowance_upper


def parent_model_aggregate_upper(cells: Sequence[Cell]) -> Q:
    """Segmentwise upper bound for the retained centred parent model.

    For ``dx/y`` the point-variation coefficient is zero.  The prepared
    owner box supplies a sharper denominator floor than the segment alone,
    so the model error is bounded by
    ``(2 / denominatorLower^2 + 1) * requestedRootDiameter``.  Its centred
    cell reserves a factor sixteen, exactly as in Lean.
    """

    weighted = sum((parent_weighted_allowance_upper(cell) for cell in cells), Q(0))
    return Q(len(cells)) * weighted


def rounded_parent_weighted_allowance_upper(
    cells: Sequence[Cell], movement_bits: int
) -> Q:
    """Sum the independently checked per-row dyadic parent bounds."""

    return sum(
        (
            dyadic_ceil(parent_weighted_allowance_upper(cell), movement_bits)
            for cell in cells
        ),
        Q(0),
    )


def cell_json(cell: Cell) -> dict[str, object]:
    return {
        "position": cell.position,
        "leg": cell.leg,
        "index": cell.index,
        "count": cell.count,
        "start": gaussian_json(cell.start),
        "finish": gaussian_json(cell.finish),
        "radicand": gaussian_json(cell.radicand),
        "root_center": gaussian_json(cell.root_center),
        "root_half_width": fraction_json(cell.root_half_width),
        "transport_root_half_width": fraction_json(
            cell.transport_root_half_width
        ),
        "coefficient": gaussian_json(cell.coefficient),
        "root_residual_sq": fraction_json(cell.root_residual_sq),
        "radicand_variation_sq": fraction_json(cell.radicand_variation_sq),
        "rouche_left_sq": fraction_json(cell.rouche_left_sq),
        "rouche_remainder_sq": fraction_json(cell.rouche_remainder_sq),
        "root_norm_sq_lower": fraction_json(cell.root_norm_sq_lower),
        "coefficient_error_sq": fraction_json(cell.coefficient_error_sq),
        "transport_coefficient_error_sq": fraction_json(
            cell.transport_coefficient_error_sq
        ),
        "movement_sq": fraction_json(cell.movement_sq),
    }


def certificate_json(cells: Sequence[Cell], movement_bits: int) -> dict[str, object]:
    sample = sum_gaussians(cell.contribution() for cell in cells)
    weighted_allowance = sum((cell.weighted_allowance() for cell in cells), Q(0))
    movement_sq_sum = sum((cell.movement_sq for cell in cells), Q(0))
    transport_weighted_error_sum = sum(
        (
            cell.movement_sq * cell.transport_coefficient_error_sq
            for cell in cells
        ),
        Q(0),
    )
    # At zero alignment target, the block theorem pays twice each generated
    # reciprocal error.  Finite Gaussian Cauchy--Schwarz then contributes the
    # number of nonstationary parent rows, independently of the later dyadic
    # child depth.
    transport_aggregate_at_zero = (
        Q(2) * Q(len(cells)) * transport_weighted_error_sum
    )
    # The certified lifted cycle contains two exact stationary sheet
    # transitions in addition to the generated positive-width rows.  Their
    # samples and weighted allowances are zero, but PathModel's aggregate
    # allowance multiplies by the complete cell count.
    aggregate_allowance = Q(len(cells) + STATIONARY_SWITCH_COUNT) * weighted_allowance
    movement = ceil_sqrt_fraction(aggregate_allowance, movement_bits)
    # Keep this diagnostic upper bound exact but compact.  Summing the distinct
    # prepared-box denominators produces a mathematically harmless denominator
    # with tens of thousands of digits; upward rounding onto the existing
    # movement grid preserves the bound and keeps JSON inspection practical.
    parent_aggregate_upper = Q(len(cells)) * (
        rounded_parent_weighted_allowance_upper(cells, movement_bits)
    )
    source_schedule_base_upper = parent_aggregate_upper + SCHEDULE_SLACK
    source_flat_error_scale_upper = Q(12) * source_schedule_base_upper
    source_error_scale_upper = Q(3) * source_flat_error_scale_upper
    return {
        "format": (
            "ccl-legendre-b-period-v1"
            if FLIP_ROOT_AT_SHEET_SWITCH
            else "ccl-legendre-a-period-v1"
        ),
        "curve_parameter": gaussian_json(LAMBDA),
        "cell_count": len(cells) + STATIONARY_SWITCH_COUNT,
        "nonstationary_cell_count": len(cells),
        "literal_sample": gaussian_json(sample),
        "weighted_allowance": fraction_json(weighted_allowance),
        "aggregate_allowance": fraction_json(aggregate_allowance),
        "movement_sq_sum": fraction_json(movement_sq_sum),
        "transport_weighted_error_sum": fraction_json(
            transport_weighted_error_sum
        ),
        "transport_aggregate_at_zero": fraction_json(
            transport_aggregate_at_zero
        ),
        "movement": fraction_json(movement),
        "real_lower": fraction_json(sample.re - movement),
        "parent_aggregate_upper": fraction_json(parent_aggregate_upper),
        "source_schedule_base_upper": fraction_json(source_schedule_base_upper),
        "source_flat_error_scale_upper": fraction_json(
            source_flat_error_scale_upper
        ),
        "source_error_scale_upper": fraction_json(source_error_scale_upper),
        "cells": [cell_json(cell) for cell in cells],
    }


def extended_gcd(left: int, right: int) -> tuple[int, int, int]:
    old_remainder, remainder = left, right
    old_left, current_left = 1, 0
    old_right, current_right = 0, 1
    while remainder:
        quotient = old_remainder // remainder
        old_remainder, remainder = remainder, old_remainder - quotient * remainder
        old_left, current_left = current_left, old_left - quotient * current_left
        old_right, current_right = current_right, old_right - quotient * current_right
    return old_remainder, old_left, old_right


def lean_integer(value: int) -> str:
    return f"(-{-value})" if value < 0 else str(value)


def lean_fraction(value: Q) -> str:
    if value.denominator == 1:
        return lean_integer(value.numerator)
    gcd, left, right = extended_gcd(abs(value.numerator), value.denominator)
    if gcd != 1:
        raise ValueError(f"non-reduced generated fraction: {value}")
    return (
        "reducedRational "
        f"{lean_integer(value.numerator)} {value.denominator} (by decide) "
        f"{lean_integer(left)} {lean_integer(right)} (by decide)"
    )


def lean_gaussian(value: GaussianQ) -> str:
    return f"⟨{lean_fraction(value.re)}, {lean_fraction(value.im)}⟩"


def lean_horner_bounds(value: Q, slope: Q) -> str:
    return f"⟨{lean_fraction(value)}, {lean_fraction(slope)}⟩"


def fixed_dyadic_numerator(value: Q, bits: int) -> int:
    scaled = value * (1 << bits)
    if scaled.denominator != 1:
        raise ValueError(f"{value} is not on the requested 2^-{bits} grid")
    return scaled.numerator


def lean_compact_totals(
    cells: Sequence[Cell], coefficient_bits: int, allowance_bits: int
) -> tuple[int, int, int, int, int, int]:
    sample = sum_gaussians(cell.contribution() for cell in cells)
    weighted_allowance = sum((cell.weighted_allowance() for cell in cells), Q(0))
    movement_sq = sum((cell.movement_sq for cell in cells), Q(0))
    transport_weighted_error = sum(
        (
            cell.movement_sq * cell.transport_coefficient_error_sq
            for cell in cells
        ),
        Q(0),
    )
    return (
        len(cells),
        fixed_dyadic_numerator(sample.re, 13 + coefficient_bits),
        fixed_dyadic_numerator(sample.im, 13 + coefficient_bits),
        fixed_dyadic_numerator(weighted_allowance, 26 + allowance_bits),
        fixed_dyadic_numerator(movement_sq, 26),
        fixed_dyadic_numerator(transport_weighted_error, 26 + allowance_bits),
    )


def lean_compact_totals_value(
    totals: tuple[int, int, int, int, int, int]
) -> str:
    (
        count,
        sample_re,
        sample_im,
        weighted_allowance,
        movement_sq,
        transport_weighted_error,
    ) = totals
    return (
        "{ count := "
        f"{count}, sampleRe := {lean_integer(sample_re)}, "
        f"sampleIm := {lean_integer(sample_im)}, "
        f"weightedAllowance := {lean_integer(weighted_allowance)}, "
        f"movementSq := {lean_integer(movement_sq)}, "
        "transportWeightedError := "
        f"{lean_integer(transport_weighted_error)} }}"
    )


def lean_entry(
    position: int,
    cell: Cell,
    root_bits: int,
    coefficient_bits: int,
    allowance_bits: int,
) -> str:
    if cell.root_half_width.numerator != 1:
        raise ValueError("generated root half-width is not a reciprocal power of two")
    half_width_bits = cell.root_half_width.denominator.bit_length() - 1
    if 1 << half_width_bits != cell.root_half_width.denominator:
        raise ValueError("generated root half-width is not dyadic")
    if cell.transport_root_half_width.numerator != 1:
        raise ValueError(
            "generated transport root half-width is not a reciprocal power of two"
        )
    transport_half_width_bits = (
        cell.transport_root_half_width.denominator.bit_length() - 1
    )
    if 1 << transport_half_width_bits != cell.transport_root_half_width.denominator:
        raise ValueError("generated transport root half-width is not dyadic")
    return (
        "  { position := "
        f"{position}\n"
        f"    rootRe := {lean_integer(fixed_dyadic_numerator(cell.root_center.re, root_bits))}\n"
        f"    rootIm := {lean_integer(fixed_dyadic_numerator(cell.root_center.im, root_bits))}\n"
        f"    halfWidthBits := {half_width_bits}\n"
        f"    transportHalfWidthBits := {transport_half_width_bits}\n"
        f"    coefficientRe := {lean_integer(fixed_dyadic_numerator(cell.coefficient.re, coefficient_bits))}\n"
        f"    coefficientIm := {lean_integer(fixed_dyadic_numerator(cell.coefficient.im, coefficient_bits))}\n"
        f"    coefficientErrorNumerator := {lean_integer(fixed_dyadic_numerator(cell.coefficient_error_sq, allowance_bits))}\n"
        f"    transportCoefficientErrorNumerator := {lean_integer(fixed_dyadic_numerator(cell.transport_coefficient_error_sq, allowance_bits))} }}"
    )


LEAN_NAMESPACE = "CCL.Riemann.ExplicitLegendreGeneratedCertificate"


def lean_checked_cell_definitions(
    cells: Sequence[Cell],
    first_cell_index: int,
    root_bits: int,
    coefficient_bits: int,
    allowance_bits: int,
) -> list[str]:
    lines: list[str] = []
    for local_cell_index, cell in enumerate(cells):
        cell_index = first_cell_index + local_cell_index
        name = f"cell{cell_index:04d}"
        lines.extend(
            [
                f"def {name}Data : CompactCellData :=",
                lean_entry(
                    cell.position,
                    cell,
                    root_bits,
                    coefficient_bits,
                    allowance_bits,
                ),
                "",
                f"def {name} : CompactCheckedCell rootBits coefficientBits allowanceBits where",
                f"  data := {name}Data",
                "  checked := by decide +revert",
                "",
            ]
        )
    return lines


def lean_base_module(
    cells: Sequence[Cell],
    root_bits: int,
    coefficient_bits: int,
    allowance_bits: int,
    movement_bits: int,
) -> str:
    certificate = certificate_json(cells, movement_bits)
    row_totals = lean_compact_totals(cells, coefficient_bits, allowance_bits)
    totals = (
        row_totals[0] + STATIONARY_SWITCH_COUNT,
        row_totals[1],
        row_totals[2],
        row_totals[3],
        row_totals[4],
        row_totals[5],
    )
    movement = Q(
        certificate["movement"]["numerator"],
        certificate["movement"]["denominator"],
    )
    movement_numerator = fixed_dyadic_numerator(movement, movement_bits)
    movement_sq_sum = sum((cell.movement_sq for cell in cells), Q(0))
    transport_weighted_error_sum = sum(
        (
            cell.movement_sq * cell.transport_coefficient_error_sq
            for cell in cells
        ),
        Q(0),
    )
    movement_sq_sum_numerator = fixed_dyadic_numerator(movement_sq_sum, 26)
    transport_weighted_error_numerator = fixed_dyadic_numerator(
        transport_weighted_error_sum, 26 + allowance_bits
    )
    lines = [
        "-- This file is generated by scripts/generate-legendre-certificate.py.",
        "-- Edit the generator, not this certificate data.",
        f"import CCL.Riemann.{GENERATED_DATA_MODULE}",
        "",
        f"namespace {LEAN_NAMESPACE}",
        "",
        f"open CCL.Riemann.{GENERATED_DATA_MODULE}",
        "",
        f"def nonstationaryCellCount : Nat := {len(cells)}",
        f"def cellCount : Nat := {len(cells) + STATIONARY_SWITCH_COUNT}",
        f"def rootBits : Nat := {root_bits}",
        f"def coefficientBits : Nat := {coefficient_bits}",
        f"def allowanceBits : Nat := {allowance_bits}",
        f"def movementBits : Nat := {movement_bits}",
        "def generatedRowTotals : CompactTotals :=",
        f"  {lean_compact_totals_value(row_totals)}",
        "def certificateTotals : CompactTotals :=",
        f"  {lean_compact_totals_value(totals)}",
        f"def movementNumerator : Int := {lean_integer(movement_numerator)}",
        "def literalSample : Gaussian :=",
        "  certificateTotals.literalSample coefficientBits",
        "def weightedAllowance : Coordinate :=",
        "  certificateTotals.weightedAllowanceValue allowanceBits",
        "def aggregateAllowance : Coordinate :=",
        "  certificateTotals.aggregateAllowance allowanceBits",
        "def movement : Coordinate :=",
        "  compactMovement movementBits movementNumerator",
        "def realLower : Coordinate :=",
        "  compactRealLower coefficientBits movementBits certificateTotals",
        "    movementNumerator",
        "/-- Sum of squared movements of the nonstationary generated rows. -/",
        "def generatedMovementSqSum : Coordinate :=",
        "  Dyadic.toCoordinate",
        f"    {{ numerator := {lean_integer(movement_sq_sum_numerator)}, bits := 26 }}",
        "/-- Sum of row movement squared times the transport reciprocal error. -/",
        "def generatedTransportWeightedErrorSum : Coordinate :=",
        "  Dyadic.toCoordinate",
        f"    {{ numerator := {lean_integer(transport_weighted_error_numerator)},",
        f"      bits := {26 + allowance_bits} }}",
        "/-- Whole-path transport comparison after finite Cauchy--Schwarz.",
        "The alignment target remains a caller-selected rational. -/",
        "def generatedTransportAggregate (target : Coordinate) : Coordinate :=",
        "  2 * (nonstationaryCellCount : Coordinate) *",
        "    (10 * target * generatedMovementSqSum +",
        "      generatedTransportWeightedErrorSum)",
        "",
        f"end {LEAN_NAMESPACE}",
        "",
    ]
    return "\n".join(lines)


def lean_shard_module(
    cells: Sequence[Cell],
    shard_index: int,
    first_cell: int,
    root_bits: int,
    coefficient_bits: int,
    allowance_bits: int,
) -> str:
    cell_names = [
        f"cell{first_cell + index:04d}" for index in range(len(cells))
    ]
    shard_name = f"shard{shard_index:03d}"
    shard_cells = ",\n    ".join(cell_names)
    first_position = cells[0].position
    totals = lean_compact_totals(cells, coefficient_bits, allowance_bits)
    lines = [
        "-- This file is generated by scripts/generate-legendre-certificate.py.",
        "-- Edit the generator, not this certificate data.",
        f"import CCL.Riemann.{EXPLICIT_CERTIFICATE_PREFIX}Data.Base",
        "",
        f"namespace {LEAN_NAMESPACE}",
        "",
        f"open CCL.Riemann.{GENERATED_DATA_MODULE}",
        "",
        *lean_checked_cell_definitions(
            cells,
            first_cell,
            root_bits,
            coefficient_bits,
            allowance_bits,
        ),
        f"def {shard_name}Cells : List (CompactCheckedCell rootBits coefficientBits allowanceBits) := [",
        f"    {shard_cells}",
        "]",
        "",
        f"def {shard_name} : CompactCheckedShard rootBits coefficientBits allowanceBits {first_position} where",
        f"  checkedCells := {shard_name}Cells",
        "  nonempty := by decide +revert",
        f"  firstCell := {cell_names[0]}.data",
        f"  lastCell := {cell_names[-1]}.data",
        "  firstChecked := by decide +revert",
        "  lastChecked := by decide +revert",
        "  sequenceChecked := by decide +revert",
        f"  totals := {lean_compact_totals_value(totals)}",
        "  totalsChecked := by decide +revert",
        "",
        f"end {LEAN_NAMESPACE}",
        "",
    ]
    return "\n".join(lines)


def lean_geometric_cell_definitions(
    cells: Sequence[Cell], first_cell_index: int, movement_bits: int
) -> list[str]:
    """Emit exact canonical-mesh witnesses for one short row block.

    The row's position already determines both endpoints in
    ``CompactCellData``.  Lean checks that those endpoints are the matching
    logarithmically selected dyadic edge; Python supplies no proof object.
    """

    lines: list[str] = []
    for local_cell_index, cell in enumerate(cells):
        cell_index = first_cell_index + local_cell_index
        cell_name = f"cell{cell_index:04d}"
        geometric_name = f"geometricCell{cell_index:04d}"
        parent_upper_name = f"{geometric_name}ParentWeightedAllowanceUpper"
        parent_upper = dyadic_ceil(
            parent_weighted_allowance_upper(cell), movement_bits
        )
        segment_index = working_segment_of_position(cell.position)
        lines.extend(
            [
                f"def {geometric_name} (_token : Unit) :",
                "    GeometricCheckedCell rootBits coefficientBits allowanceBits where",
                f"  checked := {cell_name}",
                "  geometry :=",
                "    { location :=",
                f"        {{ legIndex := ⟨{segment_index}, by",
                f"            rw [{GENERATED_LEG_LIST}_length]",
                "            decide +revert⟩",
                "          legIndex_eq := by decide +revert",
                "          localWithin := by decide +revert }",
                f"      segmentBinding := generatedLegBinding{segment_index:03d}",
                "      cachedStart_eq := by rfl",
                "      cachedFinish_eq := by rfl",
                "      transportWithinThree := by decide +revert",
                "      narrowRefinesTransport := by",
                "        unfold RFAP.Boxes.Box.Refines",
                "        decide +revert",
                "      cachedTransportCarries := by decide +revert }",
                "",
                f"@[simp] theorem {geometric_name}_checked (token : Unit) :",
                f"    ({geometric_name} token).checked = {cell_name} := rfl",
                "",
                f"@[simp] theorem {geometric_name}_denominatorLower (token : Unit) :",
                f"    ({geometric_name} token).geometry.segmentBinding.denominatorLower =",
                f"      generatedLegDenominatorLower{segment_index:03d} := rfl",
                "",
                f"def {parent_upper_name} : RFAP.ConstructiveFraction.Rational :=",
                f"  {lean_fraction(parent_upper)}",
                "",
                f"theorem {parent_upper_name}_checked (token : Unit) :",
                f"    ({geometric_name} token).parentWeightedAllowanceUpper <=",
                f"      {parent_upper_name} := by",
                f"  rw [({geometric_name} token).parentWeightedAllowanceUpper_eq_compact]",
                "  change compactParentWeightedAllowanceUpperAt",
                f"    {cell_name}.data rootBits generatedLegDenominatorLower{segment_index:03d} <=",
                f"      {parent_upper_name}",
                "  decide +revert",
                "",
            ]
        )
    for local_cell_index in range(len(cells) - 1):
        left_index = first_cell_index + local_cell_index
        right_index = left_index + 1
        left_name = f"geometricCell{left_index:04d}"
        right_name = f"geometricCell{right_index:04d}"
        link_name = f"geometricCellLink{left_index:04d}_{right_index:04d}"
        lines.extend(
            [
                f"theorem {link_name}_coordinate (token : Unit) :",
                f"    ({left_name} token).checked.data.finishValue =",
                f"      ({right_name} token).checked.data.startValue := by",
                f"  rw [{left_name}_checked, {right_name}_checked]",
                "  rfl",
                "",
                f"theorem {link_name}_sheet (token : Unit) :",
                f"    ({left_name} token).sheet = ({right_name} token).sheet := by",
                "  unfold GeometricCheckedCell.sheet",
                f"  rw [{left_name}_checked, {right_name}_checked]",
                "  decide +revert",
                "",
            ]
        )
    return lines


def lean_segment_certificate_shard_module(index: int, segment: Segment) -> str:
    lines = [
        "-- This file is generated by scripts/generate-legendre-certificate.py.",
        "-- Edit the generator, not this certificate data.",
        f"import CCL.Riemann.{EXPLICIT_CERTIFICATE_PREFIX}Semantics",
        "",
        f"namespace {LEAN_NAMESPACE}",
        "",
        f"open CCL.Riemann.{GENERATED_DATA_MODULE}",
        "",
    ]
    # A short dyadic upper bound is substantially cheaper for Lean to compare
    # than the fully reduced exact rational produced by the dense-Horner scan.
    # Twenty-four bits leaves far more slack than the tightest generated
    # transport inequality needs.
    variation = dyadic_ceil(clear_segment_variation_bound(segment, 1), 24)
    denominator_lower = segment_denominator_lower(segment)
    coefficients = clear_segment_coefficients(segment)
    bounds = clear_segment_horner_bounds(segment)
    lines.extend(
        [
            f"def generatedLegCertificate{index:03d} : GeneratedLegCertificate where",
            f"  start := {lean_gaussian(segment.start)}",
            f"  finish := {lean_gaussian(segment.finish)}",
        ]
    )
    if ALLOW_STATIONARY_GENERATED_CELLS:
        actual_coefficients = (
            coefficients[-1:] if segment.start == segment.finish else coefficients
        )
        lines.extend(
            [
                "  coefficients := ["
                + ", ".join(lean_gaussian(value) for value in actual_coefficients)
                + "]",
                "  coefficients_eq := by decide +revert",
                f"  finalBounds := {lean_horner_bounds(*bounds[-1])}",
                "  finalBounds_eq := by decide +revert",
            ]
        )
    else:
        lines.extend(
            [
                f"  coefficient3 := {lean_gaussian(coefficients[0])}",
                f"  coefficient2 := {lean_gaussian(coefficients[1])}",
                f"  coefficient1 := {lean_gaussian(coefficients[2])}",
                f"  coefficient0 := {lean_gaussian(coefficients[3])}",
                "  coefficients_eq := by decide +revert",
                f"  bounds1 := {lean_horner_bounds(*bounds[0])}",
                f"  bounds2 := {lean_horner_bounds(*bounds[1])}",
                f"  bounds3 := {lean_horner_bounds(*bounds[2])}",
                f"  bounds4 := {lean_horner_bounds(*bounds[3])}",
                "  bounds1_eq := by decide +revert",
                "  bounds2_eq := by decide +revert",
                "  bounds3_eq := by decide +revert",
                "  bounds4_eq := by decide +revert",
            ]
        )
    lines.extend(
        [
            f"  variation := {lean_fraction(variation)}",
            "  variation_le := by decide +revert",
            "",
            f"def generatedLegDenominatorLower{index:03d} :",
            "    RFAP.ConstructiveFraction.Rational :=",
            f"  {lean_fraction(denominator_lower)}",
            "",
            f"def generatedLegBinding{index:03d} : GeneratedLegBinding",
            f"    ({GENERATED_LEG_LIST}.get ⟨{index}, by",
            f"      rw [{GENERATED_LEG_LIST}_length]",
            "      decide +revert⟩) where",
            f"  certificate := generatedLegCertificate{index:03d}",
            "  start_eq := by rfl",
            "  finish_eq := by rfl",
            "  clearance_eq := by rfl",
            f"  denominatorLower := generatedLegDenominatorLower{index:03d}",
            "  denominatorLower_eq := by",
            f"    calc",
            f"      _ = generatedLegCertificate{index:03d}.denominatorLower :=",
            "        GeneratedLegCertificate.segmentDenominatorLower_eq _ _",
            "          (by rfl) (by rfl) (by rfl)",
            f"      _ = generatedLegDenominatorLower{index:03d} := by",
            "        decide +revert",
            "",
        ]
    )
    lines.extend([f"end {LEAN_NAMESPACE}", ""])
    return "\n".join(lines)


def lean_segment_certificate_module(segment_imports: Sequence[str]) -> str:
    return "\n".join(
        [
            "-- This file is generated by scripts/generate-legendre-certificate.py.",
            "-- Edit the generator, not this certificate data.",
            *segment_imports,
            "",
        ]
    )


def lean_geometry_shard_module(
    cells: Sequence[Cell],
    shard_index: int,
    first_cell: int,
    coefficient_bits: int,
    allowance_bits: int,
    movement_bits: int,
    data_shard_index: int,
) -> str:
    geometric_names = [
        f"geometricCell{first_cell + index:04d}" for index in range(len(cells))
    ]
    geometric_values = [f"({name} token)" for name in geometric_names]
    shard_name = f"geometricShard{shard_index:03d}Cells"
    run_name = f"geometricShard{shard_index:03d}Run"
    summary_name = f"geometricShard{shard_index:03d}Summary"
    shard_cells = ",\n    ".join(geometric_values)

    def sequence_proof(names: Sequence[str]) -> list[str]:
        values = [f"({name} token)" for name in names]
        if len(names) == 1:
            return [f"  exact .single {values[0]}"]
        first_link = f"geometricCellLink{names[0][-4:]}_{names[1][-4:]}"
        proof = [
            f"  exact .cons {values[0]} {values[1]}",
            f"      ({first_link}_coordinate token) ({first_link}_sheet token)",
        ]
        for index in range(1, len(names) - 1):
            link = f"geometricCellLink{names[index][-4:]}_{names[index + 1][-4:]}"
            proof.append(
                "  " * (index + 2)
                + f"(.cons {values[index]} {values[index + 1]}"
            )
            proof.append(
                "  " * (index + 3)
                + f"({link}_coordinate token) ({link}_sheet token)"
            )
        proof.append(
            "  " * (len(names) + 1)
            + f"(.single {values[-1]})"
            + ")" * (len(names) - 2)
        )
        return proof

    # Tokenized geometry cells add one deliberately lazy reduction layer.
    # Two-row local summaries keep the endpoint sequence proofs comfortably
    # inside Lean's ordinary recursion depth without changing any cell data.
    summary_block_size = 2
    block_lines: list[str] = []
    accumulated_name = ""
    for block_index, block_start in enumerate(
        range(0, len(geometric_names), summary_block_size)
    ):
        block_finish = min(block_start + summary_block_size, len(geometric_names))
        block_geometric_names = geometric_names[block_start:block_finish]
        block_names = geometric_values[block_start:block_finish]
        block_cells = cells[block_start:block_finish]
        prefix = f"geometricShard{shard_index:03d}Block{block_index:03d}"
        cells_name = f"{prefix}Cells"
        sequence_name = f"{prefix}Sequence"
        uncached_name = f"{prefix}UncachedSummary"
        totals_name = f"{prefix}Totals"
        totals_summary_name = f"{prefix}TotalsSummary"
        parent_upper_name = f"{prefix}ParentWeightedAllowanceUpper"
        block_summary_name = f"{prefix}Summary"
        block_cell_lines = ",\n    ".join(block_names)
        remaining_lines = ",\n      ".join(block_names[1:])
        block_totals = lean_compact_totals(
            block_cells, coefficient_bits, allowance_bits
        )
        block_parent_upper = rounded_parent_weighted_allowance_upper(
            block_cells, movement_bits
        )
        cell_parent_terms = " + ".join(
            f"({name} token).parentWeightedAllowanceUpper"
            for name in block_geometric_names
        )
        checked_parent_terms = " + ".join(
            f"{name}ParentWeightedAllowanceUpper"
            for name in block_geometric_names
        )
        if len(block_geometric_names) == 1:
            parent_bound_proof = [
                f"      exact {block_geometric_names[0]}ParentWeightedAllowanceUpper_checked token"
            ]
        else:
            parent_checks = " ".join(
                f"({name}ParentWeightedAllowanceUpper_checked token)"
                for name in block_geometric_names
            )
            parent_bound_proof = [
                "      calc",
                f"        {cell_parent_terms} <= {checked_parent_terms} :=",
                f"          add_le_add {parent_checks}",
                f"        _ = {parent_upper_name} := by decide +revert",
            ]
        block_lines.extend(
            [
                f"def {cells_name} (token : Unit) : List",
                "    (GeometricCheckedCell rootBits coefficientBits allowanceBits) := [",
                f"    {block_cell_lines}",
                "]",
                "",
                f"def {sequence_name} (token : Unit) : GeneratedCellSequence ({cells_name} token)",
                f"    {block_names[-1]} := by",
                f"  unfold {cells_name}",
                *sequence_proof(block_geometric_names),
                "",
                f"def {uncached_name} (token : Unit) : SummarizedGeneratedCenteredRunRange",
                f"    {block_names[0]} {block_names[-1]} := by",
                f"  apply GeneratedCenteredRun.ofCellsSummarized {block_names[0]} [",
                f"      {remaining_lines}",
                "    ]",
                f"  simpa only [{cells_name}] using {sequence_name} token",
                "",
                f"def {totals_name} : CompactTotals :=",
                f"  {lean_compact_totals_value(block_totals)}",
                "",
                f"def {totals_summary_name} (token : Unit) :=",
                f"  ({uncached_name} token).rebaseTotals {totals_name}",
                "    (by cases token; decide +revert)",
                "",
                f"def {parent_upper_name} : RFAP.ConstructiveFraction.Rational :=",
                f"  {lean_fraction(block_parent_upper)}",
                "",
                f"def {block_summary_name} (token : Unit) :=",
                f"  ({totals_summary_name} token).rebaseParentAllowance",
                f"    {len(block_cells)} 0 {parent_upper_name}",
                "    (by cases token; decide +revert)",
                "    (by cases token; decide +revert)",
                "    (by",
                *parent_bound_proof,
                "    )",
                "",
            ]
        )
        range_name = f"geometricShard{shard_index:03d}SummaryRange{block_index:03d}"
        if block_index == 0:
            block_lines.extend(
                [f"def {range_name} (token : Unit) := {block_summary_name} token", ""]
            )
        else:
            raw_name = f"{range_name}Raw"
            cumulative_totals_name = f"{range_name}Totals"
            totals_rebased_name = f"{range_name}TotalsRebased"
            cumulative_parent_upper_name = (
                f"{range_name}ParentWeightedAllowanceUpper"
            )
            left_link_index = first_cell + block_start - 1
            right_link_index = left_link_index + 1
            link_name = (
                f"geometricCellLink{left_link_index:04d}_{right_link_index:04d}"
            )
            cumulative_totals = lean_compact_totals(
                cells[:block_finish], coefficient_bits, allowance_bits
            )
            cumulative_parent_upper = rounded_parent_weighted_allowance_upper(
                cells[:block_finish], movement_bits
            )
            block_lines.extend(
                [
                    f"def {raw_name} (token : Unit) :=",
                    f"  ({accumulated_name} token).append ({block_summary_name} token)",
                    f"    ({link_name}_coordinate token) ({link_name}_sheet token)",
                    "",
                    f"def {cumulative_totals_name} : CompactTotals :=",
                    f"  {lean_compact_totals_value(cumulative_totals)}",
                    "",
                    f"def {totals_rebased_name} (token : Unit) :=",
                    f"  ({raw_name} token).rebaseTotals {cumulative_totals_name}",
                    "    (by cases token; decide +revert)",
                    "",
                    f"def {cumulative_parent_upper_name} :",
                    "    RFAP.ConstructiveFraction.Rational :=",
                    f"  {lean_fraction(cumulative_parent_upper)}",
                    "",
                    f"def {range_name} (token : Unit) :=",
                    f"  ({totals_rebased_name} token).rebaseParentAllowance",
                    f"    {block_finish} 0 {cumulative_parent_upper_name}",
                    "    (by cases token; decide +revert)",
                    "    (by cases token; decide +revert)",
                    "    (by cases token; decide +revert)",
                    "",
                ]
            )
        accumulated_name = range_name
    segment_indices = sorted(
        {working_segment_of_position(cell.position) for cell in cells}
    )
    segment_imports = [
        f"import CCL.Riemann.{EXPLICIT_SEGMENT_CERTIFICATE_PREFIX}Data."
        f"Chunk{segment_index:03d}"
        for segment_index in segment_indices
    ]
    lines = [
        "-- This file is generated by scripts/generate-legendre-certificate.py.",
        "-- Edit the generator, not this certificate data.",
        f"import CCL.Riemann.{EXPLICIT_CERTIFICATE_PREFIX}Data."
        f"Chunk{data_shard_index:03d}",
        *segment_imports,
        "",
        f"namespace {LEAN_NAMESPACE}",
        "",
        f"open CCL.Riemann.{GENERATED_DATA_MODULE}",
        "",
        *lean_geometric_cell_definitions(cells, first_cell, movement_bits),
        f"def {shard_name} (token : Unit) : List",
        "    (GeometricCheckedCell rootBits coefficientBits allowanceBits) := [",
        f"    {shard_cells}",
        "]",
        "",
        *block_lines,
        f"def {summary_name} (token : Unit) := {accumulated_name} token",
        "",
        f"def {run_name} (token : Unit) : GeneratedCenteredRunRange",
        f"    ({geometric_names[0]} token) ({geometric_names[-1]} token) :=",
        f"  ({summary_name} token).range",
        "",
        f"end {LEAN_NAMESPACE}",
        "",
    ]
    return "\n".join(lines)


def module_name(path: Path) -> str:
    return ".".join(path.with_suffix("").parts)


def write_lean_certificate(
    output: Path,
    cells: Sequence[Cell],
    chunk_size: int,
    rows_per_module: int,
    geometry_rows_per_module: int,
    root_bits: int,
    coefficient_bits: int,
    allowance_bits: int,
    movement_bits: int,
) -> None:
    if chunk_size != 1:
        raise ValueError("Lean checked-cell output currently requires --chunk-size 1")
    if rows_per_module <= 0:
        raise ValueError("--rows-per-module must be positive")
    if geometry_rows_per_module <= 0:
        raise ValueError("--geometry-rows-per-module must be positive")
    if rows_per_module % geometry_rows_per_module != 0:
        raise ValueError("geometry rows per module must divide data rows per module")
    data_directory = output.with_suffix("").with_name(f"{output.stem}Data")
    geometry_output = output.with_name(
        f"{output.stem.removesuffix('Certificate')}GeometryCertificate.lean"
    )
    geometry_directory = geometry_output.with_suffix("").with_name(
        f"{geometry_output.stem}Data"
    )
    segment_output = output.with_name(
        f"{output.stem.removesuffix('Certificate')}SegmentCertificate.lean"
    )
    segment_directory = segment_output.with_suffix("").with_name(
        f"{segment_output.stem}Data"
    )
    base_path = data_directory / "Base.lean"
    atomic_write(
        base_path,
        lean_base_module(
            cells,
            root_bits,
            coefficient_bits,
            allowance_bits,
            movement_bits,
        ),
    )
    segments = working_segments()
    if len(segments) != EXPECTED_WORKING_SEGMENT_COUNT:
        raise ValueError(
            f"expected {EXPECTED_WORKING_SEGMENT_COUNT} working segments, "
            f"found {len(segments)}"
        )
    segment_imports: list[str] = []
    expected_segment_paths: set[Path] = set()
    for segment_index, segment in enumerate(segments):
        segment_path = segment_directory / f"Chunk{segment_index:03d}.lean"
        atomic_write(
            segment_path,
            lean_segment_certificate_shard_module(segment_index, segment),
        )
        expected_segment_paths.add(segment_path)
        segment_imports.append(f"import {module_name(segment_path)}")
    for stale_path in segment_directory.glob("*.lean"):
        if stale_path not in expected_segment_paths:
            stale_path.unlink()
    atomic_write(segment_output, lean_segment_certificate_module(segment_imports))
    imports: list[str] = []
    expected_paths = {base_path}
    for shard_index, start in enumerate(range(0, len(cells), rows_per_module)):
        shard = cells[start : start + rows_per_module]
        shard_path = data_directory / f"Chunk{shard_index:03d}.lean"
        first_cell = start
        atomic_write(
            shard_path,
            lean_shard_module(
                shard,
                shard_index,
                first_cell,
                root_bits,
                coefficient_bits,
                allowance_bits,
            ),
        )
        expected_paths.add(shard_path)
        imports.append(f"import {module_name(shard_path)}")
    geometry_imports: list[str] = []
    geometry_shard_names: list[str] = []
    geometry_run_names: list[str] = []
    expected_geometry_paths: set[Path] = set()
    for shard_index, start in enumerate(
        range(0, len(cells), geometry_rows_per_module)
    ):
        shard = cells[start : start + geometry_rows_per_module]
        first_cell = start
        data_shard_index = start // rows_per_module
        geometry_shard_path = geometry_directory / f"Chunk{shard_index:03d}.lean"
        atomic_write(
            geometry_shard_path,
            lean_geometry_shard_module(
                shard,
                shard_index,
                first_cell,
                coefficient_bits,
                allowance_bits,
                movement_bits,
                data_shard_index,
            ),
        )
        expected_geometry_paths.add(geometry_shard_path)
        geometry_imports.append(f"import {module_name(geometry_shard_path)}")
        geometry_shard_names.append(f"geometricShard{shard_index:03d}Cells")
        geometry_run_names.append(f"geometricShard{shard_index:03d}Run")
    for stale_path in data_directory.glob("*.lean"):
        if stale_path not in expected_paths:
            stale_path.unlink()
    for stale_path in geometry_directory.glob("*.lean"):
        if stale_path not in expected_geometry_paths:
            stale_path.unlink()
    shard_count = len(imports)
    first_sheet_cell_count = sum(CYCLE_CELL_COUNTS[:FIRST_SHEET_LEG_COUNT])
    if first_sheet_cell_count % rows_per_module != 0:
        raise ValueError("the sheet switch must fall on a generated shard boundary")
    second_sheet_start = first_sheet_cell_count // rows_per_module
    if not 0 < second_sheet_start < shard_count:
        raise ValueError("invalid generated sheet-switch shard")
    final_shard = shard_count - 1
    first_sheet_final = second_sheet_start - 1
    unbridged_links = (
        {first_sheet_final, final_shard}
        if FLIP_ROOT_AT_SHEET_SWITCH
        else set()
    )
    global_group_size = 16
    totals_group_lines: list[str] = []
    link_group_lines: list[str] = []
    totals_group_names: list[str] = []
    for group_index, group_start in enumerate(
        range(0, shard_count, global_group_size)
    ):
        group_finish = min(group_start + global_group_size, shard_count)
        totals_name = f"generatedShardTotals{group_index:03d}"
        totals_value_name = f"generatedShardTotalsValue{group_index:03d}"
        totals_group_names.append(totals_value_name)
        shard_totals = ",\n  ".join(
            f"shard{index:03d}.totals"
            for index in range(group_start, group_finish)
        )
        group_cells = cells[
            group_start * rows_per_module : group_finish * rows_per_module
        ]
        group_totals = lean_compact_totals(
            group_cells, coefficient_bits, allowance_bits
        )
        totals_group_lines.extend(
            [
                f"def {totals_name} : List CompactTotals := [",
                f"  {shard_totals}",
                "]",
                "",
                f"def {totals_value_name} : CompactTotals :=",
                f"  {lean_compact_totals_value(group_totals)}",
                "",
                f"theorem {totals_name}_checked :",
                f"    compactShardTotals {totals_name} = {totals_value_name} := by",
                "  decide +revert",
                "",
            ]
        )
        links_name = f"generatedShardLinks{group_index:03d}"
        group_link_indices = [
            index
            for index in range(group_start, group_finish)
            if index not in unbridged_links
        ]
        shard_links = ",\n  ".join(
            "{ left := "
            f"shard{index:03d}.last\n"
            "    right := "
            f"shard{(index + 1) % shard_count:03d}.first }}"
            for index in group_link_indices
        )
        link_group_lines.extend(
            [
                f"def {links_name} : List CompactShardLink := [",
                f"  {shard_links}",
                "]",
                "",
                f"theorem {links_name}_checked :",
                f"    checkCompactShardLinks rootBits {links_name} = true := by",
                "  decide +revert",
                "",
                f"theorem {links_name}_bounds :",
                f"    CompactShardLinksBounds rootBits {links_name} :=",
                f"  checkCompactShardLinks_sound {links_name}_checked",
                "",
            ]
        )
    individual_link_lines: list[str] = []
    path_package_lines: list[str] = []
    for shard_index in range(shard_count):
        next_shard = (shard_index + 1) % shard_count
        group_index = shard_index // global_group_size
        group_start = group_index * global_group_size
        group_finish = min(group_start + global_group_size, shard_count)
        group_link_indices = [
            index
            for index in range(group_start, group_finish)
            if index not in unbridged_links
        ]
        if shard_index not in unbridged_links:
            local_index = group_link_indices.index(shard_index)
            projection = (
                f"generatedShardLinks{group_index:03d}_bounds"
                + ".2" * local_index
                + ".1"
            )
            individual_link_lines.extend(
                [
                    f"theorem generatedShardLink{shard_index:03d}_bounds :",
                    "    ({ left := "
                    f"shard{shard_index:03d}.last, right := "
                    f"shard{next_shard:03d}.first }} : CompactShardLink).Bounds rootBits :=",
                    f"  {projection}",
                    "",
                    f"theorem generatedShardEndpoint{shard_index:03d} (sheet : Fin 2) :",
                    f"    CompactCellData.liftedFinish shard{shard_index:03d}.last sheet =",
                    f"      CompactCellData.liftedStart shard{next_shard:03d}.first sheet :=",
                    f"  shardLink_endpoint generatedShardLink{shard_index:03d}_bounds sheet",
                    "",
                ]
            )
        else:
            individual_link_lines.extend(
                [
                    f"theorem generatedShardEndpoint{shard_index:03d} (sheet : Fin 2) :",
                    f"    CompactCellData.liftedFinish shard{shard_index:03d}.last sheet =",
                    f"      CompactCellData.liftedStart shard{next_shard:03d}.first sheet := by",
                    "  rfl",
                    "",
                ]
            )
        sheet = 0 if shard_index < second_sheet_start else 1
        path_package_lines.extend(
            [
                f"def generatedShardSummary{shard_index:03d} (_token : Unit) :=",
                f"  shard{shard_index:03d}.literalSummary ({sheet} : Fin 2)",
                "",
            ]
        )
        if shard_index in (0, second_sheet_start):
            path_package_lines.extend(
                [
                    f"def generatedPathSummary{shard_index:03d} (token : Unit) := "
                    f"generatedShardSummary{shard_index:03d} token",
                    "",
                ]
            )
        else:
            previous = shard_index - 1
            path_package_lines.extend(
                [
                    f"def generatedPathSummary{shard_index:03d} (token : Unit) :=",
                    f"  (generatedPathSummary{previous:03d} token).append",
                    f"    (generatedShardSummary{shard_index:03d} token)",
                    f"    (generatedShardEndpoint{previous:03d} "
                    f"({sheet} : Fin 2))",
                    "",
                ]
            )
    path_package_lines.extend(
        [
            "def generatedRightSwitchSummary (_token : Unit) :=",
            "  SummarizedLiteralPathPackage.stationary rootBits coefficientBits",
            f"    allowanceBits shard{first_sheet_final:03d}.last.finishValue "
            "(0 : Fin 2)",
            "",
            "def generatedThroughRightSwitch (token : Unit) :=",
            f"  (generatedPathSummary{first_sheet_final:03d} token).appendMixed",
            "    (generatedRightSwitchSummary token) rfl",
            "",
            "def generatedThroughSecondSheet (token : Unit) :=",
            "  (generatedThroughRightSwitch token).appendMixed",
            f"    (generatedPathSummary{final_shard:03d} token)",
            f"    (generatedShardEndpoint{first_sheet_final:03d} "
            "(1 : Fin 2))",
            "",
            "def generatedLeftSwitchSummary (_token : Unit) :=",
            "  SummarizedLiteralPathPackage.stationary rootBits coefficientBits",
            f"    allowanceBits shard{final_shard:03d}.last.finishValue "
            "(1 : Fin 2)",
            "",
            "def generatedClosedPathSummary (token : Unit) :=",
            "  (generatedThroughSecondSheet token).appendMixed",
            "    (generatedLeftSwitchSummary token) rfl",
            "",
            "def generatedClosedPathPackage (token : Unit) :=",
            "  (generatedClosedPathSummary token).package.close",
            f"    (generatedShardEndpoint{final_shard:03d} (0 : Fin 2))",
            "",
            "theorem generatedPathTotals_checked (token : Unit) :",
            "    (generatedClosedPathSummary token).totals = certificateTotals := by",
            "  cases token",
            "  decide +revert",
            "",
            "theorem generatedCellCount_eq (token : Unit) :",
            "    (generatedClosedPathPackage token).models.length = cellCount := by",
            "  change (generatedClosedPathSummary token).package.models.length = cellCount",
            "  rw [(generatedClosedPathSummary token).count_eq,",
            "    generatedPathTotals_checked token]",
            "  rfl",
            "",
            "theorem generatedLiteralSample_eq (token : Unit) :",
            "    (CCL.ProgressiveGaussianIntegration.PathModel.mk",
            "      (generatedClosedPathPackage token).models).integralSample = literalSample := by",
            "  change (CCL.ProgressiveGaussianIntegration.PathModel.mk",
            "      (generatedClosedPathSummary token).package.models).integralSample = literalSample",
            "  rw [(generatedClosedPathSummary token).integralSample_eq,",
            "    generatedPathTotals_checked token]",
            "  rfl",
            "",
            "theorem generatedAggregateAllowance_eq (token : Unit) :",
            "    (CCL.ProgressiveGaussianIntegration.PathModel.mk",
            "      (generatedClosedPathPackage token).models).aggregateAllowance =",
            "        aggregateAllowance := by",
            "  change (CCL.ProgressiveGaussianIntegration.PathModel.mk",
            "      (generatedClosedPathSummary token).package.models).aggregateAllowance =",
            "        aggregateAllowance",
            "  rw [(generatedClosedPathSummary token).aggregateAllowance_eq,",
            "    generatedPathTotals_checked token]",
            "  rfl",
            "",
        ]
    )
    totals_groups = ",\n  ".join(totals_group_names)
    facade = "\n".join(
        [
            "-- This file is generated by scripts/generate-legendre-certificate.py.",
            "-- Edit the generator, not this certificate data.",
            *imports,
            f"import CCL.Riemann.{GENERATED_SEMANTICS_MODULE}",
            "",
            f"namespace {LEAN_NAMESPACE}",
            "",
            f"open CCL.Riemann.{GENERATED_DATA_MODULE}",
            "",
            *totals_group_lines,
            "def generatedShardTotals : List CompactTotals := [",
            f"  {totals_groups}",
            "]",
            "",
            "theorem generatedShardTotals_checked :",
            "    compactShardTotals generatedShardTotals = generatedRowTotals := by",
            "  decide +revert",
            "",
            *link_group_lines,
            *individual_link_lines,
            *path_package_lines,
            "theorem generatedGlobalBounds_checked :",
            "    checkCompactGlobalBounds coefficientBits allowanceBits movementBits",
            "      certificateTotals movementNumerator = true := by",
            "  decide +revert",
            "",
            "theorem generatedGlobalBounds :",
            "    CompactGlobalBounds coefficientBits allowanceBits movementBits",
            "      certificateTotals movementNumerator :=",
            "  checkCompactGlobalBounds_sound generatedGlobalBounds_checked",
            "",
            "theorem weightedAllowance_nonnegative : 0 <= weightedAllowance :=",
            "  generatedGlobalBounds.weightedAllowanceNonnegative",
            "",
            "theorem movement_positive : 0 < movement :=",
            "  generatedGlobalBounds.movementPositive",
            "",
            "theorem aggregateAllowance_le_movement_sq :",
            "    aggregateAllowance <= movement ^ 2 :=",
            "  generatedGlobalBounds.aggregateAllowanceLe",
            "",
            "theorem realLower_positive : 0 < realLower :=",
            "  generatedGlobalBounds.realLowerPositive",
            "",
            f"end {LEAN_NAMESPACE}",
            "",
        ]
    )
    atomic_write(output, facade)
    geometry_shard_count = len(geometry_imports)
    if first_sheet_cell_count % geometry_rows_per_module != 0:
        raise ValueError(
            "the sheet switch must fall on a generated geometry boundary"
        )
    geometry_second_sheet_start = (
        first_sheet_cell_count // geometry_rows_per_module
    )
    geometric_shards = ",\n  ".join(
        f"{name} token" for name in geometry_shard_names
    )
    geometric_range_lines: list[str] = []
    sheet_ranges = (
        (0, geometry_second_sheet_start),
        (geometry_second_sheet_start, geometry_shard_count),
    )
    for group_start, group_finish in sheet_ranges:
        for shard_index in reversed(range(group_start, group_finish)):
            range_name = f"generatedGeometricSummaryRange{shard_index:03d}"
            shard_summary_name = f"geometricShard{shard_index:03d}Summary"
            if shard_index == group_finish - 1:
                geometric_range_lines.extend(
                    [
                        f"def {range_name} (token : Unit) := {shard_summary_name} token",
                        "",
                    ]
                )
                continue
            next_name = f"generatedGeometricSummaryRange{shard_index + 1:03d}"
            raw_name = f"generatedGeometricSummaryRangeRaw{shard_index:03d}"
            totals_name = f"generatedGeometricRangeTotals{shard_index:03d}"
            totals_rebased_name = (
                f"generatedGeometricSummaryRangeTotalsRebased{shard_index:03d}"
            )
            parent_upper_name = (
                f"generatedGeometricRangeParentWeightedAllowanceUpper{shard_index:03d}"
            )
            left_cell_index = (shard_index + 1) * geometry_rows_per_module - 1
            right_cell_index = left_cell_index + 1
            left_cell_name = f"geometricCell{left_cell_index:04d}"
            right_cell_name = f"geometricCell{right_cell_index:04d}"
            cumulative_cells = cells[
                shard_index * geometry_rows_per_module :
                min(group_finish * geometry_rows_per_module, len(cells))
            ]
            cumulative_totals = lean_compact_totals(
                cumulative_cells, coefficient_bits, allowance_bits
            )
            cumulative_parent_upper = rounded_parent_weighted_allowance_upper(
                cumulative_cells, movement_bits
            )
            geometric_range_lines.extend(
                [
                    f"def {raw_name} (token : Unit) :=",
                    f"  ({shard_summary_name} token).append ({next_name} token)",
                    "    (by",
                    f"      rw [{left_cell_name}_checked, {right_cell_name}_checked]",
                    "      rfl)",
                    "    (by",
                    "      unfold GeometricCheckedCell.sheet",
                    f"      rw [{left_cell_name}_checked, {right_cell_name}_checked]",
                    "      decide +revert)",
                    "",
                    f"def {totals_name} : CompactTotals :=",
                    f"  {lean_compact_totals_value(cumulative_totals)}",
                    "",
                    f"def {totals_rebased_name} (token : Unit) :=",
                    f"  ({raw_name} token).rebaseTotals {totals_name}",
                    "    (by cases token; decide +revert)",
                    "",
                    f"def {parent_upper_name} : RFAP.ConstructiveFraction.Rational :=",
                    f"  {lean_fraction(cumulative_parent_upper)}",
                    "",
                    f"def {range_name} (token : Unit) :=",
                    f"  ({totals_rebased_name} token).rebaseParentAllowance",
                    f"    {len(cumulative_cells)} 0 {parent_upper_name}",
                    "    (by cases token; decide +revert)",
                    "    (by cases token; decide +revert)",
                    "    (by cases token; decide +revert)",
                    "",
                ]
            )
    first_sheet_range = "generatedGeometricSummaryRange000"
    second_sheet_range = (
        f"generatedGeometricSummaryRange{geometry_second_sheet_start:03d}"
    )
    generated_parent_weighted_upper = rounded_parent_weighted_allowance_upper(
        cells, movement_bits
    )
    geometry_facade = "\n".join(
        [
            "-- This file is generated by scripts/generate-legendre-certificate.py.",
            "-- Edit the generator, not this certificate data.",
            *geometry_imports,
            "",
            f"namespace {LEAN_NAMESPACE}",
            "",
            f"open CCL.Riemann.{GENERATED_DATA_MODULE}",
            "",
            "def generatedGeometricShards (token : Unit) : List",
            "    (List (GeometricCheckedCell rootBits coefficientBits allowanceBits)) := [",
            f"  {geometric_shards}",
            "]",
            "",
            *geometric_range_lines,
            "def generatedFirstSheetSummaryRange (token : Unit) :=",
            f"  {first_sheet_range} token",
            "",
            "def generatedSecondSheetSummaryRange (token : Unit) :=",
            f"  {second_sheet_range} token",
            "",
            "def generatedFirstSheetRange (token : Unit) :=",
            "  (generatedFirstSheetSummaryRange token).range",
            "",
            "def generatedSecondSheetRange (token : Unit) :=",
            "  (generatedSecondSheetSummaryRange token).range",
            "",
            f"def generatedParentCount : Nat := {len(cells)}",
            "",
            "def generatedParentWeightedAllowanceUpper :",
            "    RFAP.ConstructiveFraction.Rational :=",
            f"  {lean_fraction(generated_parent_weighted_upper)}",
            "",
            "def generatedParentAggregateAllowanceUpper :",
            "    RFAP.ConstructiveFraction.Rational :=",
            "  generatedParentCount * generatedParentWeightedAllowanceUpper",
            "",
            f"end {LEAN_NAMESPACE}",
            "",
        ]
    )
    atomic_write(geometry_output, geometry_facade)


def atomic_write(path: Path, contents: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    if path.exists() and path.read_text(encoding="utf-8") == contents:
        return
    file_descriptor, temporary_name = tempfile.mkstemp(
        prefix=f".{path.name}.", dir=path.parent, text=True
    )
    try:
        with os.fdopen(file_descriptor, "w", encoding="utf-8") as output:
            output.write(contents)
        os.replace(temporary_name, path)
    except BaseException:
        try:
            os.unlink(temporary_name)
        except FileNotFoundError:
            pass
        raise


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--cycle",
        choices=("a", "b"),
        default="a",
        help="generate the canonical A or B period certificate (default: a)",
    )
    parser.add_argument(
        "--root-bits",
        type=int,
        default=40,
        help="dyadic precision used for rational square-root centres",
    )
    parser.add_argument(
        "--coefficient-bits",
        type=int,
        default=32,
        help="fixed dyadic precision used for coefficient centres",
    )
    parser.add_argument(
        "--allowance-bits",
        type=int,
        default=48,
        help="fixed dyadic grid used to round local error bounds upward",
    )
    parser.add_argument(
        "--minimum-half-width-bits",
        type=int,
        default=3,
        help="widest candidate root box has half-width 2^(-this value)",
    )
    parser.add_argument(
        "--maximum-half-width-bits",
        type=int,
        default=10,
        help="narrowest candidate root box has half-width 2^(-this value)",
    )
    parser.add_argument(
        "--movement-bits",
        type=int,
        default=32,
        help="dyadic precision of the upward-rounded aggregate error radius",
    )
    parser.add_argument(
        "--decimal-precision",
        type=int,
        default=100,
        help="working precision used only to choose dyadic root centres",
    )
    parser.add_argument("--output", type=Path, help="write deterministic output here")
    parser.add_argument(
        "--format",
        choices=("json", "lean"),
        default="json",
        help="output format (default: json)",
    )
    parser.add_argument(
        "--chunk-size",
        type=int,
        default=1,
        help="maximum rows in one independently checked Lean definition",
    )
    parser.add_argument(
        "--rows-per-module",
        type=int,
        default=64,
        help="generated rows in each independently buildable Lean module",
    )
    parser.add_argument(
        "--geometry-rows-per-module",
        type=int,
        default=16,
        help="generated geometry rows in each short-cycle Lean module",
    )
    parser.add_argument(
        "--summary", action="store_true", help="print compact exact summary data"
    )
    parser.add_argument(
        "--clearance-diagnostics",
        action="store_true",
        help="print exact strengthened-owner clearance margins",
    )
    return parser.parse_args()


def main() -> None:
    arguments = parse_args()
    configure_cycle(arguments.cycle)
    working_segments.cache_clear()
    if (
        arguments.root_bits <= 0
        or arguments.coefficient_bits <= 0
        or arguments.allowance_bits <= 0
        or arguments.minimum_half_width_bits <= 0
        or arguments.maximum_half_width_bits <= 0
    ):
        raise SystemExit("dyadic bit counts must be positive")
    cells = build_best_width_cells(
        CYCLE_LEGS,
        CYCLE_CELL_COUNTS,
        arguments.root_bits,
        arguments.coefficient_bits,
        arguments.allowance_bits,
        arguments.minimum_half_width_bits,
        arguments.maximum_half_width_bits,
        arguments.decimal_precision,
    )
    validate_cells(cells)
    certificate = certificate_json(cells, arguments.movement_bits)
    if arguments.format == "lean":
        if not arguments.output:
            raise SystemExit("--format lean requires --output")
        write_lean_certificate(
            arguments.output,
            cells,
            arguments.chunk_size,
            arguments.rows_per_module,
            arguments.geometry_rows_per_module,
            arguments.root_bits,
            arguments.coefficient_bits,
            arguments.allowance_bits,
            arguments.movement_bits,
        )
    else:
        encoded = json.dumps(certificate, sort_keys=True, separators=(",", ":")) + "\n"
    if arguments.output and arguments.format == "json":
        atomic_write(arguments.output, encoded)
    if arguments.summary or not arguments.output:
        summary = {key: certificate[key] for key in (
            "format",
            "cell_count",
            "literal_sample",
            "aggregate_allowance",
            "movement_sq_sum",
            "transport_weighted_error_sum",
            "transport_aggregate_at_zero",
            "movement",
            "real_lower",
            "parent_aggregate_upper",
            "source_schedule_base_upper",
            "source_flat_error_scale_upper",
            "source_error_scale_upper",
        )}
        print(json.dumps(summary, sort_keys=True, indent=2))
    if arguments.clearance_diagnostics:
        print(json.dumps(clearance_diagnostics(cells), sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
