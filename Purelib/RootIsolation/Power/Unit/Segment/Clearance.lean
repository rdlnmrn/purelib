module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Power
import Purelib.Data.Nat.Positive
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import all Purelib.Data.Rat.Fraction.Power.Order

import Purelib.Geometry.Rational.Affine
import Purelib.Polynomial.Clearance.Pair.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Path.Components
import Purelib.Polynomial.Dense.Gaussian.Power.Coordinate
public import Purelib.RootIsolation.Power.Unit.Box
import Purelib.RootIsolation.Power.Unit.Segment.Bounds
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Evaluation

open Purelib.Data.Gaussian.Norm.Basic (normSq)

open Purelib.Data

open Purelib

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-!
# Finite monodromy for `Z^d - w`

This file specializes finite owner monodromy to the displayed power family.
The first layer records the exact off-zero Bézout identity.  It is uniform in
the displayed positive degree and uses only finite dense-polynomial
calculations:

`-w⁻¹ (Z^d-w) + (w⁻¹ d⁻¹ Z) (Z^d-w)' = 1`.

The later layers use that identity to carry every owner around one explicit
rational circuit of the parameter and to calculate the resulting finite
permutation.
-/

namespace Purelib.RootIsolation.Power.Unit.Segment.Clearance

open Purelib.Data.Gaussian

/-- Every point of a segment retained in one robust owner box has quadrance at least one quarter. -/
theorem unitRobustSegment_coordinate_lower
    {parameter start finish : Gaussian.Basic.Canonical}
    (parameterNonzero : parameter ≠ 0)
    (parameterUnit : normSq parameter = 1)
    (degree : Data.Nat.Positive.RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (index : Fin degree.value)
    (startInside : (Power.Unit.Box.unitRobustBox parameterNonzero parameterUnit degree
      degreeAtLeastTwo index).Contains start)
    (finishInside : (Power.Unit.Box.unitRobustBox parameterNonzero parameterUnit degree
      degreeAtLeastTwo index).Contains finish)
    {time : Fraction.Rational} (timeInside : (0 : Fraction.Rational) ≤ time ∧ time ≤ 1) :
    (1 / 4 : Fraction.Rational) ≤
      normSq (Affine.line start (finish - start) time) := by
  let value := normSq (Affine.line start (finish - start) time)
  have powerLower := Power.Unit.Segment.Bounds.unitRobustSegment_power_lower parameterNonzero
    parameterUnit degree degreeAtLeastTwo index startInside finishInside
    timeInside
  by_cases oneLe : (1 : Fraction.Rational) ≤ value
  · exact (show (1 / 4 : Fraction.Rational) ≤ 1 by decide).trans oneLe
  · have valueLeOne : value ≤ 1 := (lt_of_not_ge oneLe).le
    exact powerLower.trans
      (Fraction.Power.Order.pow_le_self_of_nonnegative_le_one (Gaussian.Norm.Basic.normSq_nonneg _) valueLeOne
        degree.positive)
end Purelib.RootIsolation.Power.Unit.Segment.Clearance

end

section
@[expose] public section

/-!
# Finite monodromy for `Z^d - w`

This file specializes finite owner monodromy to the displayed power family.
The first layer records the exact off-zero Bézout identity.  It is uniform in
the displayed positive degree and uses only finite dense-polynomial
calculations:

`-w⁻¹ (Z^d-w) + (w⁻¹ d⁻¹ Z) (Z^d-w)' = 1`.

The later layers use that identity to carry every owner around one explicit
rational circuit of the parameter and to calculate the resulting finite
permutation.
-/

namespace Purelib.RootIsolation.Power.Unit.Segment.Clearance

open Purelib.Data.Gaussian

/-- Every positive coordinate power has a displayed clearance along a robust
lift segment. -/
def unitRobustSegmentCoordinatePowerCertificate
    {parameter start finish : Gaussian.Basic.Canonical}
    (parameterNonzero : parameter ≠ 0)
    (parameterUnit : normSq parameter = 1)
    (degree : Data.Nat.Positive.RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (index : Fin degree.value)
    (startInside : (Power.Unit.Box.unitRobustBox parameterNonzero parameterUnit degree
      degreeAtLeastTwo index).Contains start)
    (finishInside : (Power.Unit.Box.unitRobustBox parameterNonzero parameterUnit degree
      degreeAtLeastTwo index).Contains finish)
    (exponent : Nat) :
    Clearance.Pair.Basic.Certificate
      (Dense.Gaussian.Path.Components.pathReal
        (Dense.Gaussian.Power.Coordinate.coordinatePositivePower exponent)
        start (finish - start))
      (Dense.Gaussian.Path.Components.pathImag
        (Dense.Gaussian.Power.Coordinate.coordinatePositivePower exponent)
        start (finish - start))
      { lower := 0, upper := 1, valid := by decide } :=
  { bound := (1 / 4 : Fraction.Rational) ^ (exponent + 1)
    positive := Fraction.Order.Arithmetic.pow_pos_direct
      (Fraction.Order.Field.div_pos_direct
        (Fraction.Cast.Order.natCast_pos_direct (n := 1) (by decide))
        (Fraction.Cast.Order.natCast_pos_direct (n := 4) (by decide))) _
    lower := by
      intro time timeInside
      have coordinateLower := unitRobustSegment_coordinate_lower
        parameterNonzero parameterUnit degree degreeAtLeastTwo index startInside
        finishInside timeInside
      have powered := Fraction.Order.Arithmetic.pow_le_pow_direct (by decide)
        coordinateLower (exponent + 1)
      rw [← Gaussian.Power.normSq_pow] at powered
      simpa only [Dense.Gaussian.Path.Components.eval_pathReal,
        Dense.Gaussian.Path.Components.eval_pathImag,
        Dense.Gaussian.Power.Coordinate.coordinatePositivePower_eval, normSq] using powered }
end Purelib.RootIsolation.Power.Unit.Segment.Clearance

end
