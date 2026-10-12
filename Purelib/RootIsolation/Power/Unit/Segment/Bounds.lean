module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import all Purelib.Data.Gaussian.Power.Residual.Bounds

import Purelib.Data.Nat.Positive
import Purelib.Data.Rat.Fraction
import all Purelib.Data.Rat.Fraction.Order

import Purelib.Geometry.Rational.Affine
import Purelib.Geometry.Rational.Box.Segment

import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Power.Gaussian
public import Purelib.RootIsolation.Power.Unit.Box
import Purelib.RootIsolation.Power.Unit.Box.Residual
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic

open Purelib.Data.Gaussian.Norm.Basic (normSq)

open Purelib.Data

open Purelib

open Purelib.Data.Rat

open Purelib.Geometry.Rational

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

namespace Purelib.RootIsolation.Power.Unit.Segment.Bounds

open Purelib.Data.Gaussian

/-- Every point of the segment joining two points in the same robust box has power residual at most one over 32. -/
theorem unitRobustSegment_residual_le
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
    normSq ((Affine.line start (finish - start) time) ^
        degree.value - parameter) ≤ (1 / 32 : Fraction.Rational) := open Purelib.Polynomial in by
  let point := Affine.line start (finish - start) time
  have pointInside : (Power.Unit.Box.unitRobustBox parameterNonzero parameterUnit degree
      degreeAtLeastTwo index).Contains point :=
    Box.contains_line startInside finishInside timeInside
  have residual := Power.Unit.Box.Residual.unitRobustBox_residual_le parameterNonzero parameterUnit
    degree degreeAtLeastTwo index pointInside
  rw [Purelib.Polynomial.Power.Gaussian.rootPolynomial_eval] at residual
  exact residual
end Purelib.RootIsolation.Power.Unit.Segment.Bounds

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

namespace Purelib.RootIsolation.Power.Unit.Segment.Bounds

open Purelib.Data.Gaussian

/-- Every point of that retained robust-box segment has norm-to-the-degree at least one quarter. -/
theorem unitRobustSegment_power_lower
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
      normSq (Affine.line start (finish - start) time) ^
        degree.value := by
  apply Gaussian.Power.Residual.Bounds.one_fourth_le_normSq_power_of_residual_le_quarter parameterUnit
  exact (unitRobustSegment_residual_le parameterNonzero parameterUnit degree
    degreeAtLeastTwo index startInside finishInside timeInside).trans
      Fraction.Order.one_over_thirty_two_le_one_over_four
end Purelib.RootIsolation.Power.Unit.Segment.Bounds

end
