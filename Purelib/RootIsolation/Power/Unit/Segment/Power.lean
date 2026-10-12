module
import Purelib.Data.Nat.Subtraction

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Power
import Purelib.Data.Nat.Positive
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Polynomial.Clearance.Pair.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Path.Components
import Purelib.Polynomial.Dense.Gaussian.Power.Coordinate
public import Purelib.RootIsolation.Power.Unit.Box
import Purelib.RootIsolation.Power.Unit.Segment.Bounds
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Evaluation

open Purelib.Data

open Purelib

open Purelib.Polynomial

open Purelib.RootIsolation

section
public section

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

namespace Purelib.RootIsolation.Power.Unit.Segment

open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Norm.Basic (normSq)

/-- Quantitative nonvanishing certificate for the positive power of any
segment retained in one robust owner. -/
@[expose] def unitRobustSegmentPowerCertificate
    {parameter start finish : Gaussian.Basic.Canonical}
    (parameterNonzero : parameter ≠ 0)
    (parameterUnit : normSq parameter = 1)
    (degree : Data.Nat.Positive.RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (index : Fin degree.value)
    (startInside : (Power.Unit.Box.unitRobustBox parameterNonzero parameterUnit degree
      degreeAtLeastTwo index).Contains start)
    (finishInside : (Power.Unit.Box.unitRobustBox parameterNonzero parameterUnit degree
      degreeAtLeastTwo index).Contains finish) :
    Clearance.Pair.Basic.Certificate
      (Dense.Gaussian.Path.Components.pathReal
        (Dense.Gaussian.Power.Coordinate.coordinatePositivePower (degree.value - 1))
        start (finish - start))
      (Dense.Gaussian.Path.Components.pathImag
        (Dense.Gaussian.Power.Coordinate.coordinatePositivePower (degree.value - 1))
        start (finish - start))
      { lower := 0, upper := 1, valid := by decide } := open Purelib.Data.Rat in by
  have exponent : degree.value - 1 + 1 = degree.value :=
    Nat.Subtraction.sub_add_cancel degree.positive
  exact
    { bound := 1 / 4
      positive := Fraction.Order.Field.div_pos_direct
        (Fraction.Cast.Order.natCast_pos_direct (n := 1) (by decide))
        (Fraction.Cast.Order.natCast_pos_direct (n := 4) (by decide))
      lower := by
        intro time timeInside
        have lower := Power.Unit.Segment.Bounds.unitRobustSegment_power_lower parameterNonzero
          parameterUnit degree degreeAtLeastTwo index startInside finishInside
          timeInside
        rw [← exponent] at lower
        rw [← Gaussian.Power.normSq_pow] at lower
        simpa only [-eq_self, -iff_self, Dense.Gaussian.Path.Components.eval_pathReal,
          Dense.Gaussian.Path.Components.eval_pathImag,
          Dense.Gaussian.Power.Coordinate.coordinatePositivePower_eval, normSq] using lower }
end Purelib.RootIsolation.Power.Unit.Segment

end
