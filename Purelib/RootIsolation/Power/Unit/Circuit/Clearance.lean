module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Nat.Positive
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Interval.Basic
import Purelib.Geometry.Gaussian.UnitCircle.Quarter
import Purelib.Geometry.Rational.Affine.Segment

import Purelib.Geometry.Rational.Affine
import Purelib.Polynomial.Clearance.Pair.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Monomial.Coordinate
import Purelib.Polynomial.Dense.Gaussian.Path.Components
public import Purelib.Polynomial.Dense.Gaussian.UnitCircle.Rotation
public import Purelib.Polynomial.Dense.Rational.CauchyIndex.HalfPlane
public import Purelib.RootIsolation.Power.Unit.Circuit.Point
import Purelib.RootIsolation.Power.Unit.Circuit.Subdivision
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

open Purelib.Data.Nat.Positive (RootDegree)
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Polynomial.Clearance.Pair.Basic (Certificate)

open Purelib.Data.Gaussian.Norm.Basic (normSq)

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

namespace Purelib.RootIsolation.Power.Unit.Circuit.Clearance

open Purelib.Data.Gaussian

/-- Every point of a rotated retained quarter chord has real coordinate at least one. -/
theorem unitCircuitRotatedLine_real_ge_one
    (quarter : UnitCircuitQuarter) (degree : RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) {index : Nat}
    (indexBound : index < Power.Unit.Circuit.Subdivision.unitCircuitStepCount degree degreeAtLeastTwo)
    {time : Fraction.Rational} (timeInside : (0 : Fraction.Rational) ≤ time ∧ time ≤ 1) :
    1 ≤ ((Dense.Gaussian.UnitCircle.Rotation.unitCircuitRotatedCoordinate quarter).eval
      (Affine.line
        (Power.Unit.Circuit.Point.unitCircuitPoint quarter degree degreeAtLeastTwo index)
        (Power.Unit.Circuit.Point.unitCircuitPoint quarter degree degreeAtLeastTwo (index + 1) -
          Power.Unit.Circuit.Point.unitCircuitPoint quarter degree degreeAtLeastTwo index) time)).re := by
  let source := Power.Unit.Circuit.Point.unitCircuitPoint quarter degree degreeAtLeastTwo index
  let target := Power.Unit.Circuit.Point.unitCircuitPoint quarter degree degreeAtLeastTwo (index + 1)
  have sourceBound : 1 ≤ (Geometry.Gaussian.UnitCircle.Quarter.unitCircuitRotation quarter * source).re :=
    Power.Unit.Circuit.Point.unitCircuitRotatedPoint_real_ge_one quarter degree degreeAtLeastTwo
      (Nat.le_of_lt indexBound)
  have targetBound : 1 ≤ (Geometry.Gaussian.UnitCircle.Quarter.unitCircuitRotation quarter * target).re :=
    Power.Unit.Circuit.Point.unitCircuitRotatedPoint_real_ge_one quarter degree degreeAtLeastTwo
      (by omega)
  have oneMinusNonnegative : 0 ≤ 1 - time :=
    Fraction.Order.Arithmetic.sub_nonneg_direct timeInside.2
  rw [Dense.Gaussian.UnitCircle.Rotation.unitCircuitRotatedCoordinate_eval,
    Geometry.Rational.Affine.Segment.rotated_line_real_eq_convex]
  change 1 ≤ (1 - time) * (Geometry.Gaussian.UnitCircle.Quarter.unitCircuitRotation quarter * source).re +
    time * (Geometry.Gaussian.UnitCircle.Quarter.unitCircuitRotation quarter * target).re
  calc
    1 = (1 - time) * 1 + time * 1 := by ring1
    _ ≤ (1 - time) * (Geometry.Gaussian.UnitCircle.Quarter.unitCircuitRotation quarter * source).re +
        time * (Geometry.Gaussian.UnitCircle.Quarter.unitCircuitRotation quarter * target).re :=
      add_le_add
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          sourceBound oneMinusNonnegative)
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          targetBound timeInside.1)
end Purelib.RootIsolation.Power.Unit.Circuit.Clearance

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

namespace Purelib.RootIsolation.Power.Unit.Circuit.Clearance

open Purelib.Data.Gaussian

/-- Every point of a rotated retained quarter chord has quadrance at least one. -/
theorem unitCircuitRotatedLine_normSq_ge_one
    (quarter : UnitCircuitQuarter) (degree : RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) {index : Nat}
    (indexBound : index < Power.Unit.Circuit.Subdivision.unitCircuitStepCount degree degreeAtLeastTwo)
    {time : Fraction.Rational} (timeInside : (0 : Fraction.Rational) ≤ time ∧ time ≤ 1) :
    1 ≤ normSq ((Dense.Gaussian.UnitCircle.Rotation.unitCircuitRotatedCoordinate quarter).eval
      (Affine.line
        (Power.Unit.Circuit.Point.unitCircuitPoint quarter degree degreeAtLeastTwo index)
        (Power.Unit.Circuit.Point.unitCircuitPoint quarter degree degreeAtLeastTwo (index + 1) -
          Power.Unit.Circuit.Point.unitCircuitPoint quarter degree degreeAtLeastTwo index) time)) := by
  let value := (Dense.Gaussian.UnitCircle.Rotation.unitCircuitRotatedCoordinate quarter).eval
    (Affine.line
      (Power.Unit.Circuit.Point.unitCircuitPoint quarter degree degreeAtLeastTwo index)
      (Power.Unit.Circuit.Point.unitCircuitPoint quarter degree degreeAtLeastTwo (index + 1) -
        Power.Unit.Circuit.Point.unitCircuitPoint quarter degree degreeAtLeastTwo index) time)
  have realLower : (1 : Fraction.Rational) ≤ value.re :=
    unitCircuitRotatedLine_real_ge_one quarter degree degreeAtLeastTwo
      indexBound timeInside
  have realSquare : (1 : Fraction.Rational) ≤ value.re ^ 2 := by
    have powered := Fraction.Order.Arithmetic.pow_le_pow_direct
      (by decide : (0 : Fraction.Rational) ≤ 1) realLower 2
    simpa only [one_pow] using powered
  exact realSquare.trans (le_add_of_nonneg_right
    (Fraction.Order.Arithmetic.sq_nonneg_direct value.im))
end Purelib.RootIsolation.Power.Unit.Circuit.Clearance

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

namespace Purelib.RootIsolation.Power.Unit.Circuit.Clearance

open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Norm.Basic (normSq_mul)

/-- Every point of the original retained quarter chord has quadrance at least one half. -/
theorem unitCircuitCoordinateLine_normSq_ge_half
    (quarter : UnitCircuitQuarter) (degree : RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) {index : Nat}
    (indexBound : index < Power.Unit.Circuit.Subdivision.unitCircuitStepCount degree degreeAtLeastTwo)
    {time : Fraction.Rational} (timeInside : (0 : Fraction.Rational) ≤ time ∧ time ≤ 1) :
    (1 / 2 : Fraction.Rational) ≤ normSq (Affine.line
      (Power.Unit.Circuit.Point.unitCircuitPoint quarter degree degreeAtLeastTwo index)
      (Power.Unit.Circuit.Point.unitCircuitPoint quarter degree degreeAtLeastTwo (index + 1) -
        Power.Unit.Circuit.Point.unitCircuitPoint quarter degree degreeAtLeastTwo index) time) := by
  let point := Affine.line
    (Power.Unit.Circuit.Point.unitCircuitPoint quarter degree degreeAtLeastTwo index)
    (Power.Unit.Circuit.Point.unitCircuitPoint quarter degree degreeAtLeastTwo (index + 1) -
      Power.Unit.Circuit.Point.unitCircuitPoint quarter degree degreeAtLeastTwo index) time
  have rotatedLower := unitCircuitRotatedLine_normSq_ge_one quarter degree
    degreeAtLeastTwo indexBound timeInside
  rw [Dense.Gaussian.UnitCircle.Rotation.unitCircuitRotatedCoordinate_eval, normSq_mul,
    Geometry.Gaussian.UnitCircle.Quarter.unitCircuitRotation_normSq] at rotatedLower
  apply (Fraction.Order.Field.div_le_iff_pos
    (show (0 : Fraction.Rational) < 2 by decide)).2
  calc
    (1 : Fraction.Rational) ≤ 2 * normSq point := rotatedLower
    _ = normSq point * 2 := by ring1
end Purelib.RootIsolation.Power.Unit.Circuit.Clearance

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

namespace Purelib.RootIsolation.Power.Unit.Circuit.Clearance

open Purelib.Data.Gaussian

/-- The same chord carries a coordinate clearance; it follows from the
rotated real-coordinate bound and the exact norm two of the rotation. -/
def unitCircuitCoordinateEdgeCertificate
    (quarter : UnitCircuitQuarter) (degree : RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) {index : Nat}
    (indexBound : index < Power.Unit.Circuit.Subdivision.unitCircuitStepCount degree degreeAtLeastTwo) :
    Certificate
      (Dense.Gaussian.Path.Components.pathReal
        Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial
        (Power.Unit.Circuit.Point.unitCircuitPoint quarter degree degreeAtLeastTwo index)
        (Power.Unit.Circuit.Point.unitCircuitPoint quarter degree degreeAtLeastTwo (index + 1) -
          Power.Unit.Circuit.Point.unitCircuitPoint quarter degree degreeAtLeastTwo index))
      (Dense.Gaussian.Path.Components.pathImag
        Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial
        (Power.Unit.Circuit.Point.unitCircuitPoint quarter degree degreeAtLeastTwo index)
        (Power.Unit.Circuit.Point.unitCircuitPoint quarter degree degreeAtLeastTwo (index + 1) -
          Power.Unit.Circuit.Point.unitCircuitPoint quarter degree degreeAtLeastTwo index))
      { lower := 0, upper := 1, valid := by decide } where
  bound := 1 / 2
  positive := by decide
  lower := by
    intro time timeInside
    simpa only [Dense.Gaussian.Path.Components.eval_pathReal,
      Dense.Gaussian.Path.Components.eval_pathImag,
      Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial_eval, normSq] using
      unitCircuitCoordinateLine_normSq_ge_half quarter degree degreeAtLeastTwo
        indexBound timeInside
end Purelib.RootIsolation.Power.Unit.Circuit.Clearance

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

namespace Purelib.RootIsolation.Power.Unit.Circuit.Clearance

open Purelib.Data.Gaussian

/-- Quantitative nonvanishing of one rotated stereographic chord. -/
def unitCircuitRotatedEdgeCertificate
    (quarter : UnitCircuitQuarter) (degree : RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) {index : Nat}
    (indexBound : index < Power.Unit.Circuit.Subdivision.unitCircuitStepCount degree degreeAtLeastTwo) :
    Certificate
      (Dense.Gaussian.Path.Components.pathReal (Dense.Gaussian.UnitCircle.Rotation.unitCircuitRotatedCoordinate quarter)
        (Power.Unit.Circuit.Point.unitCircuitPoint quarter degree degreeAtLeastTwo index)
        (Power.Unit.Circuit.Point.unitCircuitPoint quarter degree degreeAtLeastTwo (index + 1) -
          Power.Unit.Circuit.Point.unitCircuitPoint quarter degree degreeAtLeastTwo index))
      (Dense.Gaussian.Path.Components.pathImag (Dense.Gaussian.UnitCircle.Rotation.unitCircuitRotatedCoordinate quarter)
        (Power.Unit.Circuit.Point.unitCircuitPoint quarter degree degreeAtLeastTwo index)
        (Power.Unit.Circuit.Point.unitCircuitPoint quarter degree degreeAtLeastTwo (index + 1) -
          Power.Unit.Circuit.Point.unitCircuitPoint quarter degree degreeAtLeastTwo index))
      { lower := 0, upper := 1, valid := by decide } where
  bound := 1
  positive := by decide
  lower := by
    intro time timeInside
    simpa only [Dense.Gaussian.Path.Components.eval_pathReal,
      Dense.Gaussian.Path.Components.eval_pathImag, normSq] using
      unitCircuitRotatedLine_normSq_ge_one quarter degree degreeAtLeastTwo
        indexBound timeInside
end Purelib.RootIsolation.Power.Unit.Circuit.Clearance

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

namespace Purelib.RootIsolation.Power.Unit.Circuit.Clearance

open Purelib.Data.Gaussian

/-- The finite right-half-plane formula for one rotated rational quarter
edge. -/
theorem unitCircuitRotatedEdgeHalfPlaneFormula
    (quarter : UnitCircuitQuarter) (degree : RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) {index : Nat}
    (indexBound : index < Power.Unit.Circuit.Subdivision.unitCircuitStepCount degree degreeAtLeastTwo) :
    Dense.Rational.CauchyIndex.HalfPlane.Formula
      (Dense.Gaussian.Path.Components.pathReal (Dense.Gaussian.UnitCircle.Rotation.unitCircuitRotatedCoordinate quarter)
        (Power.Unit.Circuit.Point.unitCircuitPoint quarter degree degreeAtLeastTwo index)
        (Power.Unit.Circuit.Point.unitCircuitPoint quarter degree degreeAtLeastTwo (index + 1) -
          Power.Unit.Circuit.Point.unitCircuitPoint quarter degree degreeAtLeastTwo index))
      (Dense.Gaussian.Path.Components.pathImag (Dense.Gaussian.UnitCircle.Rotation.unitCircuitRotatedCoordinate quarter)
        (Power.Unit.Circuit.Point.unitCircuitPoint quarter degree degreeAtLeastTwo index)
        (Power.Unit.Circuit.Point.unitCircuitPoint quarter degree degreeAtLeastTwo (index + 1) -
          Power.Unit.Circuit.Point.unitCircuitPoint quarter degree degreeAtLeastTwo index)) 0 1 := by
  let source := Power.Unit.Circuit.Point.unitCircuitPoint quarter degree degreeAtLeastTwo index
  let direction :=
    Power.Unit.Circuit.Point.unitCircuitPoint quarter degree degreeAtLeastTwo (index + 1) - source
  let A := Dense.Gaussian.Path.Components.pathReal
    (Dense.Gaussian.UnitCircle.Rotation.unitCircuitRotatedCoordinate quarter) source direction
  let B := Dense.Gaussian.Path.Components.pathImag
    (Dense.Gaussian.UnitCircle.Rotation.unitCircuitRotatedCoordinate quarter) source direction
  let interval : Data.Rat.Interval.Bounds :=
    { lower := 0, upper := 1, valid := by decide }
  let certificate : Certificate A B interval := by
    simpa only [A, B, interval, source, direction] using
      unitCircuitRotatedEdgeCertificate quarter degree degreeAtLeastTwo
        indexBound
  have positive : ∀ time : Fraction.Rational, interval.Contains time →
      0 < A.eval time := by
    intro time timeInside
    have inside : (0 : Fraction.Rational) ≤ time ∧ time ≤ 1 := by
      simpa only [interval, Data.Rat.Interval.Bounds.Contains] using
        timeInside
    have lower := unitCircuitRotatedLine_real_ge_one quarter degree
      degreeAtLeastTwo indexBound inside
    have strict := (show (0 : Fraction.Rational) < 1 by decide).trans_le lower
    simpa only [A, source, direction, Dense.Gaussian.Path.Components.eval_pathReal] using
      strict
  have formula := Dense.Rational.CauchyIndex.HalfPlane.formula_of_positive_real certificate
    (show interval.lower < interval.upper by
      simpa only [interval] using (show (0 : Fraction.Rational) < 1 by decide))
    positive
  simpa only [A, B, source, direction, interval] using formula
end Purelib.RootIsolation.Power.Unit.Circuit.Clearance

end
