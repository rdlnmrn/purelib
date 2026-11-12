module
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Interval.Basic
import Purelib.Data.Rat.Interval.Bounds
import Purelib.Data.Rat.Interval.Width
import Purelib.Geometry.Projective.Chordal.Basic
import Purelib.Geometry.Projective.Line.Gaussian
import Purelib.Geometry.Projective.Line.Hermitian
public import Purelib.Polynomial.Clearance.Pair.Basic
import Purelib.Polynomial.Dense.Gaussian.Components
import Purelib.RationalFunctions.Curve.Basic
import Purelib.RationalFunctions.Curve.Coordinates
import Purelib.RationalFunctions.Curve.Projective.Basic
public import Purelib.RationalFunctions.Curve.Projective.Bounds

open Purelib.Geometry.Projective.Line.Hermitian
open Purelib.Data.Rat.Fraction.Order

open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Interval (Bounds)
open Purelib.Polynomial.Clearance.Pair.Basic (Certificate)

section
@[expose] public section

/-!
# Quantitative projective bounds for finite rational curves

The homogeneous numerator and denominator of a rational curve are ordinary
finite coordinate polynomials.  Componentwise Horner bounds therefore give
an explicit Lipschitz coefficient for their projective cross product.  Once
the denominator coordinates carry a positive Bézout clearance on a bounded
parameter interval, this becomes a squared-chordal image bound proportional
to the square of the parameter width.

No affine division, square root, completed point, or limiting argument is
used.  The result is the finite shrinking-cylinder estimate needed to compare
a persistent curve event with a simultaneously shrinking winding box.
-/

namespace Purelib.RationalFunctions.Curve.Projective

section
open Purelib.Data
open Purelib.Polynomial
section
open Purelib.RationalFunctions
/-- Compute a squared-chordal variation coefficient from a positive denominator clearance.

Divide the homogeneous cross-product variation coefficient by the square of the retained clearance bound on the
parameter interval. -/
def chordalVariationCoefficient
    (curve : RationalCurve) (interval : Bounds)
    (clearance : Certificate
      (Coordinates.denominatorReal curve)
      (Coordinates.denominatorImaginary curve)
      interval) : Rational :=
  crossVariationCoefficient curve interval / clearance.bound ^ 2

/-- The squared-chordal variation coefficient is nonnegative. -/
theorem chordalVariationCoefficient_nonneg
    (curve : RationalCurve) (interval : Bounds)
    (clearance : Certificate
      (Coordinates.denominatorReal curve)
      (Coordinates.denominatorImaginary curve)
      interval) :
    0 ≤ chordalVariationCoefficient curve interval clearance :=
  Field.div_nonneg_direct
    (crossVariationCoefficient_nonneg curve interval)
    (Arithmetic.sq_nonneg_direct clearance.bound)

/-- The retained clearance bounds denominator quadrance below throughout the parameter interval. -/
theorem denominatorNormSq_lower
    (curve : RationalCurve) (interval : Bounds)
    (clearance : Certificate
      (Coordinates.denominatorReal curve)
      (Coordinates.denominatorImaginary curve)
      interval)
    {parameter : Rational} (inside : interval.Contains parameter) :
    clearance.bound ≤ Gaussian.Norm.Basic.normSq (curve.denominatorAt parameter) := by
  simpa only [Coordinates.denominatorReal,
    Coordinates.denominatorImaginary,
    Dense.Gaussian.Components.eval_realPart,
    Dense.Gaussian.Components.eval_imagPart,
    RationalCurve.denominatorAt, Gaussian.Norm.Basic.normSq] using
      clearance.lower parameter inside

/-- A retained positive clearance makes the homogeneous denominator nonzero throughout the interval. -/
theorem denominatorAt_ne
    (curve : RationalCurve) (interval : Bounds)
    (clearance : Certificate
      (Coordinates.denominatorReal curve)
      (Coordinates.denominatorImaginary curve)
      interval)
    {parameter : Rational} (inside : interval.Contains parameter) :
    curve.denominatorAt parameter ≠ 0 := by
  intro denominatorZero
  have lower := denominatorNormSq_lower curve interval clearance inside
  rw [denominatorZero, Gaussian.Norm.Basic.normSq_zero] at lower
  exact (not_lt_of_ge lower) clearance.positive

end

open Purelib.Geometry in
open Purelib.RationalFunctions in
/-- A positive denominator clearance gives a nonzero homogeneous coordinate throughout the interval. -/
theorem projective_valid
    (curve : RationalCurve) (interval : Bounds)
    (clearance : Certificate
      (Coordinates.denominatorReal curve)
      (Coordinates.denominatorImaginary curve)
      interval)
    {parameter : Rational} (inside : interval.Contains parameter) :
    Projective.Line.Gaussian.Proj.HasNonzeroCoordinate
      (projective curve parameter) :=
  Or.inr (denominatorAt_ne curve interval clearance inside)

end

open Purelib.Algebra in
open Purelib.Data in
open Purelib.Polynomial in
open Purelib.Geometry in
open Purelib.RationalFunctions in
/-- Squared chordal separation is bounded by the variation coefficient times squared parameter displacement.

Both parameters lie in the clearance interval. Their positive denominator quadrances bound the projective weights below
and permit division of the homogeneous cross-product estimate. -/
theorem chordalSq_projective_le
    (curve : RationalCurve) (interval : Bounds)
    (clearance : Certificate
      (Coordinates.denominatorReal curve)
      (Coordinates.denominatorImaginary curve)
      interval)
    {left right : Rational}
    (leftInside : interval.Contains left)
    (rightInside : interval.Contains right) :
    Projective.Chordal.Basic.chordalSq
        (projective curve left) (projective curve right) ≤
      chordalVariationCoefficient curve interval clearance *
        (left - right) ^ 2 := by
  let leftPoint := projective curve left
  let rightPoint := projective curve right
  let actualDenominator :=
    Proj.weight leftPoint *
      Proj.weight rightPoint
  let clearanceSq := clearance.bound ^ 2
  let upper := crossVariationCoefficient curve interval * (left - right) ^ 2
  have leftValid := projective_valid curve interval clearance leftInside
  have rightValid := projective_valid curve interval clearance rightInside
  have actualPositive : 0 < actualDenominator :=
    Arithmetic.mul_pos_direct
      (Proj.weight_pos leftValid)
      (Proj.weight_pos rightValid)
  have clearanceSqPositive : 0 < clearanceSq :=
    Arithmetic.pow_pos_direct clearance.positive 2
  have leftWeightLower : clearance.bound ≤
      Proj.weight leftPoint := by
    change clearance.bound ≤
      Gaussian.Norm.Basic.normSq (curve.numeratorAt left) + Gaussian.Norm.Basic.normSq
        (curve.denominatorAt left)
    exact (denominatorNormSq_lower curve interval clearance leftInside).trans
      (le_add_of_nonneg_left (Gaussian.Norm.Basic.normSq_nonneg (curve.numeratorAt left)))
  have rightWeightLower : clearance.bound ≤
      Proj.weight rightPoint := by
    change clearance.bound ≤
      Gaussian.Norm.Basic.normSq (curve.numeratorAt right) + Gaussian.Norm.Basic.normSq
        (curve.denominatorAt right)
    exact (denominatorNormSq_lower curve interval clearance rightInside).trans
      (le_add_of_nonneg_left (Gaussian.Norm.Basic.normSq_nonneg (curve.numeratorAt right)))
  have actualLower : clearanceSq ≤ actualDenominator := by
    dsimp only [clearanceSq, actualDenominator]
    simpa only [pow_two] using
      (Arithmetic.mul_le_mul_direct
        leftWeightLower rightWeightLower clearance.positive.le
        (Proj.weight_pos leftValid).le)
  have upperNonnegative : 0 ≤ upper :=
    Arithmetic.mul_nonneg_direct
      (crossVariationCoefficient_nonneg curve interval)
      (Arithmetic.sq_nonneg_direct (left - right))
  calc
    Projective.Chordal.Basic.chordalSq leftPoint rightPoint =
        Gaussian.Norm.Basic.normSq (Proj.cross leftPoint rightPoint) /
          actualDenominator := rfl
    _ ≤ upper / actualDenominator := by
      apply (Field.div_le_iff_pos actualPositive).2
      have cancel : upper / actualDenominator * actualDenominator = upper :=
        Rat.Fraction.Field.div_mul_cancel_of_ne upper actualDenominator
          actualPositive.ne'
      rw [cancel]
      exact normSq_cross_le curve interval leftInside rightInside
    _ ≤ upper / clearanceSq :=
      Field.div_le_div_of_nonneg_left_direct
        upperNonnegative clearanceSqPositive actualLower
    _ = chordalVariationCoefficient curve interval clearance *
        (left - right) ^ 2 := by
      simp only [chordalVariationCoefficient,
        Field.ExplicitField.div_eq_mul_inv]
      rw [Rat.Fraction.Field.mul_assoc,
        Rat.Fraction.Field.mul_comm ((left - right) ^ 2),
        ← Rat.Fraction.Field.mul_assoc]

open Purelib.Data in
open Purelib.Polynomial in
open Purelib.Geometry in
open Purelib.RationalFunctions in
/-- Squared chordal separation on a cleared interval is at most the variation coefficient times squared interval width.

The two parameters lie in the same interval and share its positive denominator clearance. -/
theorem chordalSq_projective_le_width
    (curve : RationalCurve) (interval : Bounds)
    (clearance : Certificate
      (Coordinates.denominatorReal curve)
      (Coordinates.denominatorImaginary curve)
      interval)
    {left right : Rational}
    (leftInside : interval.Contains left)
    (rightInside : interval.Contains right) :
    Projective.Chordal.Basic.chordalSq
        (projective curve left) (projective curve right) ≤
      chordalVariationCoefficient curve interval clearance *
        (Bounds.width interval) ^ 2 :=
  (chordalSq_projective_le curve interval clearance leftInside rightInside).trans
    (Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Rat.Interval.parameter_sub_sq_le_width_sq interval leftInside rightInside)
      (chordalVariationCoefficient_nonneg curve interval clearance))

end Purelib.RationalFunctions.Curve.Projective

end
