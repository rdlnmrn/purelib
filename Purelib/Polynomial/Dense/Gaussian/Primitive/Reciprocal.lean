module

public import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
public import Purelib.Calculus.Jet.Quadratic.Basic
public import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Data.Gaussian.Norm.Reciprocal
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Tactic.Ring

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic

/-!
# Quadratic control of a retained reciprocal-coordinate primitive

The original dense primitive and its box bound control the negative
primitive at reciprocal coordinates. A common positive quadrance floor
pays both actual inverses; the original polynomial and primitive caches
are consumed without constructing another antiderivative.
-/

public section

namespace Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate.DensePrimitive

open Purelib
open Purelib.Data
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction.Order
open Purelib.Geometry.Rational
open Purelib.Calculus.Jet.Quadratic.Basic
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)

variable {polynomial : CoefficientPolynomial} {box : Box}

/-- The common reciprocal floor transports the retained quadratic and coefficient bounds.

The two summands pay the original polynomial Taylor remainder and the
first-order inverse remainder separately. The displayed coefficient bound
is the actual retained original box-Horner value projection.
-/
@[expose] def reciprocalFactor (primitive : DensePrimitive polynomial box) (floor : Fraction.Rational)
    (coefficientBound : { value : Fraction.Rational // value = Bounds.Box.denseEvalNormBound polynomial box }) :
    Fraction.Rational :=
  2 * (primitive.remainderBound * floor⁻¹ ^ 4 + coefficientBound.val * floor⁻¹ ^ 3)

/-- The reciprocal factor is nonnegative for a positive denominator floor. -/
theorem reciprocalFactor_nonnegative (primitive : DensePrimitive polynomial box) {floor : Fraction.Rational}
    (positive : 0 < floor)
    (coefficientBound : { value : Fraction.Rational // value = Bounds.Box.denseEvalNormBound polynomial box }) :
    0 ≤ primitive.reciprocalFactor floor coefficientBound := by
  have coefficientNonnegative : 0 ≤ coefficientBound.val := by
    rewrite [coefficientBound.property]
    exact (Bounds.Box.denseHornerNormBounds_nonneg polynomial box).1
  apply Arithmetic.mul_nonneg_direct (by decide +kernel)
  have added := Arithmetic.add_le_add_direct
      (Arithmetic.mul_nonneg_direct primitive.remainderBound_nonnegative
        (Arithmetic.pow_nonneg_direct (Fraction.Order.Field.inv_pos_direct positive).le 4))
      (Arithmetic.mul_nonneg_direct coefficientNonnegative
        (Arithmetic.pow_nonneg_direct (Fraction.Order.Field.inv_pos_direct positive).le 3))
  simpa only [Fraction.Field.zero_add] using added

/-- Construct the original quadratic certificate for the negative retained primitive at two guarded inverse points.

Both inverse points lie in the same original box. Its retained primitive
ceiling and coefficient bound supply a uniform fourth-order displacement
bound, while the base, slope and output read the actual original caches.
-/
@[expose] def reciprocalCertificate (primitive : DensePrimitive polynomial box) {floor : Fraction.Rational}
    (positive : 0 < floor)
    (coefficientBound : { value : Fraction.Rational // value = Bounds.Box.denseEvalNormBound polynomial box })
    (first last : Canonical) (firstLower : floor ≤ Norm.Basic.normSq first)
    (lastLower : floor ≤ Norm.Basic.normSq last)
    (firstInside : box.Contains first⁻¹) (lastInside : box.Contains last⁻¹) : Certificate (last - first) :=
  let coefficient := polynomial.eval first⁻¹
  let polynomialRemainder := primitive.value.eval last⁻¹ - primitive.value.eval first⁻¹ -
    coefficient * (last⁻¹ - first⁻¹)
  let inverseRemainder := last⁻¹ - first⁻¹ + (last - first) * first⁻¹ ^ 2
  { base := -primitive.value.eval first⁻¹
    slope := coefficient * first⁻¹ ^ 2
    output := -primitive.value.eval last⁻¹
    remainder := -polynomialRemainder - coefficient * inverseRemainder
    expansion := by dsimp only [polynomialRemainder, inverseRemainder]; ring1
    factor := primitive.reciprocalFactor floor coefficientBound
    factor_nonneg := primitive.reciprocalFactor_nonnegative positive coefficientBound
    remainder_le := by
      have original := primitive.increment_bound firstInside lastInside
      have inverseMovement := Norm.Reciprocal.difference_normSq_le positive lastLower firstLower
      have polynomialBound : Norm.Basic.normSq polynomialRemainder ≤
          (primitive.remainderBound * floor⁻¹ ^ 4) * Norm.Basic.normSq (last - first) ^ 2 := by
        exact original.trans ((Arithmetic.mul_le_mul_of_nonneg_left_direct
          (Arithmetic.pow_le_pow_direct (Norm.Basic.normSq_nonneg _) inverseMovement 2)
          primitive.remainderBound_nonnegative).trans_eq (by ring1))
      have coefficientBounded : Norm.Basic.normSq coefficient ≤ coefficientBound.val := by
        rewrite [coefficientBound.property]
        exact Bounds.Box.normSq_eval_le_denseEvalNormBound polynomial firstInside
      have inverseBound : Norm.Basic.normSq (coefficient * inverseRemainder) ≤
          (coefficientBound.val * floor⁻¹ ^ 3) * Norm.Basic.normSq (last - first) ^ 2 := by
        rewrite [Norm.Basic.normSq_mul]
        have inverseBounded := Norm.Reciprocal.quadratic_remainder_normSq_le positive firstLower lastLower
        exact (Arithmetic.mul_le_mul_direct coefficientBounded inverseBounded
          (Norm.Basic.normSq_nonneg inverseRemainder)
          ((Norm.Basic.normSq_nonneg coefficient).trans coefficientBounded)).trans_eq (by ring1)
      have sumBound := Norm.Bounds.normSq_sub_le_two (-polynomialRemainder) (coefficient * inverseRemainder)
      rewrite [Norm.Basic.normSq_neg] at sumBound
      have combined := sumBound.trans (Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Arithmetic.add_le_add_direct polynomialBound inverseBound) (by decide +kernel))
      rewrite [← Norm.Basic.normSq_eq_canonical, ← Norm.Basic.normSq_eq_canonical]
      exact combined.trans_eq (by unfold reciprocalFactor; ring1) }

/-- The reciprocal certificate's base is the negative original primitive at the first inverse coordinate. -/
theorem reciprocalCertificate_base (primitive : DensePrimitive polynomial box) {floor : Fraction.Rational}
    (positive : 0 < floor)
    (coefficientBound : { value : Fraction.Rational // value = Bounds.Box.denseEvalNormBound polynomial box })
    (first last : Canonical) (firstLower : floor ≤ Norm.Basic.normSq first)
    (lastLower : floor ≤ Norm.Basic.normSq last)
    (firstInside : box.Contains first⁻¹) (lastInside : box.Contains last⁻¹) :
    (primitive.reciprocalCertificate positive coefficientBound first last firstLower lastLower
      firstInside lastInside).base = -primitive.value.eval first⁻¹ := rfl

end Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate.DensePrimitive
