module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Segment.Increment
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate

import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order
public import Purelib.Data.Rat.Interval.Basic
public import Purelib.Geometry.Rational.Affine
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.Ring

open Purelib.Data

open Purelib.Data.Rat

open Purelib

open Purelib.Geometry.Rational

open Purelib.Polynomial

section
@[expose] public section

/-!
# Whole-segment comparison of finite polynomial primitives

A uniform bound on the difference of two polynomial coefficients controls
their primitive increments.  Finite midpoint refinement eliminates the
Taylor remainder, so the final bound has no polynomial-degree-dependent
error floor.  Constant terms of either primitive are irrelevant.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Primitive.Segment.Comparison.DensePrimitive

open Purelib.Data.Gaussian.Basic.Canonical
section

variable {leftCoefficient rightCoefficient :
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {leftBox rightBox :
  Box}

/-- Compare arbitrary checked primitive representations along a common
affine segment.  A unit sign may be any displayed Gaussian of squared norm
one; the sheet application uses only `1` and `-1`. -/
theorem difference_increment_le
    (left : Dense.Gaussian.Primitive.Certificate.DensePrimitive leftCoefficient leftBox) (right :
      Dense.Gaussian.Primitive.Certificate.DensePrimitive rightCoefficient rightBox)
    (sign origin direction : Gaussian.Basic.Canonical) (signNorm : Data.Gaussian.Norm.Basic.normSq sign = 1)
      (interval : Data.Rat.Interval.Bounds)
    (leftInside : ∀ parameter, interval.Contains parameter → leftBox.Contains (Affine.line origin direction parameter))
    (rightInside : ∀ parameter, interval.Contains parameter → rightBox.Contains (Affine.line origin direction
      parameter))
    (bound : Fraction.Rational)
    (coefficientBound : ∀ parameter, interval.Contains parameter →
      Data.Gaussian.Norm.Basic.normSq (leftCoefficient.eval (Affine.line origin direction parameter) -
        sign * rightCoefficient.eval (Affine.line origin direction parameter)) ≤ bound)
    {first last : Fraction.Rational} (firstInside : interval.Contains first) (lastInside : interval.Contains last) :
    Data.Gaussian.Norm.Basic.normSq ((left.value.eval (Affine.line origin direction first) -
        left.value.eval (Affine.line origin direction last)) -
      sign * (right.value.eval (Affine.line origin direction first) -
        right.value.eval (Affine.line origin direction last))) ≤
      2 * bound * Data.Gaussian.Norm.Basic.normSq direction * (first - last) ^ 2 := open Purelib.Approximation in by
  let value := fun parameter => left.value.eval (Affine.line origin direction parameter) -
    sign * right.value.eval (Affine.line origin direction parameter)
  let remainder := 4 * (left.remainderBound + right.remainderBound) * Data.Gaussian.Norm.Basic.normSq direction ^ 2
  have remainderNonnegative : 0 ≤ remainder := Fraction.Order.Arithmetic.mul_nonneg_direct
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (add_nonneg left.remainderBound_nonnegative right.remainderBound_nonnegative))
    (Fraction.Order.Arithmetic.sq_nonneg_direct _)
  have localBound {x y : Fraction.Rational} (xInside : interval.Contains x) (yInside : interval.Contains y) :
      Data.Gaussian.Norm.Basic.normSq (value x - value y) ≤ (2 * bound * Data.Gaussian.Norm.Basic.normSq
        direction) * (x - y) ^ 2 + remainder * (x - y) ^ 4 := by
    let start := Affine.line origin direction y
    let finish := Affine.line origin direction x
    let movement := finish - start
    let coefficient := leftCoefficient.eval start - sign * rightCoefficient.eval start
    let leftError := left.value.eval finish - left.value.eval start - leftCoefficient.eval start * movement
    let rightError := right.value.eval finish - right.value.eval start - rightCoefficient.eval start * movement
    have leftTaylor : Data.Gaussian.Norm.Basic.normSq leftError ≤ left.remainderBound *
      Data.Gaussian.Norm.Basic.normSq movement ^ 2 :=
      left.increment_bound (start := start) (finish := finish) (leftInside y yInside) (leftInside x xInside)
    have rightTaylor : Data.Gaussian.Norm.Basic.normSq (sign * rightError) ≤ right.remainderBound *
      Data.Gaussian.Norm.Basic.normSq movement ^ 2 := by
      rw [Gaussian.Norm.Basic.normSq_mul, signNorm, Fraction.Field.one_mul]
      exact right.increment_bound (start := start) (finish := finish) (rightInside y yInside) (rightInside x xInside)
    have taylor : Data.Gaussian.Norm.Basic.normSq (leftError - sign * rightError) ≤
        2 * (left.remainderBound + right.remainderBound) * Data.Gaussian.Norm.Basic.normSq movement ^ 2 :=
      (Gaussian.Norm.Bounds.normSq_sub_le_two _ _).trans ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (add_le_add leftTaylor rightTaylor) (by decide)).trans_eq (by ring1))
    have linear : Data.Gaussian.Norm.Basic.normSq (coefficient * movement) ≤ bound *
      Data.Gaussian.Norm.Basic.normSq movement := by
      rw [Gaussian.Norm.Basic.normSq_mul]
      exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (coefficientBound y yInside)
        (Gaussian.Norm.Basic.normSq_nonneg _)
    have identity : value x - value y = (leftError - sign * rightError) + coefficient * movement := by
      dsimp only [value, leftError, rightError, coefficient, movement, start, finish]
      ring1
    have distance : Data.Gaussian.Norm.Basic.normSq movement = Data.Gaussian.Norm.Basic.normSq direction * (x -
      y) ^ 2 := Affine.normSq_line_sub origin direction x y
    rw [identity]
    calc
      _ ≤ 2 * (Data.Gaussian.Norm.Basic.normSq (leftError - sign * rightError) + Data.Gaussian.Norm.Basic.normSq
        (coefficient * movement)) := Gaussian.Norm.Bounds.normSq_add_le_two _ _
      _ ≤ 2 * ((2 * (left.remainderBound + right.remainderBound) * Data.Gaussian.Norm.Basic.normSq movement ^ 2) +
        bound * Data.Gaussian.Norm.Basic.normSq movement) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add taylor linear) (by decide)
      _ = _ := by rw [distance]; dsimp only [remainder]; ring1
  have estimate := Gaussian.Segment.Increment.remove_quartic value interval
    (2 * bound * Data.Gaussian.Norm.Basic.normSq direction) remainder remainderNonnegative localBound firstInside
      lastInside
  have identity : (left.value.eval (Affine.line origin direction first) -
        left.value.eval (Affine.line origin direction last)) -
      sign * (right.value.eval (Affine.line origin direction first) -
        right.value.eval (Affine.line origin direction last)) = value first - value last := by dsimp only [value]; ring1
  rw [identity]
  exact estimate

end

end Purelib.Polynomial.Dense.Gaussian.Primitive.Segment.Comparison.DensePrimitive

end
