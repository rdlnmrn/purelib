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
public import Purelib.Data.Rat.Interval.Basic
public import Purelib.Geometry.Rational.Affine

import Purelib.Data.Rat.Fraction.Compatibility
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.Ring

open Purelib.Data

open Purelib.Data.Rat

open Purelib

open Purelib.Geometry.Rational

open Purelib.Polynomial

@[expose] public section

/-!
# Whole-segment increments of a bounded finite polynomial primitive

The finite subdivision theorem removes the Taylor remainder.  The resulting
coefficient ceiling does not depend on the primitive degree and is suitable
for boundary traces whose number of sample segments keeps growing.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Primitive.Segment.Bounds.DensePrimitive

open Purelib.Data.Gaussian.Basic.Canonical

/-- A uniform coefficient bound controls the primitive increment along a segment.

The segment stays in the primitive's box; the squared increment is bounded by twice the coefficient ceiling times the
direction norm and squared parameter displacement. -/
theorem segment_increment_le {coefficient : Basic.CanonicalCoefficients.CoefficientPolynomial} {box : Box}
    (primitive : Dense.Gaussian.Primitive.Certificate.DensePrimitive coefficient box) (origin direction :
      Gaussian.Basic.Canonical) (interval : Data.Rat.Interval.Bounds)
    (inside : ∀ parameter, interval.Contains parameter → box.Contains (Affine.line origin direction parameter))
    (bound : Fraction.Rational) (coefficientBound : ∀ parameter, interval.Contains parameter →
      Data.Gaussian.Norm.Basic.normSq (coefficient.eval (Affine.line origin direction parameter)) ≤ bound)
    {first last : Fraction.Rational} (firstInside : interval.Contains first) (lastInside : interval.Contains last) :
    Data.Gaussian.Norm.Basic.normSq (primitive.value.eval (Affine.line origin direction first) -
      primitive.value.eval (Affine.line origin direction last)) ≤
        2 * bound * Data.Gaussian.Norm.Basic.normSq direction * (first - last) ^ 2 := open Purelib.Approximation in
          by
  let value := fun parameter => primitive.value.eval (Affine.line origin direction parameter)
  let remainder := 2 * primitive.remainderBound * Data.Gaussian.Norm.Basic.normSq direction ^ 2
  have remainderNonnegative : 0 ≤ remainder := Fraction.Order.Arithmetic.mul_nonneg_direct
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) primitive.remainderBound_nonnegative)
    (Fraction.Order.Arithmetic.sq_nonneg_direct _)
  have localBound {x y : Fraction.Rational} (xInside : interval.Contains x) (yInside : interval.Contains y) :
      Data.Gaussian.Norm.Basic.normSq (value x - value y) ≤ (2 * bound * Data.Gaussian.Norm.Basic.normSq
        direction) * (x - y) ^ 2 + remainder * (x - y) ^ 4 := by
    let start := Affine.line origin direction y
    let finish := Affine.line origin direction x
    let movement := finish - start
    let linear := coefficient.eval start * movement
    let error := value x - value y - linear
    have taylor : Data.Gaussian.Norm.Basic.normSq error ≤ primitive.remainderBound *
      Data.Gaussian.Norm.Basic.normSq movement ^ 2 :=
      primitive.increment_bound (inside y yInside) (inside x xInside)
    have linearLe : Data.Gaussian.Norm.Basic.normSq linear ≤ bound * Data.Gaussian.Norm.Basic.normSq movement :=
      by
      rw [Gaussian.Norm.Basic.normSq_mul]
      exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (coefficientBound y yInside)
        (Gaussian.Norm.Basic.normSq_nonneg movement)
    have distance : Data.Gaussian.Norm.Basic.normSq movement = Data.Gaussian.Norm.Basic.normSq direction * (x -
      y) ^ 2 := Affine.normSq_line_sub origin direction x y
    rw [show value x - value y = error + linear by dsimp only [error]; ring1]
    exact (Gaussian.Norm.Bounds.normSq_add_le_two error linear).trans
      ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add taylor linearLe) (by decide)).trans_eq
        (by
        rw [distance]
        dsimp only [remainder]
        ring1))
  exact Gaussian.Segment.Increment.remove_quartic value interval
    (2 * bound * Data.Gaussian.Norm.Basic.normSq direction) remainder remainderNonnegative localBound firstInside
      lastInside

end Purelib.Polynomial.Dense.Gaussian.Primitive.Segment.Bounds.DensePrimitive
