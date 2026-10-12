module
public import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
public import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Approximation.Gaussian.Enclosure

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Finite squared-error enclosures for constructive CCL arithmetic

The standalone CCL word remains a list of bits.  Arithmetic uses a proof
sidecar: a rational centre and a rational squared Euclidean error.  The
operations below transport these finite certificates directly.  They do not
name completed limits or collections of compatible points.
-/

namespace Purelib.Approximation.Gaussian.Enclosure.Ball
section Ball

/-- Multiplication transports both first-order errors and their product. -/
def mul (left right : Ball) : Ball
  :=
  { center := left.center * right.center
    radiusSq :=
      4 * (left.radiusSq * Data.Gaussian.Norm.Basic.normSq right.center +
        Data.Gaussian.Norm.Basic.normSq left.center * right.radiusSq) +
      2 * (left.radiusSq * right.radiusSq)
    radiusSq_nonneg := by
      exact add_nonneg
        (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
          (add_nonneg
            (Fraction.Order.Arithmetic.mul_nonneg_direct
              left.radiusSq_nonneg (Data.Gaussian.Norm.Basic.normSq_nonneg right.center))
            (Fraction.Order.Arithmetic.mul_nonneg_direct
              (Data.Gaussian.Norm.Basic.normSq_nonneg left.center) right.radiusSq_nonneg)))
        (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
          (Fraction.Order.Arithmetic.mul_nonneg_direct
            left.radiusSq_nonneg right.radiusSq_nonneg)) }

/-- The product ball admits products of readings admitted by the two original balls.

Its squared-error allowance pays both first-order errors and their product using explicit finite norm bounds. -/
theorem contains_mul {left right : Ball} {x y
  : Data.Gaussian.Basic.Canonical}
    (xInside : left.Contains x) (yInside : right.Contains y) :
    (left.mul right).Contains (x * y) := by
  let dx := x - left.center
  let dy := y - right.center
  have difference :
      x * y - left.center * right.center =
        (dx * right.center + left.center * dy) + dx * dy := by
    dsimp only [dx, dy]
    apply Data.Gaussian.Basic.ext <;>
      simp only [Data.Gaussian.Basic.sub_re, Data.Gaussian.Basic.sub_im, Data.Gaussian.Basic.add_re,
        Data.Gaussian.Basic.add_im, Data.Gaussian.Basic.mul_re, Data.Gaussian.Basic.mul_im] <;> ring1
  have firstTerm :
      Data.Gaussian.Norm.Basic.normSq (dx * right.center) ≤
        left.radiusSq * Data.Gaussian.Norm.Basic.normSq right.center := by
    rw [Data.Gaussian.Norm.Basic.normSq_mul]
    exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      xInside (Data.Gaussian.Norm.Basic.normSq_nonneg right.center)
  have secondTerm :
      Data.Gaussian.Norm.Basic.normSq (left.center * dy) ≤
        Data.Gaussian.Norm.Basic.normSq left.center * right.radiusSq := by
    rw [Data.Gaussian.Norm.Basic.normSq_mul]
    exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      yInside (Data.Gaussian.Norm.Basic.normSq_nonneg left.center)
  have productTerm : Data.Gaussian.Norm.Basic.normSq (dx * dy) ≤
      left.radiusSq * right.radiusSq := by
    rw [Data.Gaussian.Norm.Basic.normSq_mul]
    have firstScaled :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        xInside (Data.Gaussian.Norm.Basic.normSq_nonneg dy)
    exact firstScaled.trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        yInside left.radiusSq_nonneg)
  unfold Contains mul
  rw [difference]
  calc
    Data.Gaussian.Norm.Basic.normSq ((dx * right.center + left.center * dy) + dx * dy) ≤
        2 * (Data.Gaussian.Norm.Basic.normSq (dx * right.center + left.center * dy) +
          Data.Gaussian.Norm.Basic.normSq (dx * dy)) := Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _
    _ ≤ 2 *
        (2 * (Data.Gaussian.Norm.Basic.normSq (dx * right.center) + Data.Gaussian.Norm.Basic.normSq
          (left.center * dy)) +
          Data.Gaussian.Norm.Basic.normSq (dx * dy)) := by
      exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (add_le_add (Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _) le_rfl) (by decide)
    _ ≤ 2 *
        (2 * (left.radiusSq * Data.Gaussian.Norm.Basic.normSq right.center +
          Data.Gaussian.Norm.Basic.normSq left.center * right.radiusSq) +
          left.radiusSq * right.radiusSq) := by
      apply Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      · apply add_le_add
        · exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
            (add_le_add firstTerm secondTerm) (by decide)
        · exact productTerm
      · decide
    _ = 4 * (left.radiusSq * Data.Gaussian.Norm.Basic.normSq right.center +
          Data.Gaussian.Norm.Basic.normSq left.center * right.radiusSq) +
        2 * (left.radiusSq * right.radiusSq) := by ring1
end Ball

end Purelib.Approximation.Gaussian.Enclosure.Ball

end
