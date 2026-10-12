module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Field
public import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring
import Purelib.Algebra.NatCast

section
public section

/-!
# Indexed weighted bounds for displayed Gaussian balls

The original positive index weight controls the center quadrance and the
retained enclosure radius in one rational upper bound.
-/

namespace Purelib.Approximation.Gaussian.Enclosure.Ball.WeightedBound

open Purelib.Algebra

open Purelib

open Purelib.Approximation.Gaussian.Enclosure

open Purelib.Data.Rat

/-- Positive rational weight used by the indexed square-root-free triangle bound. Increasing the index makes the
coefficient of the centre norm tend to one. -/
@[expose] def weight (index : Nat) : Fraction.Rational := index + 1

/-- The successor-index rational weight is strictly positive.

Its natural successor supplies a strictly positive rational cast, with the original weight operation and index
unchanged. -/
theorem weight_positive (index : Nat) : 0 < Purelib.Approximation.Gaussian.Enclosure.Ball.WeightedBound.weight index :=
  by
  unfold Approximation.Gaussian.Enclosure.Ball.WeightedBound.weight
  simpa only [NatCast.add, Nat.cast_one] using
    (Fraction.Cast.Order.natCast_pos_direct
      (n := index + 1) (Nat.zero_lt_succ index))

/-- Executable upper norm-square bound for every point admitted by a ball. -/
@[expose] def weightedUpper (index : Nat) (ball : Ball) : Fraction.Rational :=
  (Approximation.Gaussian.Enclosure.Ball.WeightedBound.weight index + 1) * ball.radiusSq +
    ((Approximation.Gaussian.Enclosure.Ball.WeightedBound.weight index + 1) /
      Approximation.Gaussian.Enclosure.Ball.WeightedBound.weight index) * Data.Gaussian.Norm.Basic.normSq
      ball.center

/-- Passing the indexed weighted bound places every admitted point strictly inside the requested norm-square target. -/
theorem normSq_lt_of_weightedUpper {index : Nat} {ball : Ball}
    {target : Fraction.Rational} (small : Approximation.Gaussian.Enclosure.Ball.WeightedBound.weightedUpper index ball <
      target)
    {value : Data.Gaussian.Basic.Canonical} (inside : ball.Contains value) :
    Data.Gaussian.Norm.Basic.normSq value < target := by
  have decomposition : value = (value - ball.center) + ball.center := by
    apply Data.Gaussian.Basic.ext <;>
      simp only [Data.Gaussian.Basic.sub_re, Data.Gaussian.Basic.sub_im, Data.Gaussian.Basic.add_re,
        Data.Gaussian.Basic.add_im] <;> ring1
  rw [decomposition]
  exact (Data.Gaussian.Norm.Bounds.normSq_add_le_weighted (Approximation.Gaussian.Enclosure.Ball.WeightedBound.weight
    index) (Approximation.Gaussian.Enclosure.Ball.WeightedBound.weight_positive index)
      (value - ball.center) ball.center).trans_lt
    (lt_of_le_of_lt
      (add_le_add
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          inside
          (add_nonneg (Approximation.Gaussian.Enclosure.Ball.WeightedBound.weight_positive index).le (by decide)))
        le_rfl)
      small)
end Purelib.Approximation.Gaussian.Enclosure.Ball.WeightedBound

end
