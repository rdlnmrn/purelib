module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic

public import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Approximation.Gaussian.Enclosure

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Finite enclosure representations and direct translations

This module instantiates the generic protocol for rational balls, rational
boxes, boxed raw CCL prefixes, finite fast-Cauchy indices, and states of an
arbitrary progressive enclosure process.
-/

namespace Purelib.Approximation.Gaussian.Enclosure.Ball.Distance
open Purelib.Data.Gaussian.Basic.Canonical

section Ball

/-- Two readings of one squared-radius ball are within four times its native squared error. No square root or completed
metric point is used. -/
theorem normSq_sub_le_four_radiusSq {ball :
  Ball} {left right : Data.Gaussian.Basic.Canonical}
    (leftInside : ball.Contains left) (rightInside : ball.Contains right) :
    Data.Gaussian.Norm.Basic.normSq (left - right) ≤ 4 * ball.radiusSq := by
  have centerRight : Data.Gaussian.Norm.Basic.normSq (ball.center - right) ≤ ball.radiusSq := by
    have identity : ball.center - right = -(right - ball.center) := by
      apply Data.Gaussian.Basic.ext <;>
        simp only [Data.Gaussian.Basic.sub_re, Data.Gaussian.Basic.sub_im, Data.Gaussian.Basic.neg_re,
          Data.Gaussian.Basic.neg_im] <;> ring1
    rw [identity, Data.Gaussian.Norm.Basic.normSq_neg]
    exact rightInside
  calc
    Data.Gaussian.Norm.Basic.normSq (left - right) ≤
        2 * (Data.Gaussian.Norm.Basic.normSq (left - ball.center) +
          Data.Gaussian.Norm.Basic.normSq (ball.center - right)) :=
      Data.Gaussian.Norm.Bounds.normSq_sub_le_via left ball.center right
    _ ≤ 2 * (ball.radiusSq + ball.radiusSq) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (add_le_add leftInside centerRight) (by decide)
    _ = 4 * ball.radiusSq := by ring1

end Ball
end Purelib.Approximation.Gaussian.Enclosure.Ball.Distance

end
