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

open Purelib.Data.Gaussian.Norm
open Purelib.Data.Rat.Fraction.Order

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
      4 * (left.radiusSq * Basic.normSq right.center +
        Basic.normSq left.center * right.radiusSq) +
      2 * (left.radiusSq * right.radiusSq)
    radiusSq_nonneg := by
      exact add_nonneg
        (Arithmetic.mul_nonneg_direct (by decide)
          (add_nonneg
            (Arithmetic.mul_nonneg_direct
              left.radiusSq_nonneg (Basic.normSq_nonneg right.center))
            (Arithmetic.mul_nonneg_direct
              (Basic.normSq_nonneg left.center) right.radiusSq_nonneg)))
        (Arithmetic.mul_nonneg_direct (by decide)
          (Arithmetic.mul_nonneg_direct
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
      Basic.normSq (dx * right.center) ≤
        left.radiusSq * Basic.normSq right.center := by
    rw [Basic.normSq_mul]
    exact Arithmetic.mul_le_mul_of_nonneg_right_direct
      xInside (Basic.normSq_nonneg right.center)
  have secondTerm :
      Basic.normSq (left.center * dy) ≤
        Basic.normSq left.center * right.radiusSq := by
    rw [Basic.normSq_mul]
    exact Arithmetic.mul_le_mul_of_nonneg_left_direct
      yInside (Basic.normSq_nonneg left.center)
  have productTerm : Basic.normSq (dx * dy) ≤
      left.radiusSq * right.radiusSq := by
    rw [Basic.normSq_mul]
    have firstScaled :=
      Arithmetic.mul_le_mul_of_nonneg_right_direct
        xInside (Basic.normSq_nonneg dy)
    exact firstScaled.trans
      (Arithmetic.mul_le_mul_of_nonneg_left_direct
        yInside left.radiusSq_nonneg)
  unfold Contains mul
  rw [difference]
  calc
    Basic.normSq ((dx * right.center + left.center * dy) + dx * dy) ≤
        2 * (Basic.normSq (dx * right.center + left.center * dy) +
          Basic.normSq (dx * dy)) := Bounds.normSq_add_le_two _ _
    _ ≤ 2 *
        (2 * (Basic.normSq (dx * right.center) + Basic.normSq
          (left.center * dy)) +
          Basic.normSq (dx * dy)) := by
      exact Arithmetic.mul_le_mul_of_nonneg_left_direct
        (add_le_add (Bounds.normSq_add_le_two _ _) le_rfl) (by decide)
    _ ≤ 2 *
        (2 * (left.radiusSq * Basic.normSq right.center +
          Basic.normSq left.center * right.radiusSq) +
          left.radiusSq * right.radiusSq) := by
      apply Arithmetic.mul_le_mul_of_nonneg_left_direct
      · apply add_le_add
        · exact Arithmetic.mul_le_mul_of_nonneg_left_direct
            (add_le_add firstTerm secondTerm) (by decide)
        · exact productTerm
      · decide
    _ = 4 * (left.radiusSq * Basic.normSq right.center +
          Basic.normSq left.center * right.radiusSq) +
        2 * (left.radiusSq * right.radiusSq) := by ring1

/-- Enclose a finite natural power by multiplying the previous enclosure by the same original input ball.

The zero power is the exact unit ball. Positive powers consume the original
input enclosure at every factor and retain the existing multiplication bounds.
-/
def pow (ball : Ball) : Nat → Ball
  | 0 => point 1
  | exponent + 1 => (ball.pow exponent).mul ball

/-- Zero ball power is the complete exact-unit enclosure. -/
theorem pow_zero (ball : Ball) : ball.pow 0 = point 1 := rfl

/-- Each positive ball power multiplies its previous enclosure by the original input ball. -/
theorem pow_succ (ball : Ball) (exponent : Nat) :
    ball.pow (exponent + 1) = (ball.pow exponent).mul ball := rfl

/-- The power enclosure's center is the natural power of its same original input center. -/
theorem pow_center (ball : Ball) (exponent : Nat) :
    (ball.pow exponent).center = ball.center ^ exponent := by
  induction exponent with
  | zero => rfl
  | succ exponent previous =>
      change (ball.pow exponent).center * ball.center = _
      rewrite [previous, _root_.pow_succ]
      rfl

/-- A finite power enclosure contains powers of every reading admitted by the original input ball. -/
theorem contains_pow {ball : Ball} {value : Data.Gaussian.Basic.Canonical}
    (inside : ball.Contains value) (exponent : Nat) : (ball.pow exponent).Contains (value ^ exponent) := by
  induction exponent with
  | zero => exact contains_point 1
  | succ exponent previous =>
      rewrite [_root_.pow_succ]
      exact contains_mul previous inside

end Ball

end Purelib.Approximation.Gaussian.Enclosure.Ball

end
