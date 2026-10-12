module
import Purelib.Approximation.Rat.Logarithm.Horner.Basic
import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Gaussian.Logarithm.Local.Horner.Basic
import Purelib.Approximation.Rat.Logarithm.Horner.Sensitivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.RationalEmbedding
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib

open Purelib.Approximation.Gaussian.Logarithm.Local

open Purelib.Approximation.Rat.Logarithm.Horner

open Purelib.Approximation.Rat.Logarithm.Horner.Basic

open Purelib.Data.Gaussian

open Purelib.Data.Gaussian.RationalEmbedding

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Finite complex logarithm on a reduced Gaussian-rational disk

For a displayed Gaussian rational `z` with `normSq z <= 1/9`, this module
computes finite truncations of

`2 z (1 + z^2/3 + z^4/5 + ...)`.

The ellipsis is descriptive only.  The implementation is a finite Horner
recurrence indexed by a natural depth.  The input is already the reduced
argument `(u - 1) / (u + 1)`; constructing that quotient, proving its
denominator apart, and selecting a logarithm branch are handled separately.
-/

namespace Purelib.Approximation.Gaussian.Logarithm.Local.Horner.Bounds

/-- A positive-index logarithm Horner product has squared norm at most four ninths when its argument and tail bounds are
one ninth and four. -/
theorem scaled_term_bound {w tail :
  Canonical} {index : Nat}
    (positive : 1 ≤ index) (wBound : Data.Gaussian.Norm.Basic.normSq w ≤ 1 / 9)
    (tailBound : Data.Gaussian.Norm.Basic.normSq tail ≤ 4) :
    Data.Gaussian.Norm.Basic.normSq (ComplexLog.scalar (ComplexLog.coefficient index) * w * tail) ≤ 4 / 9 := by
  rw [Data.Gaussian.Norm.Basic.normSq_mul, Data.Gaussian.Norm.Basic.normSq_mul, RationalEmbedding.normSq_scalar]
  calc
    ComplexLog.coefficient index ^ 2 * Data.Gaussian.Norm.Basic.normSq w *
      Data.Gaussian.Norm.Basic.normSq tail ≤
        1 * (1 / 9 : Fraction.Rational) * 4 :=
      Fraction.Order.Arithmetic.mul_le_mul_direct
        (Fraction.Order.Arithmetic.mul_le_mul_direct
          (Sensitivity.coefficient_sq_le_one positive) wBound
          (Data.Gaussian.Norm.Basic.normSq_nonneg w) (by decide))
        tailBound (Data.Gaussian.Norm.Basic.normSq_nonneg tail)
        (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (by decide))
    _ = 4 / 9 := by decide

/-- A positive-index logarithm Horner step preserves the squared-norm bound four on the displayed reduced disk. -/
theorem step_bound {w tail :
  Canonical} {index : Nat}
    (positive : 1 ≤ index) (wBound : Data.Gaussian.Norm.Basic.normSq w ≤ 1 / 9)
    (tailBound : Data.Gaussian.Norm.Basic.normSq tail ≤ 4) :
    Data.Gaussian.Norm.Basic.normSq (Horner.Basic.step w index tail) ≤ 4 := by
  rw [Horner.Basic.step_eq]
  calc
    Data.Gaussian.Norm.Basic.normSq (1 + ComplexLog.scalar (ComplexLog.coefficient index) * w * tail) ≤
        2 * (Data.Gaussian.Norm.Basic.normSq 1 + Data.Gaussian.Norm.Basic.normSq (ComplexLog.scalar
          (ComplexLog.coefficient index) * w * tail)) :=
      Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _
    _ ≤ 2 * ((1 : Fraction.Rational) + 4 / 9) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (add_le_add le_rfl (scaled_term_bound positive wBound
          tailBound))
        (by decide)
    _ ≤ 4 := by decide

/-- A logarithm Horner product has squared norm at most one quarter for argument bound one ninth and tail bound nine
fourths. -/
theorem scaled_term_bound_quarter {w tail :
  Canonical} {index : Nat}
    (positive : 1 ≤ index) (wBound : Data.Gaussian.Norm.Basic.normSq w ≤ 1 / 9)
    (tailBound : Data.Gaussian.Norm.Basic.normSq tail ≤ 9 / 4) :
    Data.Gaussian.Norm.Basic.normSq (ComplexLog.scalar (ComplexLog.coefficient index) * w * tail) ≤ 1 / 4 := by
  rw [Data.Gaussian.Norm.Basic.normSq_mul, Data.Gaussian.Norm.Basic.normSq_mul, RationalEmbedding.normSq_scalar]
  calc
    ComplexLog.coefficient index ^ 2 * Data.Gaussian.Norm.Basic.normSq w *
      Data.Gaussian.Norm.Basic.normSq tail ≤
        1 * (1 / 9 : Fraction.Rational) * (9 / 4) :=
      Fraction.Order.Arithmetic.mul_le_mul_direct
        (Fraction.Order.Arithmetic.mul_le_mul_direct
          (Sensitivity.coefficient_sq_le_one positive) wBound
          (Data.Gaussian.Norm.Basic.normSq_nonneg w) (by decide))
        tailBound (Data.Gaussian.Norm.Basic.normSq_nonneg tail)
        (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (by decide))
    _ = 1 / 4 := by decide

/-- A positive-index logarithm Horner step preserves the sharper squared-norm bound nine fourths. -/
theorem step_bound_nine_four {w tail :
  Canonical} {index : Nat}
    (positive : 1 ≤ index) (wBound : Data.Gaussian.Norm.Basic.normSq w ≤ 1 / 9)
    (tailBound : Data.Gaussian.Norm.Basic.normSq tail ≤ 9 / 4) :
    Data.Gaussian.Norm.Basic.normSq (Horner.Basic.step w index tail) ≤ 9 / 4 := by
  rw [Horner.Basic.step_eq, Data.Gaussian.Basic.add_comm]
  calc
    Data.Gaussian.Norm.Basic.normSq (ComplexLog.scalar (ComplexLog.coefficient index) * w * tail + 1) ≤
        3 * Data.Gaussian.Norm.Basic.normSq (ComplexLog.scalar (ComplexLog.coefficient index) * w * tail) +
          (3 / 2) * Data.Gaussian.Norm.Basic.normSq 1 :=
      Data.Gaussian.Norm.Bounds.normSq_add_le_three_one_and_half _ _
    _ ≤ 3 * (1 / 4 : Fraction.Rational) + (3 / 2) * 1 :=
      add_le_add
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (scaled_term_bound_quarter positive wBound tailBound) (by
            decide))
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (by rw [Data.Gaussian.Norm.Basic.normSq_one]) (by decide))
    _ = 9 / 4 := by decide

/-- Every positive-index finite logarithm Horner value has squared norm at most nine fourths when the argument quadrance
is at most one ninth. -/
theorem horner_bound_nine_four {w :
  Canonical}
    (wBound : Data.Gaussian.Norm.Basic.normSq w ≤ 1 / 9) :
    ∀ (depth index : Nat), 1 ≤ index →
      Data.Gaussian.Norm.Basic.normSq (Horner.Basic.horner w index depth) ≤ 9 / 4
  | 0, _, _ => by rw [Horner.Basic.horner_zero, Data.Gaussian.Norm.Basic.normSq_one]; decide
  | depth + 1, index, positive => by
      rw [Horner.Basic.horner_succ]
      exact step_bound_nine_four positive wBound
        (horner_bound_nine_four wBound depth (index + 1)
          (by omega))

/-- Every positive-index finite logarithm Horner value has squared norm at most four on the displayed reduced disk. -/
theorem horner_bound {w :
  Canonical} (wBound : Data.Gaussian.Norm.Basic.normSq w ≤ 1 / 9) :
    ∀ (depth index : Nat), 1 ≤ index → Data.Gaussian.Norm.Basic.normSq (Horner.Basic.horner w index depth) ≤ 4
  | 0, _, _ => by rw [Horner.Basic.horner_zero, Data.Gaussian.Norm.Basic.normSq_one]; decide
  | depth + 1, index, positive => by
      rw [Horner.Basic.horner_succ]
      exact step_bound positive wBound
        (horner_bound wBound depth (index + 1) (by omega))

/-- The difference between logarithm Horner steps factors through their original tail difference. -/
theorem step_sub_step (w :
  Canonical) (index : Nat) (left right : Canonical) :
    Horner.Basic.step w index left - Horner.Basic.step w index right =
      ComplexLog.scalar (ComplexLog.coefficient index) * w * (left - right) := by
  rw [Horner.Basic.step_eq, Horner.Basic.step_eq]
  apply Data.Gaussian.Basic.ext <;>
    simp only [Basic.sub_re, Basic.sub_im, Basic.add_re, Basic.add_im, Basic.mul_re, Basic.mul_im,
      ComplexLog.scalar, Basic.one_re, Basic.one_im] <;> ring1

/-- A logarithm Horner step contracts squared tail differences by the factor one quarter on the reduced disk. -/
theorem step_difference_contract {w :
  Canonical} (wBound : Data.Gaussian.Norm.Basic.normSq w ≤ 1 / 9)
    {index : Nat} (positive : 1 ≤ index) (left right : Canonical) :
    Data.Gaussian.Norm.Basic.normSq (Horner.Basic.step w index left - Horner.Basic.step w index right) ≤
      (1 / 4 : Fraction.Rational) * Data.Gaussian.Norm.Basic.normSq (left - right) := by
  rw [step_sub_step, Data.Gaussian.Norm.Basic.normSq_mul,
    Data.Gaussian.Norm.Basic.normSq_mul, RationalEmbedding.normSq_scalar]
  have factorBound : ComplexLog.coefficient index ^ 2 * Data.Gaussian.Norm.Basic.normSq w ≤ 1 / 4 := by
    calc
      ComplexLog.coefficient index ^ 2 * Data.Gaussian.Norm.Basic.normSq w ≤ 1 * (1 / 9 : Fraction.Rational) :=
        Fraction.Order.Arithmetic.mul_le_mul_direct
          (Sensitivity.coefficient_sq_le_one positive) wBound
          (Data.Gaussian.Norm.Basic.normSq_nonneg w) (by decide)
      _ ≤ 1 / 4 := by decide
  exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    factorBound (Data.Gaussian.Norm.Basic.normSq_nonneg (left - right))

/-- The squared deviation of a finite positive-index logarithm Horner value from one is at most ten. -/
theorem horner_sub_one_bound {w :
  Canonical} (wBound : Data.Gaussian.Norm.Basic.normSq w ≤ 1 / 9)
    (depth index : Nat) (positive : 1 ≤ index) :
    Data.Gaussian.Norm.Basic.normSq (Horner.Basic.horner w index depth - 1) ≤ 10 := by
  exact (Data.Gaussian.Norm.Bounds.normSq_sub_le_two _ _).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (add_le_add (horner_bound wBound depth index positive)
        le_rfl)
      (by decide))

/-- Extending logarithm Horner depth changes its value by squared norm at most ten times the original-depth
quarter-power.

The reduced argument has quadrance at most one ninth and the starting coefficient index is positive. -/
theorem horner_add_depth_close {w :
  Canonical} (wBound : Data.Gaussian.Norm.Basic.normSq w ≤ 1 / 9) :
    ∀ (earlier extra index : Nat), 1 ≤ index →
      Data.Gaussian.Norm.Basic.normSq (Horner.Basic.horner w index (earlier + extra) - Horner.Basic.horner w
        index earlier) ≤
        10 * (1 / 4 : Fraction.Rational) ^ earlier
  | 0, extra, index, positive => by
      simp only [Nat.zero_add, Horner.Basic.horner_zero, pow_zero,
        Fraction.Field.mul_one_direct]
      exact horner_sub_one_bound wBound extra index positive
  | earlier + 1, extra, index, positive => by
      rw [show earlier + 1 + extra = (earlier + extra) + 1 by ring1,
        Horner.Basic.horner_succ, Horner.Basic.horner_succ]
      exact (step_difference_contract wBound positive _ _).trans
        (by
        have previous := horner_add_depth_close wBound
          earlier extra
          (index + 1) (positive.trans (Nat.le_add_right index 1))
        calc
          (1 / 4 : Fraction.Rational) *
              Data.Gaussian.Norm.Basic.normSq
                (Horner.Basic.horner w (index + 1) (earlier + extra) -
                  Horner.Basic.horner w (index + 1) earlier) ≤
              (1 / 4 : Fraction.Rational) *
                (10 * (1 / 4 : Fraction.Rational) ^ earlier) :=
            Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct previous
              (by decide)
          _ = 10 * (1 / 4 : Fraction.Rational) ^ (earlier + 1) := by
            rw [pow_succ]
            ring1)
end Purelib.Approximation.Gaussian.Logarithm.Local.Horner.Bounds

end
