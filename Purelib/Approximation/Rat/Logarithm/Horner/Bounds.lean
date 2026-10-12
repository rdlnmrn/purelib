module
import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Rat.Logarithm.Horner.Basic
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

open Purelib

open Purelib.Approximation.Rat.Logarithm

open Purelib.Approximation.Rat.Logarithm.Horner.Basic

open Purelib.Data.Rat

section
public section

/-!
# Finite logarithm Horner approximation

For a displayed positive rational input in `[1/2,2]`, this module computes only
finite truncations of `2z(1 + z²/3 + z⁴/5 + ⋯)`, where
`z = (x - 1)/(x + 1)`.  The ellipsis is descriptive only: every definition
below is structural recursion with a natural depth, and every semantic
predicate has an explicit later finite index witness.  No completed logarithm,
infinite series, or limit is introduced.
-/

namespace Purelib.Approximation.Rat.Logarithm.Horner.Bounds

/-- A nonnegative argument at most one ninth times a Horner coefficient is at most one ninth. -/
theorem coefficient_mul_le_ninth {w : Fraction.Rational} (wNonnegative : 0 ≤ w)
    (wLe : w ≤ 1 / 9) (index : Nat) :
    Log.coefficient index * w ≤ 1 / 9 := by
  have multiplied := Fraction.Order.Arithmetic.mul_le_mul_direct
    (Log.coefficient_le_one index) wLe wNonnegative
    (by decide : (0 : Fraction.Rational) ≤ 1)
  simpa only [Fraction.Field.one_mul] using multiplied

/-- At a positive index, the coefficient times a nonnegative argument is nonnegative. -/
theorem coefficient_mul_nonneg {w : Fraction.Rational} (wNonnegative : 0 ≤ w)
    {index : Nat} (positive : 1 ≤ index) :
    0 ≤ Log.coefficient index * w :=
  Fraction.Order.Arithmetic.mul_nonneg_direct
    (Log.coefficient_nonneg positive) wNonnegative

/-- A logarithm Horner step preserves the interval from one to two for an argument between zero and one ninth. -/
theorem step_bounds {w : Fraction.Rational} (wNonnegative : 0 ≤ w)
    (wLe : w ≤ 1 / 9) {index : Nat} (positive : 1 ≤ index)
    {tail : Fraction.Rational} (tailLower : 1 ≤ tail) (tailUpper : tail ≤ 2) :
    1 ≤ Horner.Basic.step w index tail ∧ Horner.Basic.step w index tail ≤ 2 := by
  rw [Horner.Basic.step_eq]
  have coefficientWNonnegative := Approximation.Rat.Logarithm.Horner.Bounds.coefficient_mul_nonneg wNonnegative positive
  have termNonnegative : 0 ≤ Log.coefficient index * w * tail :=
    Fraction.Order.Arithmetic.mul_nonneg_direct coefficientWNonnegative
      ((by decide : (0 : Fraction.Rational) ≤ 1).trans tailLower)
  have termUpper : Log.coefficient index * w * tail ≤ (1 / 9 : Fraction.Rational) * 2 :=
    Fraction.Order.Arithmetic.mul_le_mul_direct
      (Approximation.Rat.Logarithm.Horner.Bounds.coefficient_mul_le_ninth wNonnegative wLe index) tailUpper
      ((by decide : (0 : Fraction.Rational) ≤ 1).trans tailLower)
      (by decide)
  constructor
  · calc
      1 = 0 + 1 := by ring1
      _ ≤ Log.coefficient index * w * tail + 1 :=
        add_le_add_left termNonnegative 1
      _ = 1 + Log.coefficient index * w * tail := by ring1
  · calc
      1 + Log.coefficient index * w * tail = Log.coefficient index * w * tail + 1 := by ring1
      _ ≤ (1 / 9 : Fraction.Rational) * 2 + 1 := add_le_add_left termUpper 1
      _ = 1 + (1 / 9 : Fraction.Rational) * 2 := by ring1
      _ ≤ 2 := by decide

/-- Every finite positive-index logarithm Horner value lies between one and two on the displayed argument interval. -/
theorem horner_bounds {w : Fraction.Rational} (wNonnegative : 0 ≤ w)
    (wLe : w ≤ 1 / 9) :
    ∀ (depth index : Nat), 1 ≤ index →
      1 ≤ Horner.Basic.horner w index depth ∧ Horner.Basic.horner w index depth ≤ 2
  | 0, _, _ => by
      rw [Horner.Basic.horner_zero]
      exact ⟨le_rfl, by decide⟩
  | depth + 1, index, positive => by
      rw [Horner.Basic.horner_succ]
      have tail := Purelib.Approximation.Rat.Logarithm.Horner.Bounds.horner_bounds wNonnegative wLe depth (index + 1)
        (by omega)
      exact Approximation.Rat.Logarithm.Horner.Bounds.step_bounds wNonnegative wLe positive tail.1 tail.2

/-- The difference between Horner steps factors through the difference of their retained tails. -/
theorem step_sub_step (w : Fraction.Rational) (index : Nat) (left right : Fraction.Rational) :
    Horner.Basic.step w index left - Horner.Basic.step w index right =
      (Log.coefficient index * w) * (left - right) := by
  rw [Horner.Basic.step_eq, Horner.Basic.step_eq]
  ring1

/-- For the displayed nonnegative reduced argument and positive index, the coefficient product squared is at most one
quarter. -/
theorem coefficient_mul_sq_le_quarter {w : Fraction.Rational}
    (wNonnegative : 0 ≤ w) (wLe : w ≤ 1 / 9)
    {index : Nat} (positive : 1 ≤ index) :
    (Log.coefficient index * w) ^ 2 ≤ 1 / 4 := by
  calc
    (Log.coefficient index * w) ^ 2 ≤ (1 / 9 : Fraction.Rational) ^ 2 :=
      Fraction.Order.Arithmetic.pow_le_pow_direct
        (Approximation.Rat.Logarithm.Horner.Bounds.coefficient_mul_nonneg wNonnegative positive)
        (Approximation.Rat.Logarithm.Horner.Bounds.coefficient_mul_le_ninth wNonnegative wLe index) 2
    _ ≤ 1 / 4 := by decide

/-- One logarithm Horner step contracts squared tail differences by at least the factor one quarter. -/
theorem step_difference_contract {w : Fraction.Rational} (wNonnegative : 0 ≤ w)
    (wLe : w ≤ 1 / 9) {index : Nat} (positive : 1 ≤ index)
    (left right : Fraction.Rational) :
    (Horner.Basic.step w index left - Horner.Basic.step w index right) ^ 2 ≤
      (1 / 4 : Fraction.Rational) * (left - right) ^ 2 := by
  rw [Approximation.Rat.Logarithm.Horner.Bounds.step_sub_step]
  rw [show ((Log.coefficient index * w) * (left - right)) ^ 2 =
    (Log.coefficient index * w) ^ 2 * (left - right) ^ 2 by ring1]
  exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (Approximation.Rat.Logarithm.Horner.Bounds.coefficient_mul_sq_le_quarter wNonnegative wLe positive)
    (Fraction.Order.Arithmetic.sq_nonneg_direct (left - right))

/-- The squared deviation of a finite logarithm Horner value from one is at most one. -/
theorem horner_sub_one_sq_le_one {w : Fraction.Rational} (wNonnegative : 0 ≤ w)
    (wLe : w ≤ 1 / 9) (depth index : Nat) (positive : 1 ≤ index) :
    (Horner.Basic.horner w index depth - 1) ^ 2 ≤ 1 := by
  have bounds := Approximation.Rat.Logarithm.Horner.Bounds.horner_bounds wNonnegative wLe depth index positive
  have differenceNonnegative : 0 ≤ Horner.Basic.horner w index depth - 1 :=
    Fraction.Order.Arithmetic.sub_nonneg_direct bounds.1
  have differenceLe : Horner.Basic.horner w index depth - 1 ≤ 1 := by
    have shifted := add_le_add_right bounds.2 (-1)
    calc
      Horner.Basic.horner w index depth - 1 = -1 + Horner.Basic.horner w index depth := by ring1
      _ ≤ -1 + 2 := shifted
      _ = 1 := by ring1
  have squared := Fraction.Order.Arithmetic.pow_le_pow_direct
    differenceNonnegative differenceLe 2
  simpa only [one_pow] using squared

/-- Extending a finite logarithm Horner depth changes its value by squared error at most the quarter-power of the
original depth.

The reduced argument lies between zero and one ninth and the starting coefficient index is positive. -/
theorem horner_add_depth_close {w : Fraction.Rational} (wNonnegative : 0 ≤ w)
    (wLe : w ≤ 1 / 9) :
    ∀ (earlier extra index : Nat), 1 ≤ index →
      (Horner.Basic.horner w index (earlier + extra) - Horner.Basic.horner w index earlier) ^ 2 ≤
        (1 / 4 : Fraction.Rational) ^ earlier
  | 0, extra, index, positive => by
      simp only [Nat.zero_add, Horner.Basic.horner_zero, pow_zero]
      exact Approximation.Rat.Logarithm.Horner.Bounds.horner_sub_one_sq_le_one wNonnegative wLe extra index positive
  | earlier + 1, extra, index, positive => by
      rw [show earlier + 1 + extra = (earlier + extra) + 1 by ring1,
        Horner.Basic.horner_succ, Horner.Basic.horner_succ]
      calc
        (Horner.Basic.step w index (Horner.Basic.horner w (index + 1) (earlier + extra)) -
            Horner.Basic.step w index (Horner.Basic.horner w (index + 1) earlier)) ^ 2 ≤
          (1 / 4 : Fraction.Rational) *
            (Horner.Basic.horner w (index + 1) (earlier + extra) -
              Horner.Basic.horner w (index + 1) earlier) ^ 2 :=
          Approximation.Rat.Logarithm.Horner.Bounds.step_difference_contract wNonnegative wLe positive _ _
        _ ≤ (1 / 4 : Fraction.Rational) * (1 / 4 : Fraction.Rational) ^ earlier :=
          Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
            (Purelib.Approximation.Rat.Logarithm.Horner.Bounds.horner_add_depth_close wNonnegative wLe earlier extra
              (index + 1) (Nat.succ_le_succ (Nat.zero_le index))) (by decide)
        _ = (1 / 4 : Fraction.Rational) ^ (earlier + 1) := by
          rw [pow_succ]
          ring1
end Purelib.Approximation.Rat.Logarithm.Horner.Bounds

end
