module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

section
@[expose] public section

/-!
# Executable, limit-free differential laws for the logarithm

This module works with the finite local coordinate `log(1+u)`, on the
displayed rational disk `normSq u ≤ 1/4`.  Its relative forms and derivative
are finite alternating sums.  The reciprocal derivative law is expressed by
an exact finite geometric remainder and then by finite-request operational
equivalence.  No infinitesimal, limit, infinite series, or global logarithm
branch is introduced.
-/

namespace Purelib.Data.Gaussian.Norm.OneAdd

open Purelib.Data.Gaussian
open Purelib.Data.Rat
/-- A Gaussian squared norm at most one quarter gives squared norm at least one quarter after adding one. -/
theorem one_add_normSq_lower {u : Basic.Canonical} (disk :
  Data.Gaussian.Norm.Basic.normSq u ≤ 1 / 4) :
    (1 / 4 : Fraction.Rational) ≤ Data.Gaussian.Norm.Basic.normSq (1 + u) := by
  have realSquare : u.re ^ 2 ≤ (1 / 2 : Fraction.Rational) ^ 2 := by
    calc
      u.re ^ 2 ≤ u.re ^ 2 + u.im ^ 2 :=
        le_add_of_nonneg_right (Fraction.Order.Arithmetic.sq_nonneg_direct _)
      _ = Data.Gaussian.Norm.Basic.normSq u := rfl
      _ ≤ 1 / 4 := disk
      _ = (1 / 2 : Fraction.Rational) ^ 2 := by decide
  have realLower : -(1 / 2 : Fraction.Rational) ≤ u.re :=
    Fraction.Order.Arithmetic.neg_le_of_sq_le_sq_direct (by decide) realSquare
  have shifted : (1 / 2 : Fraction.Rational) ≤ 1 + u.re := by
    calc
      (1 / 2 : Fraction.Rational) = 1 + -(1 / 2) := by decide
      _ ≤ 1 + u.re := by
        simpa only [Fraction.Field.add_comm] using
          add_le_add_right realLower 1
  have squared := Fraction.Order.Arithmetic.pow_le_pow_direct
    (by decide : (0 : Fraction.Rational) ≤ 1 / 2) shifted 2
  calc
    (1 / 4 : Fraction.Rational) = (1 / 2 : Fraction.Rational) ^ 2 := by decide
    _ ≤ (1 + u.re) ^ 2 := squared
    _ ≤ (1 + u.re) ^ 2 + u.im ^ 2 :=
      le_add_of_nonneg_right (Fraction.Order.Arithmetic.sq_nonneg_direct _)
    _ = Data.Gaussian.Norm.Basic.normSq (1 + u) := by
      simp only [Data.Gaussian.Norm.Basic.normSq, Basic.add_re, Basic.add_im, Basic.one_re, Basic.one_im]
      ring1

/-- Adding one to a Gaussian whose squared norm is at most one quarter gives a nonzero Gaussian. -/
theorem one_add_ne_zero {u : Basic.Canonical} (disk :
  Data.Gaussian.Norm.Basic.normSq u ≤ 1 / 4) :
    1 + u ≠ 0 := by
  intro zero
  have lower := one_add_normSq_lower disk
  rw [zero, Norm.Basic.normSq_zero] at lower
  exact (by decide : ¬ ((1 / 4 : Fraction.Rational) ≤ 0)) lower

/-- The inverse of one plus a quarter-norm-bounded Gaussian has squared norm at most four. -/
theorem one_add_inverse_normSq_le_four {u : Basic.Canonical}
    (disk : Data.Gaussian.Norm.Basic.normSq u ≤ 1 / 4) : Data.Gaussian.Norm.Basic.normSq ((1 + u)⁻¹) ≤ 4 := by
  have nonzero := one_add_ne_zero disk
  rw [Field.inv_eq,
    Field.normSq_inv (1 + u) nonzero]
  have inverseOrder := Fraction.Order.Field.inv_le_inv_of_pos_direct
    (by decide : (0 : Fraction.Rational) < 1 / 4) (one_add_normSq_lower disk)
  simpa only [show (1 / 4 : Fraction.Rational)⁻¹ = 4 by decide] using inverseOrder
end Purelib.Data.Gaussian.Norm.OneAdd

end
