module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.GaussianInt.Basic
public import Purelib.Data.GaussianInt.Division.Nearest
import Purelib.Data.GaussianInt.Fraction.Basic
import Purelib.Data.Rat.Fraction.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.GaussianInt.Embedding
import Purelib.Data.GaussianInt.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Field
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

import Purelib.Algebra.NatCast
import Purelib.Data.Nat.Order
import Purelib.Data.Nat.BitWidth

/-!
# Hurwitz step norms and budgets

The nearest Gaussian-integer digit and retained remainder determine the next
fraction. Norm and binary-width certificates bound this original step.
-/

public section

namespace Purelib.Data.ComplexContinuedFraction.Hurwitz.Step

open Purelib.Data
open Purelib.Algebra

/-- Compute the larger of twice the sum of source numerator and denominator norms and four times denominator norm. -/
@[expose] def digitNormBudget (fraction : GaussianInt.Fraction) : Nat :=
  max
    (2 * (GaussianInt.normNat fraction.numerator + GaussianInt.normNat fraction.denominator))
    (4 * GaussianInt.normNat fraction.denominator)

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- The nearest integer digit norm is at most twice the sum of the retained numerator and denominator norms. -/
theorem digit_norm_le (fraction : GaussianInt.Fraction) :
    GaussianInt.normNat (GaussianInt.Division.Nearest.digit fraction) ≤
      2 * (GaussianInt.normNat fraction.numerator + GaussianInt.normNat fraction.denominator) := by
  have productBound :
      GaussianInt.normNat (GaussianInt.Division.Nearest.digit fraction) * GaussianInt.normNat fraction.denominator ≤
        2 * (GaussianInt.normNat fraction.numerator + GaussianInt.normNat (GaussianInt.Division.Nearest.remainder
          fraction)) := by
    apply (Fraction.Cast.Order.natCast_le_iff_direct).1
    calc
      ((GaussianInt.normNat (GaussianInt.Division.Nearest.digit fraction) * GaussianInt.normNat fraction.denominator :
        Nat) :
          Fraction.Basic.Rational) =
          Gaussian.Norm.Basic.normSq
            (GaussianInt.toGaussian (GaussianInt.Division.Nearest.digit fraction) *
              GaussianInt.toGaussian fraction.denominator) := by
        rw [NatCast.mul, ← GaussianInt.normSq_toGaussian, ← GaussianInt.normSq_toGaussian,
          Norm.Basic.normSq_mul]
      _ = Gaussian.Norm.Basic.normSq
          (GaussianInt.toGaussian fraction.numerator -
            GaussianInt.toGaussian (GaussianInt.Division.Nearest.remainder fraction)) := by
        have division := GaussianInt.Division.Nearest.digit_mul_denominator_add_remainder fraction
        have rearranged :
            GaussianInt.Division.Nearest.digit fraction * fraction.denominator =
              fraction.numerator - GaussianInt.Division.Nearest.remainder fraction := by
          calc
            GaussianInt.Division.Nearest.digit fraction * fraction.denominator =
                (GaussianInt.Division.Nearest.digit fraction * fraction.denominator +
                  GaussianInt.Division.Nearest.remainder fraction) -
                  GaussianInt.Division.Nearest.remainder fraction := by
              apply GaussianInt.ext <;>
                simp only [
                  GaussianInt.add_re,
                  GaussianInt.add_im,
                  GaussianInt.sub_re,
                  GaussianInt.sub_im] <;>
                ring1
            _ = fraction.numerator - GaussianInt.Division.Nearest.remainder fraction := by rw [division]
        rw [← GaussianInt.toGaussian_mul, rearranged, GaussianInt.toGaussian_sub]
      _ ≤ 2 *
          (Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian fraction.numerator) +
            Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian (GaussianInt.Division.Nearest.remainder fraction))) :=
        Norm.Bounds.normSq_sub_le_two _ _
      _ = ((2 *
          (GaussianInt.normNat fraction.numerator + GaussianInt.normNat (GaussianInt.Division.Nearest.remainder
            fraction)) : Nat) :
            Fraction.Basic.Rational) := by
        rw [GaussianInt.normSq_toGaussian, GaussianInt.normSq_toGaussian, NatCast.mul,
          NatCast.add, Nat.cast_ofNat]
  have remainderLe :
      GaussianInt.normNat (GaussianInt.Division.Nearest.remainder fraction) ≤ GaussianInt.normNat fraction.denominator
        :=
    (GaussianInt.Division.Nearest.remainder_norm_lt_denominator fraction).le
  have denominatorPositive := GaussianInt.normNat_pos fraction.denominatorNonzero
  calc
    GaussianInt.normNat (GaussianInt.Division.Nearest.digit fraction) ≤
        GaussianInt.normNat (GaussianInt.Division.Nearest.digit fraction) * GaussianInt.normNat fraction.denominator :=
          by
      exact Nat.le_mul_of_pos_right _ denominatorPositive
    _ ≤ 2 *
        (GaussianInt.normNat fraction.numerator + GaussianInt.normNat (GaussianInt.Division.Nearest.remainder fraction))
          :=
      productBound
    _ ≤ 2 *
        (GaussianInt.normNat fraction.numerator + GaussianInt.normNat fraction.denominator) := by
      exact Nat.mul_le_mul_left 2 (Nat.add_le_add_left remainderLe _)

/-- The selected nearest integer digit meets the retained source norm budget. -/
theorem digit_norm_le_budget (fraction : GaussianInt.Fraction) :
    GaussianInt.normNat (GaussianInt.Division.Nearest.digit fraction) ≤ digitNormBudget fraction := by
  change _ ≤ max _ _
  rewrite [Nat.Order.max_eq_natMax]
  exact Nat.le_trans (digit_norm_le fraction) (Nat.Order.le_max_left _ _)

/-- Construct the next Hurwitz fraction from the old denominator and exact nonzero nearest-integer remainder.

Keep the supplied witness for the new denominator and preserve the displayed fraction representation without an
additional normalization step. -/
@[expose] def next (fraction : GaussianInt.Fraction)
    (remainderNonzero : GaussianInt.Division.Nearest.remainder fraction ≠ 0) : GaussianInt.Fraction :=
  ⟨fraction.denominator, GaussianInt.Division.Nearest.remainder fraction, remainderNonzero⟩

/-- The next Hurwitz denominator is the retained nearest-integer remainder. -/
@[simp] theorem next_denominator (fraction : GaussianInt.Fraction)
    (remainderNonzero : GaussianInt.Division.Nearest.remainder fraction ≠ 0) :
    (next fraction remainderNonzero).denominator = GaussianInt.Division.Nearest.remainder fraction := rfl

/-- A nonterminal Hurwitz step does not increase the retained digit norm budget. -/
theorem next_digitNormBudget_le {fraction : GaussianInt.Fraction}
    (nonterminal : GaussianInt.Division.Nearest.remainder fraction ≠ 0) :
    digitNormBudget (next fraction nonterminal) ≤ digitNormBudget fraction := by
  have remainderLe :
      GaussianInt.normNat (GaussianInt.Division.Nearest.remainder fraction) ≤ GaussianInt.normNat fraction.denominator
        :=
    (GaussianInt.Division.Nearest.remainder_norm_lt_denominator fraction).le
  change max _ _ ≤ max _ _
  rewrite [Nat.Order.max_eq_natMax]
  apply Nat.Order.max_le
  · calc
      2 *
          (GaussianInt.normNat (next fraction nonterminal).numerator +
            GaussianInt.normNat (next fraction nonterminal).denominator) =
          2 *
            (GaussianInt.normNat fraction.denominator +
              GaussianInt.normNat (GaussianInt.Division.Nearest.remainder fraction)) := rfl
      _ ≤ 4 * GaussianInt.normNat fraction.denominator := by omega
      _ ≤ digitNormBudget fraction := by
        change _ ≤ max _ _
        rewrite [Nat.Order.max_eq_natMax]
        exact Nat.Order.le_max_right _ _
  · calc
      4 * GaussianInt.normNat (next fraction nonterminal).denominator =
          4 * GaussianInt.normNat (GaussianInt.Division.Nearest.remainder fraction) := rfl
      _ ≤ 4 * GaussianInt.normNat fraction.denominator :=
        Nat.mul_le_mul_left 4 remainderLe
      _ ≤ digitNormBudget fraction := by
        change _ ≤ max _ _
        rewrite [Nat.Order.max_eq_natMax]
        exact Nat.Order.le_max_right _ _

/-- The next Hurwitz numerator is the original retained denominator. -/
@[simp] theorem next_numerator (fraction : GaussianInt.Fraction)
    (remainderNonzero : GaussianInt.Division.Nearest.remainder fraction ≠ 0) :
    (next fraction remainderNonzero).numerator = fraction.denominator := rfl

open Purelib.Data.Gaussian in
/-- The next Hurwitz fraction value is the reciprocal of the original Gaussian residual. -/
theorem next_value (fraction : GaussianInt.Fraction)
    (remainderNonzero : GaussianInt.Division.Nearest.remainder fraction ≠ 0) :
    (next fraction remainderNonzero).value = (GaussianInt.Division.Nearest.residual fraction)⁻¹ := by
  have remainderGaussianNonzero : GaussianInt.toGaussian (GaussianInt.Division.Nearest.remainder fraction) ≠ 0 := by
    intro zero
    exact remainderNonzero (GaussianInt.toGaussian_eq_zero.mp zero)
  apply Field.mul_right_cancel_of_ne
    remainderGaussianNonzero
  calc
    (next fraction remainderNonzero).value * GaussianInt.toGaussian (GaussianInt.Division.Nearest.remainder fraction) =
        GaussianInt.toGaussian fraction.denominator :=
      (next fraction remainderNonzero).value_mul_denominator
    _ = (GaussianInt.Division.Nearest.residual fraction)⁻¹ * GaussianInt.toGaussian
      (GaussianInt.Division.Nearest.remainder fraction) := by
      rw [GaussianInt.Division.Nearest.remainder_toGaussian,
        ← Basic.mul_assoc,
        Field.inv_eq,
        Field.inv_mul _
          (GaussianInt.Division.Nearest.residual_ne_zero remainderNonzero),
        Basic.one_mul]

/-- A nonzero Hurwitz remainder reduces the denominator norm's binary logarithm by at least one. -/
theorem remainder_width_step {fraction : GaussianInt.Fraction}
    (nonterminal : GaussianInt.Division.Nearest.remainder fraction ≠ 0) :
    Nat.log2 (GaussianInt.normNat (GaussianInt.Division.Nearest.remainder fraction)) + 1 ≤
      Nat.log2 (GaussianInt.normNat fraction.denominator) := by
  have remainderPositive := GaussianInt.normNat_pos nonterminal
  have widthLess := Nat.BitWidth.natWidth_lt_of_two_mul_le remainderPositive
    (GaussianInt.Division.Nearest.twice_remainder_norm_le_denominator fraction)
  exact Nat.le_of_lt_succ widthLess

end Purelib.Data.ComplexContinuedFraction.Hurwitz.Step
