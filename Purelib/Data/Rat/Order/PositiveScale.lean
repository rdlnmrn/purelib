module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Data.Rat

section
public section

/-!
# Finite rational geometry of CCL comparisons

Every radial or coordinate comparison made after a finite decoder homography
pulls back to a four-coefficient Hermitian form

`a * (x² + y²) + b * x + c * y + d`.

The coefficients and the evaluated point are constructive rationals.  These
identities are the algebraic input for the finite x--y curve classifier used
by the persistent next-bit controller.
-/

namespace Purelib.Data.Rat.Order.PositiveScale

/-- A positive scaling of a rational difference is negative exactly when its first endpoint is below the threshold.

The retained identity expresses the cleared value as a positive multiple of the original difference. -/
theorem compare_lt_iff
    {value threshold cleared factor : Fraction.Rational}
    (factorPositive : 0 < factor)
    (identity : cleared = factor * (value - threshold)) :
    value < threshold ↔ cleared < 0 := by
  constructor
  · intro less
    rw [identity]
    exact Fraction.Order.Arithmetic.mul_neg_of_pos_of_neg_direct
      factorPositive (Fraction.Order.Arithmetic.sub_neg_direct less)
  · intro negative
    rw [identity] at negative
    have scaled :
        (value - threshold) * factor < (0 : Fraction.Rational) * factor := by
      simpa only [Fraction.Field.mul_comm,
        Fraction.Field.zero_mul_direct,
        Fraction.Field.mul_zero_direct] using negative
    exact Fraction.Order.Arithmetic.lt_of_sub_neg_direct
      (Fraction.Order.Arithmetic.lt_of_mul_lt_mul_right_direct
        scaled factorPositive)

/-- A positive scaling of a rational difference is nonpositive exactly when its first endpoint is at most the threshold.

A positive multiplier preserves and reflects the weak upper comparison of the original rational difference. -/
theorem compare_le_iff
    {value threshold cleared factor : Fraction.Rational}
    (factorPositive : 0 < factor)
    (identity : cleared = factor * (value - threshold)) :
    value ≤ threshold ↔ cleared ≤ 0 := by
  constructor
  · intro less
    rw [identity]
    have scaled :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Fraction.Order.Boundary.sub_nonpositive_iff.mpr less) factorPositive.le
    simpa only [Fraction.Field.mul_zero_direct] using scaled
  · intro nonpositive
    rw [identity] at nonpositive
    have scaled :
        (value - threshold) * factor ≤ (0 : Fraction.Rational) * factor := by
      simpa only [Fraction.Field.mul_comm,
        Fraction.Field.zero_mul_direct,
        Fraction.Field.mul_zero_direct] using nonpositive
    exact Fraction.Order.Boundary.sub_nonpositive_iff.mp
      (Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct
        scaled factorPositive)

/-- A positive scaling of a rational difference vanishes exactly when its two endpoints agree.

Cancellation of the positive multiplier identifies the two original rational endpoints. -/
theorem compare_eq_iff
    {value threshold cleared factor : Fraction.Rational}
    (factorPositive : 0 < factor)
    (identity : cleared = factor * (value - threshold)) :
    value = threshold ↔ cleared = 0 := by
  constructor
  · intro equal
    rw [identity, equal]
    ring1
  · intro zero
    have differenceZero : value - threshold = 0 := by
      apply Fraction.Field.mul_right_cancel_of_ne
        factorPositive.ne'
      calc
        (value - threshold) * factor =
            factor * (value - threshold) :=
          Fraction.Field.mul_comm _ _
        _ = cleared := identity.symm
        _ = 0 := zero
        _ = 0 * factor := by
          rw [Fraction.Field.zero_mul_direct]
    calc
      value = (value - threshold) + threshold := by ring1
      _ = threshold := by rw [differenceZero]; ring1

/-- A positive scaling of a rational difference is positive exactly when its first endpoint exceeds the threshold.

The retained identity expresses the cleared value as a positive multiple of the original difference. -/
theorem compare_gt_iff
    {value threshold cleared factor : Fraction.Rational}
    (factorPositive : 0 < factor)
    (identity : cleared = factor * (value - threshold)) :
    threshold < value ↔ 0 < cleared := by
  constructor
  · intro greater
    rw [identity]
    exact Fraction.Order.Arithmetic.mul_pos_direct factorPositive
      (Fraction.Order.Arithmetic.sub_pos_direct greater)
  · intro positive
    rw [identity] at positive
    have scaled :
        (0 : Fraction.Rational) * factor < (value - threshold) * factor := by
      simpa only [Fraction.Field.mul_comm,
        Fraction.Field.zero_mul_direct,
        Fraction.Field.mul_zero_direct] using positive
    exact Fraction.Order.Arithmetic.lt_of_sub_pos_direct
      (Fraction.Order.Arithmetic.lt_of_mul_lt_mul_right_direct
        scaled factorPositive)

/-- A positive scaling of a rational difference is nonnegative exactly when its first endpoint is at least the
threshold.

A positive multiplier preserves and reflects the weak lower comparison of the original rational difference. -/
theorem compare_ge_iff
    {value threshold cleared factor : Fraction.Rational}
    (factorPositive : 0 < factor)
    (identity : cleared = factor * (value - threshold)) :
    threshold ≤ value ↔ 0 ≤ cleared := by
  constructor
  · intro greater
    rw [identity]
    exact Fraction.Order.Arithmetic.mul_nonneg_direct factorPositive.le
      (Fraction.Order.Arithmetic.sub_nonneg_direct greater)
  · intro nonnegative
    rw [identity] at nonnegative
    have scaled :
        (0 : Fraction.Rational) * factor ≤ (value - threshold) * factor := by
      simpa only [Fraction.Field.mul_comm,
        Fraction.Field.zero_mul_direct,
        Fraction.Field.mul_zero_direct] using nonnegative
    exact Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
      (Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct
        scaled factorPositive)
end Purelib.Data.Rat.Order.PositiveScale

end
