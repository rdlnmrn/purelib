module

public import Purelib.Data.Gaussian.Norm.Power
public import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Inverse.Subtraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Tactic.Ring

/-! # Quantitative Gaussian reciprocal and reciprocal-power bounds

A displayed positive quadrance floor controls each original reciprocal and
the displacement between two original reciprocals. Finite power sensitivity
then gives an explicit bound for their reciprocal-power displacement. Both
input readings and their common denominator payment remain unchanged.
-/

public section

namespace Purelib.Data.Gaussian.Norm.Reciprocal

open Purelib.Data
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction.Order

/-- A positive displayed quadrance floor excludes zero for its original reading. -/
private theorem nonzero_of_floor {source : Canonical} {floor : Fraction.Rational}
    (positive : 0 < floor) (lower : floor ≤ Norm.Basic.normSq source) : source ≠ 0 := by
  intro zero
  rewrite [zero, Norm.Basic.normSq_zero] at lower
  exact (not_le_of_gt positive) lower

/-- The original reciprocal quadrance is at most the inverse of its positive denominator floor. -/
theorem normSq_le {source : Canonical} {floor : Fraction.Rational}
    (positive : 0 < floor) (lower : floor ≤ Norm.Basic.normSq source) :
    Norm.Basic.normSq source⁻¹ ≤ floor⁻¹ := by
  rewrite [Gaussian.Field.inv_eq, Gaussian.Field.normSq_inv _ (nonzero_of_floor positive lower)]
  exact Fraction.Order.Field.inv_le_inv_of_pos_direct positive lower

/-- Original reciprocal displacement is bounded by the squared inverse floor times original input displacement. -/
theorem difference_normSq_le {first last : Canonical} {floor : Fraction.Rational}
    (positive : 0 < floor) (firstLower : floor ≤ Norm.Basic.normSq first)
    (lastLower : floor ≤ Norm.Basic.normSq last) :
    Norm.Basic.normSq (first⁻¹ - last⁻¹) ≤ (floor⁻¹ * floor⁻¹) * Norm.Basic.normSq (first - last) := by
  have firstBound := normSq_le positive firstLower
  have lastBound := normSq_le positive lastLower
  rewrite [Gaussian.Field.inv_eq] at firstBound lastBound
  have reverse : last - first = -(first - last) := by ring1
  rewrite [Gaussian.Field.inv_eq, Gaussian.Field.inv_eq,
    Gaussian.Field.inverse_sub_inverse_direct (nonzero_of_floor positive firstLower)
      (nonzero_of_floor positive lastLower),
    Norm.Basic.normSq_mul, Norm.Basic.normSq_mul, reverse, Norm.Basic.normSq_neg]
  calc
    _ ≤ (floor⁻¹ * Norm.Basic.normSq (first - last)) * floor⁻¹ :=
      Arithmetic.mul_le_mul_direct
        (Arithmetic.mul_le_mul_of_nonneg_right_direct firstBound (Norm.Basic.normSq_nonneg _))
        lastBound (Norm.Basic.normSq_nonneg _)
        (Arithmetic.mul_nonneg_direct (Fraction.Order.Field.inv_pos_direct positive).le
          (Norm.Basic.normSq_nonneg _))
    _ = _ := by ring1

/-- Every finite original reciprocal power obeys the corresponding inverse-floor power bound. -/
theorem power_normSq_le {source : Canonical} {floor : Fraction.Rational}
    (positive : 0 < floor) (lower : floor ≤ Norm.Basic.normSq source) (exponent : Nat) :
    Norm.Basic.normSq (source⁻¹ ^ exponent) ≤ floor⁻¹ ^ exponent := by
  rewrite [Norm.Power.normSq_pow]
  exact Arithmetic.pow_le_pow_direct (Norm.Basic.normSq_nonneg _) (normSq_le positive lower) exponent

/-- Original reciprocal-power displacement retains the finite sensitivity and both denominator floor payments. -/
theorem power_difference_normSq_le {first last : Canonical} {floor : Fraction.Rational}
    (positive : 0 < floor) (firstLower : floor ≤ Norm.Basic.normSq first)
    (lastLower : floor ≤ Norm.Basic.normSq last) (exponent : Nat) :
    Norm.Basic.normSq (first⁻¹ ^ exponent - last⁻¹ ^ exponent) ≤
      (Norm.Power.differenceFactor floor⁻¹ exponent * (floor⁻¹ * floor⁻¹)) * Norm.Basic.normSq (first - last) := by
  have powered := Norm.Power.difference_normSq_le
    (normSq_le positive firstLower) (normSq_le positive lastLower) exponent
  exact powered.trans
    ((Arithmetic.mul_le_mul_of_nonneg_left_direct
      (difference_normSq_le positive firstLower lastLower)
      (Norm.Power.differenceFactor_nonnegative (Fraction.Order.Field.inv_pos_direct positive).le exponent)).trans_eq
        (by ring1))

/-- A retained numerator and two original reciprocal powers obey their separately paid magnitude budgets. -/
theorem coefficient_two_powers_normSq_le {coefficient first last : Canonical}
    {budget firstFloor lastFloor : Fraction.Rational}
    (coefficientBound : Norm.Basic.normSq coefficient ≤ budget)
    (firstPositive : 0 < firstFloor) (lastPositive : 0 < lastFloor)
    (firstLower : firstFloor ≤ Norm.Basic.normSq first) (lastLower : lastFloor ≤ Norm.Basic.normSq last)
    (firstExponent lastExponent : Nat) :
    Norm.Basic.normSq (coefficient * first⁻¹ ^ firstExponent * last⁻¹ ^ lastExponent) ≤
      budget * firstFloor⁻¹ ^ firstExponent * lastFloor⁻¹ ^ lastExponent := by
  have firstBound := power_normSq_le (source := first) firstPositive firstLower firstExponent
  have lastBound := power_normSq_le (source := last) lastPositive lastLower lastExponent
  have firstNonnegative := Norm.Basic.normSq_nonneg (first⁻¹ ^ firstExponent)
  have productNonnegative := Arithmetic.mul_nonneg_direct
    (Norm.Basic.normSq_nonneg coefficient) firstNonnegative
  rewrite [Norm.Basic.normSq_mul, Norm.Basic.normSq_mul]
  have productBound := Arithmetic.mul_le_mul_direct coefficientBound firstBound
    firstNonnegative ((Norm.Basic.normSq_nonneg coefficient).trans coefficientBound)
  exact Arithmetic.mul_le_mul_direct productBound lastBound
    (Norm.Basic.normSq_nonneg (last⁻¹ ^ lastExponent)) (productNonnegative.trans productBound)

/-- The original inverse has a quadratic finite remainder paid by the common positive denominator floor.

Both reciprocal readings retain their original nonzero guards. Their exact
inverse-difference law factors the remainder into the squared displacement,
the squared first reciprocal and the last reciprocal.
-/
theorem quadratic_remainder_normSq_le {first last : Canonical} {floor : Fraction.Rational}
    (positive : 0 < floor) (firstLower : floor ≤ Norm.Basic.normSq first)
    (lastLower : floor ≤ Norm.Basic.normSq last) :
    Norm.Basic.normSq (last⁻¹ - first⁻¹ + (last - first) * first⁻¹ ^ 2) ≤
      floor⁻¹ ^ 3 * Norm.Basic.normSq (last - first) ^ 2 := by
  have firstNonzero := nonzero_of_floor positive firstLower
  have lastNonzero := nonzero_of_floor positive lastLower
  have forward := Inverse.Subtraction.inverse_sub_inverse lastNonzero firstNonzero
  have backward : first⁻¹ - last⁻¹ = (last - first) * (first⁻¹ * last⁻¹) := by
    rewrite [Inverse.Subtraction.inverse_sub_inverse firstNonzero lastNonzero]
    ring1
  have factored : last⁻¹ - first⁻¹ + (last - first) * first⁻¹ ^ 2 =
      (last - first) ^ 2 * first⁻¹ ^ 2 * last⁻¹ ^ 1 := by
    calc
      _ = (last - first) * first⁻¹ * (first⁻¹ - last⁻¹) := by rewrite [forward]; ring1
      _ = _ := by rewrite [backward]; ring1
  rewrite [factored]
  have bounded := coefficient_two_powers_normSq_le
    (coefficient := (last - first) ^ 2) (first := first) (last := last)
    (Fraction.Order.Basic.le_refl _) positive positive firstLower lastLower 2 1
  rewrite [Norm.Power.normSq_pow] at bounded
  exact bounded.trans_eq (by ring1)

end Purelib.Data.Gaussian.Norm.Reciprocal
