module

public import Purelib.Data.Gaussian.Norm.Reciprocal
public import Purelib.Data.Gaussian.Norm.Product
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

/-! # Separately paid variation of two original reciprocal-power factors

Each original coefficient is a numerator times two reciprocal powers.
Positive floors concern the two distinct denominator families. The original
numerator, first denominator and second denominator movements contribute
separately through their actual finite sensitivity factors.
-/

public section

namespace Purelib.Data.Gaussian.Norm.Reciprocal

open Purelib.Data
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction.Order

/-- The finite reciprocal-power sensitivity retains its original positive quadrance floor and exponent. -/
@[expose] def powerSensitivity (floor : Fraction.Rational) (exponent : Nat) : Fraction.Rational :=
  Norm.Power.differenceFactor floor⁻¹ exponent * (floor⁻¹ * floor⁻¹)

/-- A positive original floor makes its finite reciprocal-power sensitivity nonnegative. -/
theorem powerSensitivity_nonnegative {floor : Fraction.Rational} (positive : 0 < floor) (exponent : Nat) :
    0 ≤ powerSensitivity floor exponent :=
  Arithmetic.mul_nonneg_direct
    (Norm.Power.differenceFactor_nonnegative (Fraction.Order.Field.inv_pos_direct positive).le exponent)
    (Arithmetic.mul_nonneg_direct (Fraction.Order.Field.inv_pos_direct positive).le
      (Fraction.Order.Field.inv_pos_direct positive).le)

/-- An original denominator movement budget pays its reciprocal-power movement with the same retained sensitivity. -/
theorem power_difference_le {first last : Canonical} {floor movement : Fraction.Rational}
    (positive : 0 < floor) (firstLower : floor ≤ Norm.Basic.normSq first)
    (lastLower : floor ≤ Norm.Basic.normSq last)
    (close : Norm.Basic.normSq (first - last) ≤ movement) (exponent : Nat) :
    Norm.Basic.normSq (first⁻¹ ^ exponent - last⁻¹ ^ exponent) ≤ powerSensitivity floor exponent * movement :=
  (power_difference_normSq_le positive firstLower lastLower exponent).trans
    (Arithmetic.mul_le_mul_of_nonneg_left_direct close (powerSensitivity_nonnegative positive exponent))

/-- The two original reciprocal-power coefficients have separate numerator and denominator movement payments.

The first denominator family and the second denominator family each retain
both original readings and their own common floor. The nested two-product
estimate preserves all three contributions and the actual finite exponents.
-/
theorem coefficient_two_powers_difference_le
    {firstCoefficient lastCoefficient firstSource lastSource firstRoot lastRoot : Canonical}
    {numeratorMovement numeratorBound firstMovement lastMovement firstFloor lastFloor : Fraction.Rational}
    (numeratorClose : Norm.Basic.normSq (firstCoefficient - lastCoefficient) ≤ numeratorMovement)
    (numeratorMagnitude : Norm.Basic.normSq lastCoefficient ≤ numeratorBound)
    (firstPositive : 0 < firstFloor) (lastPositive : 0 < lastFloor)
    (firstSourceLower : firstFloor ≤ Norm.Basic.normSq firstSource)
    (lastSourceLower : firstFloor ≤ Norm.Basic.normSq lastSource)
    (firstRootLower : lastFloor ≤ Norm.Basic.normSq firstRoot)
    (lastRootLower : lastFloor ≤ Norm.Basic.normSq lastRoot)
    (sourceClose : Norm.Basic.normSq (firstSource - lastSource) ≤ firstMovement)
    (rootClose : Norm.Basic.normSq (firstRoot - lastRoot) ≤ lastMovement)
    (firstExponent lastExponent : Nat) :
    Norm.Basic.normSq (firstCoefficient * firstSource⁻¹ ^ firstExponent * firstRoot⁻¹ ^ lastExponent -
      lastCoefficient * lastSource⁻¹ ^ firstExponent * lastRoot⁻¹ ^ lastExponent) ≤
      2 * (2 * (numeratorMovement * firstFloor⁻¹ ^ firstExponent +
        numeratorBound * (powerSensitivity firstFloor firstExponent * firstMovement)) * lastFloor⁻¹ ^ lastExponent +
          (numeratorBound * firstFloor⁻¹ ^ firstExponent) *
            (powerSensitivity lastFloor lastExponent * lastMovement)) := by
  have sourceMagnitude := power_normSq_le (source := firstSource) firstPositive firstSourceLower firstExponent
  have sourceMovement := power_difference_le (first := firstSource) (last := lastSource)
    firstPositive firstSourceLower lastSourceLower sourceClose firstExponent
  have firstProductMovement := Norm.Product.difference_le numeratorClose sourceMagnitude
    numeratorMagnitude sourceMovement
  have lastSourceMagnitude := power_normSq_le (source := lastSource) firstPositive lastSourceLower firstExponent
  have lastProductMagnitude : Norm.Basic.normSq (lastCoefficient * lastSource⁻¹ ^ firstExponent) ≤
      numeratorBound * firstFloor⁻¹ ^ firstExponent := by
    rewrite [Norm.Basic.normSq_mul]
    exact Arithmetic.mul_le_mul_direct numeratorMagnitude lastSourceMagnitude
      (Norm.Basic.normSq_nonneg (lastSource⁻¹ ^ firstExponent))
      ((Norm.Basic.normSq_nonneg lastCoefficient).trans numeratorMagnitude)
  have rootMagnitude := power_normSq_le (source := firstRoot) lastPositive firstRootLower lastExponent
  have rootMovement := power_difference_le (first := firstRoot) (last := lastRoot)
    lastPositive firstRootLower lastRootLower rootClose lastExponent
  exact Norm.Product.difference_le firstProductMovement rootMagnitude lastProductMagnitude rootMovement

end Purelib.Data.Gaussian.Norm.Reciprocal
