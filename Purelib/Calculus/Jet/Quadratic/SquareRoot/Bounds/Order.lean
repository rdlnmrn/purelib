module

public import Purelib.Calculus.Jet.Quadratic.SquareRoot.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

/-! # Order of the original inverse-root coefficient ceilings

Increasing the coefficient ceiling and decreasing positive root and signed-sum
floors increases the same original numerical ceiling. The actual square-root
certificate, readings, residual factors and composition remain unchanged.
-/

public section

namespace Purelib.Calculus.Jet.Quadratic.SquareRoot

open Purelib.Data.Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction

/-- The original movement ceiling is nonnegative for nonnegative factors and a positive signed-sum floor. -/
private theorem movementCeiling_nonnegative {coefficient sumFloor firstFactor lastFactor : Rational}
    (coefficientNonnegative : 0 ≤ coefficient) (sumPositive : 0 < sumFloor)
    (firstNonnegative : 0 ≤ firstFactor) (lastNonnegative : 0 ≤ lastFactor) :
    0 ≤ movementCeiling coefficient sumFloor firstFactor lastFactor :=
  Order.Arithmetic.mul_nonneg_direct
    (Order.Arithmetic.add_le_add_direct
      (Order.Arithmetic.mul_nonneg_direct (by decide +kernel : (0 : Rational) ≤ 4)
        (Order.Arithmetic.add_le_add_direct firstNonnegative lastNonnegative))
      (Order.Arithmetic.mul_nonneg_direct (by decide +kernel : (0 : Rational) ≤ 2) coefficientNonnegative))
    (Order.Field.inv_pos_direct sumPositive).le

/-- The original root remainder ceiling is nonnegative for its positive source floor and residual factors. -/
private theorem remainderCeiling_nonnegative {coefficient sourceFloor sumFloor firstFactor lastFactor : Rational}
    (sourcePositive : 0 < sourceFloor)
    (firstNonnegative : 0 ≤ firstFactor) (lastNonnegative : 0 ≤ lastFactor) :
    0 ≤ remainderCeiling coefficient sourceFloor sumFloor firstFactor lastFactor :=
  Order.Arithmetic.mul_nonneg_direct
    (Order.Arithmetic.mul_nonneg_direct (by decide +kernel : (0 : Rational) ≤ 2)
      (Order.Arithmetic.add_le_add_direct
        (Order.Arithmetic.mul_nonneg_direct (by decide +kernel : (0 : Rational) ≤ 2)
          (Order.Arithmetic.add_le_add_direct firstNonnegative lastNonnegative))
        (Order.Arithmetic.sq_nonneg_direct _)))
    (Order.Field.inv_pos_direct sourcePositive).le

/-- The original slope ceiling is nonnegative for a nonnegative coefficient and positive source floor. -/
private theorem rootSlopeCeiling_nonnegative {coefficient sourceFloor : Rational}
    (coefficientNonnegative : 0 ≤ coefficient) (sourcePositive : 0 < sourceFloor) :
    0 ≤ rootSlopeCeiling coefficient sourceFloor :=
  Order.Arithmetic.mul_nonneg_direct
    (Order.Arithmetic.mul_nonneg_direct (Norm.Basic.normSq_nonneg half) coefficientNonnegative)
    (Order.Field.inv_pos_direct sourcePositive).le

/-- A coefficient envelope and smaller positive root floors bound the same original inverse-root ceiling.

All residual factors remain identical. Reciprocal antitonicity pays the
source, target and signed-sum denominators, and nonnegative products and
squares preserve each original numerical expression.
-/
theorem inverseCeiling_mono
    {firstCoefficient lastCoefficient firstSource lastSource firstTarget lastTarget firstSum lastSum
      firstFactor lastFactor : Rational}
    (coefficientNonnegative : 0 ≤ firstCoefficient) (coefficientBound : firstCoefficient ≤ lastCoefficient)
    (sourcePositive : 0 < lastSource) (sourceBound : lastSource ≤ firstSource)
    (targetPositive : 0 < lastTarget) (targetBound : lastTarget ≤ firstTarget)
    (sumPositive : 0 < lastSum) (sumBound : lastSum ≤ firstSum)
    (firstNonnegative : 0 ≤ firstFactor) (lastNonnegative : 0 ≤ lastFactor) :
    inverseCeiling firstCoefficient firstSource firstTarget firstSum firstFactor lastFactor ≤
      inverseCeiling lastCoefficient lastSource lastTarget lastSum firstFactor lastFactor := by
  have firstSourcePositive := sourcePositive.trans_le sourceBound
  have firstTargetPositive := targetPositive.trans_le targetBound
  have firstSumPositive := sumPositive.trans_le sumBound
  have sourceInverse := Order.Field.inv_le_inv_of_pos_direct sourcePositive sourceBound
  have targetInverse := Order.Field.inv_le_inv_of_pos_direct targetPositive targetBound
  have sumInverse := Order.Field.inv_le_inv_of_pos_direct sumPositive sumBound
  have lastCoefficientNonnegative := coefficientNonnegative.trans coefficientBound
  have movementBound : movementCeiling firstCoefficient firstSum firstFactor lastFactor ≤
      movementCeiling lastCoefficient lastSum firstFactor lastFactor := by
    apply Order.Arithmetic.mul_le_mul_direct
    · exact Order.Arithmetic.add_le_add_direct (Order.Basic.le_refl _)
        (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct coefficientBound
          (by decide +kernel : (0 : Rational) ≤ 2))
    · exact sumInverse
    · exact (Order.Field.inv_pos_direct firstSumPositive).le
    · exact Order.Arithmetic.add_le_add_direct
        (Order.Arithmetic.mul_nonneg_direct (by decide +kernel : (0 : Rational) ≤ 4)
          (Order.Arithmetic.add_le_add_direct firstNonnegative lastNonnegative))
        (Order.Arithmetic.mul_nonneg_direct (by decide +kernel : (0 : Rational) ≤ 2)
          lastCoefficientNonnegative)
  have firstMovementNonnegative := movementCeiling_nonnegative coefficientNonnegative firstSumPositive
    firstNonnegative lastNonnegative
  have remainderBound : remainderCeiling firstCoefficient firstSource firstSum firstFactor lastFactor ≤
      remainderCeiling lastCoefficient lastSource lastSum firstFactor lastFactor := by
    apply Order.Arithmetic.mul_le_mul_direct
    · exact Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Order.Arithmetic.add_le_add_direct (Order.Basic.le_refl _)
          (Order.Arithmetic.pow_le_pow_direct firstMovementNonnegative movementBound 2))
        (by decide +kernel : (0 : Rational) ≤ 2)
    · exact sourceInverse
    · exact (Order.Field.inv_pos_direct firstSourcePositive).le
    · exact Order.Arithmetic.mul_nonneg_direct (by decide +kernel : (0 : Rational) ≤ 2)
        (Order.Arithmetic.add_le_add_direct
          (Order.Arithmetic.mul_nonneg_direct (by decide +kernel : (0 : Rational) ≤ 2)
            (Order.Arithmetic.add_le_add_direct firstNonnegative lastNonnegative))
          (Order.Arithmetic.sq_nonneg_direct _))
  have firstRemainderNonnegative :
      0 ≤ remainderCeiling firstCoefficient firstSource firstSum firstFactor lastFactor :=
    remainderCeiling_nonnegative firstSourcePositive firstNonnegative lastNonnegative
  have slopeBound : rootSlopeCeiling firstCoefficient firstSource ≤ rootSlopeCeiling lastCoefficient lastSource :=
    Order.Arithmetic.mul_le_mul_direct
      (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct coefficientBound (Norm.Basic.normSq_nonneg half))
      sourceInverse (Order.Field.inv_pos_direct firstSourcePositive).le
      (Order.Arithmetic.mul_nonneg_direct (Norm.Basic.normSq_nonneg half) lastCoefficientNonnegative)
  have firstSlopeNonnegative := rootSlopeCeiling_nonnegative coefficientNonnegative firstSourcePositive
  have sensitivityBound := Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Order.Arithmetic.add_le_add_direct slopeBound remainderBound)
    (by decide +kernel : (0 : Rational) ≤ 2)
  have firstSensitivityNonnegative := Order.Arithmetic.mul_nonneg_direct
    (by decide +kernel : (0 : Rational) ≤ 2)
    (Order.Arithmetic.add_le_add_direct firstSlopeNonnegative firstRemainderNonnegative)
  have sourceSquare := Order.Arithmetic.pow_le_pow_direct
    (Order.Field.inv_pos_direct firstSourcePositive).le sourceInverse 2
  have lastSourceSquareNonnegative := Order.Arithmetic.pow_nonneg_direct
    (Order.Field.inv_pos_direct sourcePositive).le 2
  unfold inverseCeiling
  exact Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Order.Arithmetic.add_le_add_direct
      (Order.Arithmetic.mul_le_mul_direct sourceSquare remainderBound firstRemainderNonnegative
        lastSourceSquareNonnegative)
      (Order.Arithmetic.mul_le_mul_direct
        (Order.Arithmetic.mul_le_mul_direct sourceSquare targetInverse
          (Order.Field.inv_pos_direct firstTargetPositive).le lastSourceSquareNonnegative)
        (Order.Arithmetic.pow_le_pow_direct firstSensitivityNonnegative sensitivityBound 2)
        (Order.Arithmetic.sq_nonneg_direct _)
        (Order.Arithmetic.mul_nonneg_direct lastSourceSquareNonnegative
          (Order.Field.inv_pos_direct targetPositive).le)))
    (by decide +kernel : (0 : Rational) ≤ 2)

end Purelib.Calculus.Jet.Quadratic.SquareRoot

end
