module

public import Purelib.Calculus.Jet.Quadratic.Product
import Purelib.Calculus.Jet.Quadratic.Composition.Bounds
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic

/-! # Fixed budgets for the original product certificate

Both original certificates retain their base values, slopes and remainder
factors. Their fixed scalar ceilings pay the actual product-rule slope and
original product remainder factor with the same retained movement budgets.
-/

public section

namespace Purelib.Calculus.Jet.Quadratic.Product

open Purelib.Calculus.Jet.Quadratic.Basic
open Purelib.Data
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction.Order

/-- Fixed slope and base quadrance budgets bound the retained product-rule slope. -/
theorem slope_le {increment : Canonical} (left right : Certificate increment) (unit : Norm.Basic.normSq increment ≤ 1)
    {leftValue rightValue leftSlope rightSlope : Fraction.Rational}
    (leftBase : Norm.Basic.normSq left.base ≤ leftValue) (rightBase : Norm.Basic.normSq right.base ≤ rightValue)
    (leftSlopeBound : Norm.Basic.normSq left.slope ≤ leftSlope)
    (rightSlopeBound : Norm.Basic.normSq right.slope ≤ rightSlope) :
    Norm.Basic.normSq (certificate left right unit).slope ≤ 2 * (leftSlope * rightValue + leftValue * rightSlope) := by
  change Norm.Basic.normSq (left.slope * right.base + left.base * right.slope) ≤ _
  have first : Norm.Basic.normSq (left.slope * right.base) ≤ leftSlope * rightValue := by
    rewrite [Norm.Basic.normSq_mul]
    exact Arithmetic.mul_le_mul_direct leftSlopeBound rightBase (Norm.Basic.normSq_nonneg _)
      ((Norm.Basic.normSq_nonneg left.slope).trans leftSlopeBound)
  have last : Norm.Basic.normSq (left.base * right.slope) ≤ leftValue * rightSlope := by
    rewrite [Norm.Basic.normSq_mul]
    exact Arithmetic.mul_le_mul_direct leftBase rightSlopeBound (Norm.Basic.normSq_nonneg _)
      ((Norm.Basic.normSq_nonneg left.base).trans leftBase)
  exact (Norm.Bounds.normSq_add_le_two _ _).trans
    (Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Arithmetic.add_le_add_direct first last) (by decide +kernel))

/-- Fixed base, slope and remainder budgets bound the original product certificate's actual finite factor.

Both original sensitivities derive from their same slope and remainder
budgets. The base-weighted remainder terms and displacement cross term use
these exact retained certificates, without recomputing a product expansion.
-/
theorem factor_le {increment : Canonical} (left right : Certificate increment) (unit : Norm.Basic.normSq increment ≤ 1)
    {leftValue rightValue leftSlope rightSlope leftFactor rightFactor : Fraction.Rational}
    (leftBase : Norm.Basic.normSq left.base ≤ leftValue) (rightBase : Norm.Basic.normSq right.base ≤ rightValue)
    (leftSlopeBound : Norm.Basic.normSq left.slope ≤ leftSlope)
    (rightSlopeBound : Norm.Basic.normSq right.slope ≤ rightSlope)
    (leftFactorBound : left.factor ≤ leftFactor) (rightFactorBound : right.factor ≤ rightFactor) :
    (certificate left right unit).factor ≤
      4 * (rightValue * leftFactor + leftValue * rightFactor +
        (2 * (leftSlope + leftFactor)) * (2 * (rightSlope + rightFactor))) := by
  have leftValueNonnegative := (Norm.Basic.normSq_nonneg left.base).trans leftBase
  have rightValueNonnegative := (Norm.Basic.normSq_nonneg right.base).trans rightBase
  have leftSensitivity := left.sensitivity_le leftSlopeBound leftFactorBound
  have rightSensitivity := right.sensitivity_le rightSlopeBound rightFactorBound
  have first := Arithmetic.mul_le_mul_direct rightBase leftFactorBound
    left.factor_nonneg rightValueNonnegative
  have last := Arithmetic.mul_le_mul_direct leftBase rightFactorBound
    right.factor_nonneg leftValueNonnegative
  have cross := Arithmetic.mul_le_mul_direct leftSensitivity rightSensitivity
    right.sensitivity_nonneg (left.sensitivity_nonneg.trans leftSensitivity)
  change factor left right ≤ _
  unfold factor
  simp only [← Norm.Basic.normSq_eq_canonical]
  exact Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Arithmetic.add_le_add_direct (Arithmetic.add_le_add_direct first last) cross)
    (by decide +kernel)

end Purelib.Calculus.Jet.Quadratic.Product

end
