module
public import Purelib.Data.Nat.Order
public import Purelib.Algebra.Group.Negation
import Purelib.Algebra.Field.Ratio
import Purelib.Algebra.Field.Cancellation
import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.Field.Squares
import Purelib.Geometry.Trigonometry.Spread.Number.Basic
public import Purelib.Geometry.Trigonometry.Spread.Number.Parametrization
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Purelib.Tactic.Ring

section
open Purelib.Algebra
open Purelib.Data

-- These owned adapters retain the complete original operation dictionaries.
attribute [local instance 2000] Group.Negation.subNegZeroMonoid
  Nat.successorNeZero Nat.successorAtLeastTwo

open Purelib

open Purelib.Algebra.Field

open Purelib.Geometry.Trigonometry.Spread

open Purelib.Geometry.Trigonometry.Spread.Number

section
public section

/-!
# Divine Proportions, Exercises 2.1–2.2: spread-number parameters

The square root in the definition of a spread number is an explicit witness.
Consequently the converse parametrization computes its parameter directly;
it never selects a root or searches a field.
-/

namespace Purelib.Geometry.Trigonometry.Spread.Number.TwoParameter

variable {K : Type*} [ExplicitField K]

/-- The two-input number in Exercise 2.2. -/
@[expose] def twoPointSpreadNumber (x y : K) : K :=
  (x - y) ^ 2 / ((1 + x ^ 2) * (1 + y ^ 2))

/-- The parameter requested in the final clause of Exercise 2.2. -/
@[expose] def twoPointSpreadParameter (x y : K) : K :=
  (x - y) / (1 + x * y)

/-- First clause of Exercise 2.2, including the explicit square witness. -/
theorem twoPointSpreadNumber_isSpreadNumber
    (x y : K) (xSquareNotNegativeOne : x ^ 2 ≠ -1)
    (ySquareNotNegativeOne : y ^ 2 ≠ -1) :
    Number.Basic.IsSpreadNumber (twoPointSpreadNumber x y) := by
  let numerator := x - y
  let complementNumerator := 1 + x * y
  let denominator := (1 + x ^ 2) * (1 + y ^ 2)
  have denominatorNonzero : denominator ≠ 0 :=
    ExplicitField.mul_ne_zero
      (Squares.one_add_square_nonzero xSquareNotNegativeOne)
      (Squares.one_add_square_nonzero ySquareNotNegativeOne)
  have denominatorCancel : denominator * denominator⁻¹ = (1 : K) :=
    ExplicitField.mul_inv_cancel denominator denominatorNonzero
  have fibonacci :
      denominator = numerator ^ 2 + complementNumerator ^ 2 := by
    unfold denominator numerator complementNumerator
    ring1
  refine ⟨numerator * complementNumerator / denominator, ?_⟩
  unfold twoPointSpreadNumber
  simp only [ExplicitField.div_eq_mul_inv]
  change
    numerator ^ 2 * denominator⁻¹ *
        (1 - numerator ^ 2 * denominator⁻¹) =
      (numerator * complementNumerator * denominator⁻¹) ^ 2
  have complement :
      1 - numerator ^ 2 * denominator⁻¹ =
        complementNumerator ^ 2 * denominator⁻¹ := by
    calc
      1 - numerator ^ 2 * denominator⁻¹ =
          denominator * denominator⁻¹ -
            numerator ^ 2 * denominator⁻¹ := by rw [denominatorCancel]
      _ = complementNumerator ^ 2 * denominator⁻¹ := by
        rw [fibonacci]
        ring1
  rw [complement]
  ring1

/-- Final clause of Exercise 2.2: if `xy≠-1`, the requested parameter is exactly `(x-y)/(1+xy)`. -/
theorem twoPointSpreadNumber_eq_spreadParameter
    (x y : K) (xSquareNotNegativeOne : x ^ 2 ≠ -1)
    (ySquareNotNegativeOne : y ^ 2 ≠ -1)
    (productNotNegativeOne : x * y ≠ -1) :
    let parameter := twoPointSpreadParameter x y
    parameter ^ 2 ≠ -1 ∧
      twoPointSpreadNumber x y = Parametrization.spreadParameter parameter := by
  let numerator := x - y
  let productSum := 1 + x * y
  let denominator := (1 + x ^ 2) * (1 + y ^ 2)
  let parameter := twoPointSpreadParameter x y
  have productSumNonzero : productSum ≠ 0 := by
    intro productSumZero
    change 1 + x * y = 0 at productSumZero
    apply productNotNegativeOne
    calc
      x * y = (1 + x * y) - 1 := by ring1
      _ = -1 := by rw [productSumZero]; ring1
  have productSumCancel : productSum * productSum⁻¹ = (1 : K) :=
    ExplicitField.mul_inv_cancel productSum productSumNonzero
  have denominatorNonzero : denominator ≠ 0 :=
    ExplicitField.mul_ne_zero
      (Squares.one_add_square_nonzero xSquareNotNegativeOne)
      (Squares.one_add_square_nonzero ySquareNotNegativeOne)
  have fibonacci :
      denominator = numerator ^ 2 + productSum ^ 2 := by
    unfold denominator numerator productSum
    ring1
  have parameterFormula : parameter = numerator * productSum⁻¹ := by
    unfold parameter twoPointSpreadParameter numerator productSum
    rw [ExplicitField.div_eq_mul_inv]
  have parameterDenominatorTimesSquare :
      (1 + parameter ^ 2) * productSum ^ 2 = denominator := by
    rw [parameterFormula, fibonacci]
    calc
      (1 + (numerator * productSum⁻¹) ^ 2) * productSum ^ 2 =
          productSum ^ 2 +
            numerator ^ 2 * (productSum * productSum⁻¹) ^ 2 := by ring1
      _ = numerator ^ 2 + productSum ^ 2 := by
        rw [productSumCancel]
        ring1
  have parameterDenominatorNonzero : 1 + parameter ^ 2 ≠ 0 := by
    intro parameterDenominatorZero
    apply denominatorNonzero
    calc
      denominator = (1 + parameter ^ 2) * productSum ^ 2 :=
        parameterDenominatorTimesSquare.symm
      _ = 0 := by rw [parameterDenominatorZero]; ring1
  have parameterSquareNotNegativeOne : parameter ^ 2 ≠ -1 := by
    intro parameterSquareNegativeOne
    apply parameterDenominatorNonzero
    rw [parameterSquareNegativeOne]
    ring1
  refine ⟨parameterSquareNotNegativeOne, ?_⟩
  unfold twoPointSpreadNumber Parametrization.spreadParameter
  change numerator ^ 2 / denominator =
    parameter ^ 2 / (1 + parameter ^ 2)
  apply Ratio.ratio_eq_of_cross_product denominatorNonzero
    parameterDenominatorNonzero
  have crossDifference :
      numerator ^ 2 * (1 + parameter ^ 2) -
          parameter ^ 2 * denominator = 0 := by
    rw [parameterFormula, fibonacci]
    calc
      numerator ^ 2 * (1 + (numerator * productSum⁻¹) ^ 2) -
            (numerator * productSum⁻¹) ^ 2 *
              (numerator ^ 2 + productSum ^ 2) =
          numerator ^ 2 *
            (1 - (productSum * productSum⁻¹) ^ 2) := by ring1
      _ = 0 := by rw [productSumCancel]; ring1
  calc
    numerator ^ 2 * (1 + parameter ^ 2) =
        (numerator ^ 2 * (1 + parameter ^ 2) -
          parameter ^ 2 * denominator) + parameter ^ 2 * denominator := by
      ring1
    _ = parameter ^ 2 * denominator := by rw [crossDifference]; ring1

/-- Exercise 2.2 packaged with its universal spread witness and its requested extra parameter when `xy≠-1`. -/
theorem exercise_2_2
    (x y : K) (xSquareNotNegativeOne : x ^ 2 ≠ -1)
    (ySquareNotNegativeOne : y ^ 2 ≠ -1) :
    Number.Basic.IsSpreadNumber (twoPointSpreadNumber x y) ∧
      (x * y ≠ -1 →
        let parameter := twoPointSpreadParameter x y
        parameter ^ 2 ≠ -1 ∧
          twoPointSpreadNumber x y = Parametrization.spreadParameter
            parameter) := by
  exact ⟨twoPointSpreadNumber_isSpreadNumber x y
      xSquareNotNegativeOne ySquareNotNegativeOne,
    fun productNotNegativeOne =>
      twoPointSpreadNumber_eq_spreadParameter x y
        xSquareNotNegativeOne ySquareNotNegativeOne productNotNegativeOne⟩

end Purelib.Geometry.Trigonometry.Spread.Number.TwoParameter

end

end
