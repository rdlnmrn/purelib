module
public import Purelib.Data.Nat.Order
public import Purelib.Algebra.Group.Negation
import Purelib.Algebra.Field.Cancellation
import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.Field.Squares
public import Purelib.Geometry.Trigonometry.Spread.Number.Basic
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

section
public section

/-!
# Divine Proportions, Exercises 2.1–2.2: spread-number parameters

The square root in the definition of a spread number is an explicit witness.
Consequently the converse parametrization computes its parameter directly;
it never selects a root or searches a field.
-/

namespace Purelib.Geometry.Trigonometry.Spread.Number.Parametrization

variable {K : Type*} [ExplicitField K]

/-- The rational parametrization `u²/(1+u²)` from Exercise 2.1. -/
@[expose] def spreadParameter (parameter : K) : K :=
  parameter ^ 2 / (1 + parameter ^ 2)

/-- First half of Exercise 2.1: every valid rational parameter produces a spread number, with the square witness
displayed. -/
theorem spreadParameter_isSpreadNumber
    (parameter : K) (squareNotNegativeOne : parameter ^ 2 ≠ -1) :
    Number.Basic.IsSpreadNumber (spreadParameter parameter) := by
  let denominator := 1 + parameter ^ 2
  have denominatorNonzero : denominator ≠ 0 :=
    Squares.one_add_square_nonzero squareNotNegativeOne
  have denominatorCancel : denominator * denominator⁻¹ = (1 : K) :=
    ExplicitField.mul_inv_cancel denominator denominatorNonzero
  refine ⟨parameter / denominator, ?_⟩
  unfold spreadParameter
  simp only [ExplicitField.div_eq_mul_inv]
  have complement :
      1 - parameter ^ 2 * denominator⁻¹ = denominator⁻¹ := by
    calc
      1 - parameter ^ 2 * denominator⁻¹ =
          denominator * denominator⁻¹ -
            parameter ^ 2 * denominator⁻¹ := by rw [denominatorCancel]
      _ = denominator⁻¹ := by unfold denominator; ring1
  rw [complement]
  ring1

/-- Converse half of Exercise 2.1: the stored square witness gives the explicit parameter `root/(1-s)`. -/
theorem spreadNumber_has_parameter
    (value : K) (spreadNumber : Number.Basic.IsSpreadNumber value)
    (notOne : value ≠ 1) :
    ∃ parameter : K,
      parameter ^ 2 ≠ -1 ∧ value = spreadParameter parameter := by
  rcases spreadNumber with ⟨root, squareWitness⟩
  let denominator := 1 - value
  let parameter := root / denominator
  have denominatorNonzero : denominator ≠ 0 := (fun {K : Type _} [ExplicitField K] {value : K}
    (notOne : value ≠ 1) => (ExplicitField.one_sub_ne_zero_of_ne_one (K := K) (value := value)
    notOne : 1 - value ≠ 0)) notOne
  have denominatorCancel : denominator * denominator⁻¹ = (1 : K) :=
    ExplicitField.mul_inv_cancel denominator denominatorNonzero
  have parameterSquare :
      parameter ^ 2 = value * denominator⁻¹ := by
    unfold parameter
    simp only [ExplicitField.div_eq_mul_inv]
    calc
      (root * denominator⁻¹) ^ 2 =
          root ^ 2 * denominator⁻¹ ^ 2 := by ring1
      _ = value * denominator * denominator⁻¹ ^ 2 := by
        rw [← squareWitness]
      _ = value * denominator⁻¹ *
          (denominator * denominator⁻¹) := by ring1
      _ = value * denominator⁻¹ := by rw [denominatorCancel]; ring1
  have parameterDenominator :
      1 + parameter ^ 2 = denominator⁻¹ := by
    rw [parameterSquare]
    calc
      1 + value * denominator⁻¹ =
          denominator * denominator⁻¹ + value * denominator⁻¹ := by
        rw [denominatorCancel]
      _ = denominator⁻¹ := by unfold denominator; ring1
  have parameterDenominatorNonzero : 1 + parameter ^ 2 ≠ 0 := by
    rw [parameterDenominator]
    exact ExplicitField.inv_ne_zero denominatorNonzero
  have parameterSquareNotNegativeOne : parameter ^ 2 ≠ -1 := by
    intro squareNegativeOne
    apply parameterDenominatorNonzero
    rw [squareNegativeOne]
    ring1
  refine ⟨parameter, parameterSquareNotNegativeOne, ?_⟩
  unfold spreadParameter
  apply (fun {K : Type _} [ExplicitField K] {factor left right : K} (factorNonzero : factor ≠ 0)
    (productsEqual : left * factor = right * factor) => (ExplicitField.eq_of_mul_eq_mul_right (K
    := K) (left := left) (right := right) (factor := factor) factorNonzero productsEqual : left = right))
    parameterDenominatorNonzero
  calc
    value * (1 + parameter ^ 2) = value * denominator⁻¹ := by
      rw [parameterDenominator]
    _ = parameter ^ 2 := parameterSquare.symm
    _ = (parameter ^ 2 / (1 + parameter ^ 2)) *
        (1 + parameter ^ 2) :=
      (ExplicitField.div_mul_cancel _
        parameterDenominatorNonzero).symm

/-- Parametrize spread numbers other than one, retaining all denominator conditions.

Every parameter whose square is not minus one gives a spread number; conversely, each spread number unequal to one has
an admissible parameter (Exercise 2.1). -/
theorem exercise_2_1
    (parameter : K) (squareNotNegativeOne : parameter ^ 2 ≠ -1) :
    Number.Basic.IsSpreadNumber (spreadParameter parameter) ∧
      ∀ value : K, Number.Basic.IsSpreadNumber value → value ≠ 1 →
        ∃ recovered : K,
          recovered ^ 2 ≠ -1 ∧ value = spreadParameter recovered :=
            by
  exact ⟨spreadParameter_isSpreadNumber parameter
    squareNotNegativeOne,
    spreadNumber_has_parameter⟩
end Purelib.Geometry.Trigonometry.Spread.Number.Parametrization

end

end
