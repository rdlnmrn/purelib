module

public import Purelib.Approximation.Rational.Budget.Aggregate
public import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Riemann.Readings.RectangularSharedClippedBoundary
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
public import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Data.Rat.Fraction
import Mathlib.Order.Basic
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

public section

/-! A cached finite allowance paying the full clipped-mesh ownership error.
The spatial triangle count is fixed before the model accuracy is selected. -/
namespace Purelib.Riemann.Periods

open Purelib.Data.Rat

open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)

open Purelib.Approximation.Rational in
set_option genInjectivity false in
/-- A positive reading budget paying the original clipped bilinear error weight.

The retained count and nonnegative magnitude determine the exact weight; a unit-capped weighted allowance supplies the
error and its one-sixteenth reading target. -/
structure ClippedBilinearBudget (count : Nat) (magnitude target : Coordinate) where
  /-- The original magnitude bound is nonnegative. -/ magnitude_nonnegative : 0 ≤ magnitude
  /-- The original requested target is strictly positive. -/ target_positive : 0 < target
  /-- The cached count-and-magnitude bilinear error weight. -/ weight : Coordinate
  /-- The weight is exactly count squared times 32 times magnitude plus one. -/ weight_eq : weight = (count :
    Coordinate) ^ 2 * (32 * (magnitude + 1))
  /-- The cached unit-capped positive error allowance. -/ error : Coordinate
  /-- The error is exactly the minimum of one and the weighted half-target allowance. -/ error_eq : error = min 1
    (Budget.Weighted.allowance (target / 2) weight)
  /-- The cached target for each original primitive reading. -/ readingTarget : Coordinate
  /-- The reading target is exactly one sixteenth of the retained error. -/ readingTarget_eq : readingTarget = error /
    16

constructive_injectivity ClippedBilinearBudget

namespace ClippedBilinearBudget

variable {count : Nat} {magnitude target : Coordinate}

open Purelib.Approximation.Rational in
/-- Compute the retained clipped bilinear budget from its original count, magnitude and positive target.

The exact count-coordinate weight, capped half-target allowance and reading target are cached with their defining
equalities. -/
@[expose] def build (count : Nat) (magnitude target : Coordinate)
    (nonnegative : 0 ≤ magnitude) (positive : 0 < target) : ClippedBilinearBudget count magnitude target :=
  let weight := Budget.Aggregate.countCoordinate count ^ 2 * (32 * (magnitude + 1))
  let error := min 1 (Budget.Weighted.allowance (target / 2) weight)
  ⟨nonnegative, positive, weight, by dsimp only [weight]; rw [Budget.Aggregate.countCoordinate_eq],
    error, rfl, error / 16, rfl⟩

/-- The original count-and-magnitude error weight is nonnegative.

The count square is nonnegative, and the retained magnitude makes its thirty-two-scaled successor nonnegative. Their
product is the exact cached weight. -/
theorem weight_nonnegative (budget : ClippedBilinearBudget count magnitude target) : 0 ≤ budget.weight := by
  rw [budget.weight_eq]
  exact Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.sq_nonneg_direct _)
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel) (add_nonneg budget.magnitude_nonnegative (by
      decide)))

open Purelib.Approximation.Rational in
/-- The retained clipped bilinear error allowance is strictly positive.

Both the unit cap and the weighted half-target allowance are strictly positive. Their minimum is the exact retained
error allowance. -/
theorem error_positive (budget : ClippedBilinearBudget count magnitude target) : 0 < budget.error := by
  rw [budget.error_eq]
  exact Fraction.Order.Basic.lt_min (by decide) (Budget.Weighted.allowance_positive
    (Fraction.Order.Field.div_pos_direct budget.target_positive (by decide)) budget.weight_nonnegative)

/-- The retained one-sixteenth reading target is strictly positive.

The retained error is strictly positive and the divisor sixteen is positive. Its exact quotient is the cached reading
target. -/
theorem readingTarget_positive (budget : ClippedBilinearBudget count magnitude target) : 0 < budget.readingTarget := by
  rw [budget.readingTarget_eq]
  exact Fraction.Order.Field.div_pos_direct budget.error_positive (by decide +kernel)

/-- The retained error allowance is at most one. -/
theorem error_le_one (budget : ClippedBilinearBudget count magnitude target) : budget.error ≤ 1 := by
  rw [budget.error_eq]
  exact Fraction.Order.Basic.min_le_left _ _

open Purelib.Approximation.Rational in
/-- The retained weight times error allowance is strictly below the original target.

The capped error is at most the weighted half-target allowance. Its weighted payment is at most half of the original
strictly positive target. -/
theorem error_paid (budget : ClippedBilinearBudget count magnitude target) : budget.weight * budget.error < target := by
  have allowanceBound : budget.error ≤ Budget.Weighted.allowance (target / 2) budget.weight := by
    rw [budget.error_eq]
    exact Fraction.Order.Basic.min_le_right _ _
  have halfPositive : 0 < target / 2 := Fraction.Order.Field.div_pos_direct budget.target_positive (by decide)
  have halfLess : target / 2 < target := by
    have doubled : target / 2 * 2 = target := Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)
    have strict := Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
      halfPositive (show (1 : Coordinate) < 2 by decide)
    simpa only [Fraction.Field.mul_one_direct, doubled] using strict
  exact ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct allowanceBound budget.weight_nonnegative).trans
    (Budget.Weighted.mul_allowance_le halfPositive.le budget.weight_nonnegative)).trans_lt halfLess

/-- Sixteen times either requested reading error is bounded by the retained error allowance.

Both actual reading errors lie below the same cached reading target. Multiplying their maximum by sixteen recovers the
retained error allowance. -/
theorem scaled_error_le (budget : ClippedBilinearBudget count magnitude target)
    {left right : Coordinate} (leftLe : left ≤ budget.readingTarget) (rightLe : right ≤ budget.readingTarget) :
    16 * max left right ≤ budget.error := by
  have bound := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Basic.max_le leftLe rightLe)
    (show (0 : Coordinate) ≤ 16 by decide +kernel)
  rw [budget.readingTarget_eq] at bound
  exact bound.trans_eq (by
    rw [Fraction.Field.mul_comm]
    exact Fraction.Field.div_mul_cancel_of_ne _ _ (by decide +kernel))

/-- Two readings within the retained target give a scaled maximum error at most one.

The scaled maximum is bounded by the retained error. The unit cap bounds that same error by one. -/
theorem small (budget : ClippedBilinearBudget count magnitude target)
    {left right : Coordinate} (leftLe : left ≤ budget.readingTarget) (rightLe : right ≤ budget.readingTarget) :
    16 * max left right ≤ 1 := (budget.scaled_error_le leftLe rightLe).trans budget.error_le_one

/-- The original count-weighted bilinear error is strictly paid by the retained target.

Both reading errors must lie below the cached reading target; the exact magnitude weight and factor 16 remain unchanged.
-/
theorem paid (budget : ClippedBilinearBudget count magnitude target)
    {left right : Coordinate} (leftLe : left ≤ budget.readingTarget) (rightLe : right ≤ budget.readingTarget) :
    (count : Coordinate) ^ 2 * (32 * (magnitude + 1) * (16 * max left right)) < target := by
  have bound := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (budget.scaled_error_le leftLe rightLe) budget.weight_nonnegative
  rw [budget.weight_eq] at bound
  exact (show (count : Coordinate) ^ 2 * (32 * (magnitude + 1) * (16 * max left right)) ≤
    budget.weight * budget.error by
      rw [budget.weight_eq]
      convert bound using 1; ring1).trans_lt budget.error_paid

end ClippedBilinearBudget
end Purelib.Riemann.Periods

end
