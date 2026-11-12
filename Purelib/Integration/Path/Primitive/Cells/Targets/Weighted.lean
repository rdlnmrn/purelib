module

public import Purelib.Integration.Path.Primitive.Cells.Targets
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-! # Count-weighted payments from the original finite path allocations

The retained count-square denominator pays the linear count factor using
its same positive cost. These bounds consume the original Targets cache;
no count, request, budget or path preparation is reconstructed.
-/

public section

namespace Purelib.Integration.Path.Primitive.PrimitiveEdge.CellEndpoints.Targets

open Purelib
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Approximation.Rational.Geometric

variable {sheets : Nat} {start finish : LiftedPoint sheets}
  {original : LiftedPath sheets start finish} {stage : Nat}

/-- The original count is bounded by its same retained positive count-square cost. -/
private theorem count_le_cost (targets : Targets original stage) :
    (targets.count : Rational) ≤ targets.cost := by
  have countNonnegative : (0 : Rational) ≤ (targets.count : Rational) :=
    Cast.Order.natCast_le_direct (m := 0) (n := targets.count) (Nat.zero_le targets.count)
  have difference := Order.Arithmetic.add_le_add_direct
    (Order.Arithmetic.sq_nonneg_direct ((targets.count : Rational) - 1)) countNonnegative
  rewrite [Field.zero_add] at difference
  have exactDifference : ((targets.count : Rational) - 1) ^ 2 + (targets.count : Rational) =
      targets.cost - (targets.count : Rational) := by
    rewrite [targets.cost_eq, targets.countSquare_eq]
    ring1
  exact Order.Arithmetic.le_of_sub_nonneg_direct (difference.trans_eq exactDifference)

/-- The actual count times its retained local allocation is paid by the original geometric budget.

The same cached count-square denominator absorbs this linear count. No
new allocation, count estimate or source request is introduced.
-/
theorem count_mul_localBound_le_budget (targets : Targets original stage) :
    (targets.count : Rational) * targets.localBound ≤ targets.budget := by
  have costBound : targets.cost ≤ targets.denominator := by
    have scaled := Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      (by decide +kernel : (1 : Rational) ≤ 16) targets.cost_positive.le
    exact (by ring1 : targets.cost = 1 * targets.cost).trans_le
      (scaled.trans_eq targets.denominator_eq.symm)
  have bound := Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (targets.count_le_cost.trans costBound) targets.localBound_positive.le
  have cancellation : targets.denominator * targets.localBound = targets.budget := by
    calc
      _ = targets.localBound * targets.denominator := Field.mul_comm _ _
      _ = targets.budget := by
        rewrite [targets.localBound_eq]
        exact Field.div_mul_cancel_of_ne _ _ targets.denominator_positive.ne'
  exact bound.trans_eq cancellation

/-- The count-weighted allocation obeys the original unit-scale quarter-radius schedule. -/
theorem count_mul_localBound_le_quarterRadius (targets : Targets original stage) :
    (targets.count : Rational) * targets.localBound ≤ Basic.quarterRadius 1 stage :=
  targets.count_mul_localBound_le_budget.trans_eq targets.budget_eq

end Purelib.Integration.Path.Primitive.PrimitiveEdge.CellEndpoints.Targets

end
