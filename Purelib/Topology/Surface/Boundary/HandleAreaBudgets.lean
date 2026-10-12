module

public import Purelib.Approximation.Rational.Budget.Aggregate
public import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Data.Rat.Fraction.Compatibility
public import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Topology.Surface.Boundary.HandleAreaBounds
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction
import Mathlib.Data.Int.Cast.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Data.Nat.Cast.Defs
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Approximation.Rational.Budget

open Purelib.Data

open Purelib.Data.Gaussian.Norm.Basic

open Purelib.Data.Rat

open Purelib.Riemann.Readings

public section

/-!
# Scalar selection for the actual period-area comparison

One positive request pays the full word-area error and the doubled handle
area error. The row tolerance is capped before sampling, including empty
handle lists and arbitrarily small or large endpoint magnitudes.
-/

namespace Purelib.Topology.Surface.Boundary.HandleAreaBudgets

open Purelib.Topology.Surface.Boundary.HandleAreaBounds
open Purelib.Riemann.Readings.PrimitiveAreaBounds (AreaCoordinate)

open Purelib.Data.Gaussian.Basic (Canonical)

open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)

set_option genInjectivity false in
/-- Cached scalar requests for boundary error and perturbed handle areas.

A positive total target and nonnegative magnitude determine separate boundary and handle targets, an area weight, and a
unit-capped row tolerance for the retained handle count. -/
structure HandleAreaBudget (magnitude : PrimitiveAreaBounds.AreaCoordinate) (handles : Nat) (target :
  PrimitiveAreaBounds.AreaCoordinate) where
  /-- Strict positivity of the original total error target. -/ positive : 0 < target
  /-- Nonnegativity of the fixed input primitive magnitude. -/ magnitude_nonnegative : 0 ≤ magnitude
  /-- Retained squared-norm target for the boundary comparison. -/ boundaryTarget : PrimitiveAreaBounds.AreaCoordinate
  /-- The boundary target is one quarter of the original target. -/ boundaryTarget_eq : boundaryTarget = target / 4
  /-- Retained squared-norm target for the complete handle-area perturbation. -/ handleTarget :
    PrimitiveAreaBounds.AreaCoordinate
  /-- The handle target is one sixteenth of the original target. -/ handleTarget_eq : handleTarget = target / 16
  /-- Cached scalar amplification of an individual handle perturbation. -/ weight : PrimitiveAreaBounds.AreaCoordinate
  /-- The retained area weight is 32 times one plus the fixed magnitude. -/ weight_eq : weight = 32 * (magnitude + 1)
  /-- Cached unit-capped component tolerance before sampling. -/ rowTarget : PrimitiveAreaBounds.AreaCoordinate
  /-- The row tolerance is the minimum of one and the paid per-handle weighted allowance. -/ rowTarget_eq : rowTarget =
    min 1 (Aggregate.perTerm
    (Weighted.allowance handleTarget weight) handles)

constructive_injectivity HandleAreaBudget

namespace HandleAreaBudget

variable {magnitude target : PrimitiveAreaBounds.AreaCoordinate} {handles : Nat}

open Purelib.Topology.Surface.Boundary
/-- Allocate and cache the boundary, handle, and row requests from the original target and magnitude. -/
@[expose] def build (magnitude : PrimitiveAreaBounds.AreaCoordinate) (nonnegative : 0 ≤ magnitude) (handles : Nat)
    (target : PrimitiveAreaBounds.AreaCoordinate) (positive : 0 < target) : HandleAreaBudget magnitude
      handles target :=
  let boundaryTarget := target / 4
  let handleTarget := target / 16
  let weight := 32 * (magnitude + 1)
  let rowTarget := min 1 (Aggregate.perTerm (Weighted.allowance handleTarget weight) handles)
  ⟨positive, nonnegative, boundaryTarget, rfl, handleTarget, rfl, weight, rfl, rowTarget, rfl⟩

/-- The allocated boundary-error target is strictly positive. -/
theorem boundary_positive (budget : HandleAreaBudget magnitude handles target) : 0 <
  budget.boundaryTarget := by
  rw [budget.boundaryTarget_eq]
  exact Fraction.Order.Field.div_pos_direct budget.positive (by decide)

/-- The allocated handle-area target is strictly positive. -/
theorem handle_positive (budget : HandleAreaBudget magnitude handles target) : 0 < budget.handleTarget
  := by
  rw [budget.handleTarget_eq]
  exact Fraction.Order.Field.div_pos_direct budget.positive (by decide +kernel)

/-- The retained handle-area perturbation weight is nonnegative. -/
theorem weight_nonnegative (budget : HandleAreaBudget magnitude handles target) : 0 ≤ budget.weight :=
  by
  rw [budget.weight_eq]
  exact Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel) (add_nonneg budget.magnitude_nonnegative (by
    decide))

/-- The unit-capped per-row request is strictly positive, including for an empty handle list. -/
theorem row_positive (budget : HandleAreaBudget magnitude handles target) : 0 < budget.rowTarget := by
  rw [budget.rowTarget_eq]
  exact Fraction.Order.Basic.lt_min (by decide) (Aggregate.perTerm_positive
    (Weighted.allowance_positive budget.handle_positive budget.weight_nonnegative) handles)

/-- The per-row perturbation request is capped by one. -/
theorem row_le_one (budget : HandleAreaBudget magnitude handles target) : budget.rowTarget ≤ 1 := by
  rw [budget.rowTarget_eq]
  exact Fraction.Order.Basic.min_le_left _ _

/-- The cached row request is paid by the weighted aggregate handle budget. -/
theorem row_paid (budget : HandleAreaBudget magnitude handles target) :
    budget.rowTarget ≤ Aggregate.perTerm
      (Weighted.allowance budget.handleTarget (32 * (magnitude + 1))) handles := by
  rw [budget.rowTarget_eq, budget.weight_eq]
  exact Fraction.Order.Basic.min_le_right _ _

/-- The boundary and doubled-handle allocations combine to the original target exactly. -/
theorem total_eq (budget : HandleAreaBudget magnitude handles target) :
    2 * (budget.boundaryTarget + 4 * budget.handleTarget) = target := by
  rw [budget.boundaryTarget_eq, budget.handleTarget_eq]
  have four : (target / 4) * 4 = target := Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)
  have sixteen : (target / 16) * 16 = target := Fraction.Field.div_mul_cancel_of_ne _ _ (by decide +kernel)
  apply Fraction.Field.mul_right_cancel_of_ne (by decide : (2 : PrimitiveAreaBounds.AreaCoordinate) ≠ 0)
  calc
    _ = (target / 4) * 4 + (target / 16) * 16 := by ring1
    _ = target + target := by rw [four, sixteen]
    _ = target * 2 := by ring1

/-- Compose the actual boundary error with the doubled handle-area error; the entire physical remainder is kept on both
sides of the comparison. -/
theorem combine (budget : HandleAreaBudget magnitude handles target) (surface original changed
  remainder : Gaussian.Basic.Canonical)
    (boundary : Data.Gaussian.Norm.Basic.normSq (surface - (2 * original + remainder)) < budget.boundaryTarget)
    (handle : Data.Gaussian.Norm.Basic.normSq (changed - original) < budget.handleTarget) :
    Data.Gaussian.Norm.Basic.normSq (surface - (2 * changed + remainder)) < target := by
  have expanded : surface - (2 * changed + remainder) =
      (surface - (2 * original + remainder)) - 2 * (changed - original) := by ring1
  rw [expanded]
  have estimate := Gaussian.Norm.Bounds.normSq_sub_le_two
    (surface - (2 * original + remainder)) (2 * (changed - original))
  rw [Gaussian.Norm.Basic.normSq_mul] at estimate
  have two : Data.Gaussian.Norm.Basic.normSq (2 : Gaussian.Basic.Canonical) = 4 := by decide
  rw [two] at estimate
  have scaled := Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by
      decide : (0 : PrimitiveAreaBounds.AreaCoordinate) < 4) handle
  have shifted := Fraction.Order.Arithmetic.add_lt_add_right_direct scaled budget.boundaryTarget
  have summed := (add_le_add boundary.le (le_refl (4 * Data.Gaussian.Norm.Basic.normSq (changed - original)))).trans_lt
    (by simpa only [add_comm] using shifted)
  exact (estimate.trans_lt (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide) summed)).trans_eq
    budget.total_eq

end HandleAreaBudget
end Purelib.Topology.Surface.Boundary.HandleAreaBudgets
