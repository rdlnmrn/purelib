module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Vector.Basic

import Purelib.Data.Rat.Fraction.Compatibility
public import Purelib.Riemann.Periods.WeightedPeriods
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

public section

/-! One cached allowance pays both actual weighted rows, including the
component chart, integration, and common-stage movement factors. -/

namespace Purelib.Integration.Budget.WeightedPair

variable {count : Nat} {firstWeights lastWeights : Data.Vector Int count}

open Purelib.Riemann.Periods in
set_option genInjectivity false in
/-- Two retained coefficient-family targets and a shared positive component budget for an original positive target.

Each family keeps its own per-component quarter-target allocation. The shared component is one sixteenth of their
minimum and separately pays both family's component cost. -/
structure TwoPeriodBudget (first : WeightedPeriods.Coefficients firstWeights) (last : WeightedPeriods.Coefficients
  lastWeights) (target : WeightedPeriods.Coordinate) where
  /-- The original shared target is strictly positive. -/ positive : 0 < target
  /-- The cached first coefficient family's component target. -/ firstTarget : WeightedPeriods.Coordinate
  /-- The first target equals its family's per-component allocation at one quarter of the original target. -/
    firstTarget_eq : firstTarget = first.perComponent (target / 4)
  /-- The cached last coefficient family's component target. -/ lastTarget : WeightedPeriods.Coordinate
  /-- The last target equals its family's per-component allocation at one quarter of the original target. -/
    lastTarget_eq : lastTarget = last.perComponent (target / 4)
  /-- The retained common component allowance. -/ component : WeightedPeriods.Coordinate
  /-- The common component is one sixteenth of the minimum of the two retained targets. -/ component_eq : component =
    min firstTarget lastTarget / 16
  /-- The retained common component allowance is strictly positive. -/ component_positive : 0 < component
  /-- The common component cost is bounded by the first family's original component target. -/ first_bound : 2 * (4 *
    component + component) ≤ first.perComponent (target / 4)
  /-- The common component cost is bounded by the last family's original component target. -/ last_bound : 2 * (4 *
    component + component) ≤ last.perComponent (target / 4)

constructive_injectivity TwoPeriodBudget

namespace TwoPeriodBudget

variable {first : Purelib.Riemann.Periods.WeightedPeriods.Coefficients firstWeights} {last :
  Purelib.Riemann.Periods.WeightedPeriods.Coefficients lastWeights} {target :
  Purelib.Riemann.Periods.WeightedPeriods.Coordinate}

open Purelib.Data.Rat in
open Purelib.Riemann.Periods in
/-- One sixteenth of a positive minimum pays the twice-fivefold component cost below that minimum. -/
theorem paid_minimum {a b : WeightedPeriods.Coordinate} (positive : 0 < min a b) :
    2 * (4 * (min a b / 16) + min a b / 16) ≤ min a b := by
  have order := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (by
      decide : (10 : WeightedPeriods.Coordinate) ≤ 16)
    (Fraction.Order.Field.div_pos_direct positive (by decide : (0 : WeightedPeriods.Coordinate) < 16)).le
  exact (by ring1 : 2 * (4 * (min a b / 16) + min a b / 16) = (min a b / 16) * 10).trans_le
    (order.trans_eq (Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)))

open Purelib in
open Purelib.Data.Rat in
open Purelib.Riemann.Periods in
/-- Allocate a shared component budget from the two exact retained coefficient families and positive original target. -/
@[expose] def build (first : WeightedPeriods.Coefficients firstWeights) (last : WeightedPeriods.Coefficients
  lastWeights)
    (target : WeightedPeriods.Coordinate) (positive : 0 < target) : Integration.Budget.WeightedPair.TwoPeriodBudget
      first last target :=
  let firstTarget := first.perComponent (target / 4)
  let lastTarget := last.perComponent (target / 4)
  have quarterPositive := Fraction.Order.Field.div_pos_direct positive (by
      decide : (0 : WeightedPeriods.Coordinate) < 4)
  have minimumPositive : 0 < min firstTarget lastTarget :=
    Fraction.Order.Basic.lt_min (first.perComponent_positive quarterPositive) (last.perComponent_positive
      quarterPositive)
  ⟨positive, firstTarget, rfl, lastTarget, rfl, min firstTarget lastTarget / 16, rfl,
    Fraction.Order.Field.div_pos_direct minimumPositive (by decide),
    (Integration.Budget.WeightedPair.TwoPeriodBudget.paid_minimum minimumPositive).trans
      (Fraction.Order.Basic.min_le_left _ _), (Integration.Budget.WeightedPair.TwoPeriodBudget.paid_minimum
      minimumPositive).trans (Fraction.Order.Basic.min_le_right _ _)⟩

open Purelib
open Purelib.Data.Rat
/-- The first retained coefficient family's charge at the shared component cost is below one quarter of the original
target. -/
theorem first_paid (budget : Integration.Budget.WeightedPair.TwoPeriodBudget first last target) :
    first.charge (fun _ => 2 * (4 * budget.component + budget.component)) < target / 4 := by
  rw [first.charge_constant]
  exact (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct budget.first_bound first.mass_nonnegative).trans_lt
    (first.mass_mul_perComponent_lt (Fraction.Order.Field.div_pos_direct budget.positive (by decide)))

/-- The last retained coefficient family's charge at the shared component cost is below one quarter of the original
target. -/
theorem last_paid (budget : Integration.Budget.WeightedPair.TwoPeriodBudget first last target) :
    last.charge (fun _ => 2 * (4 * budget.component + budget.component)) < target / 4 := by
  rw [last.charge_constant]
  exact (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct budget.last_bound last.mass_nonnegative).trans_lt
    (last.mass_mul_perComponent_lt (Fraction.Order.Field.div_pos_direct budget.positive (by decide)))

end TwoPeriodBudget
end Purelib.Integration.Budget.WeightedPair
