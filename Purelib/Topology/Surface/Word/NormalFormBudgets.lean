module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Vector.Basic

import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Periods.WeightedPeriods
public import Purelib.Approximation.Budget.WeightedRowBudgets
import Purelib.Data.Vector.Dependent
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib

open Purelib.Approximation.Budget

open Purelib.Approximation.Rational.Budget

open Purelib.Data.Rat

open Purelib.Riemann.Periods

public section

/-!
# Joint row and boundary-area scalar allocation

The component allowance pays chord error, cut-path comparison and movement
to a common stage. The area cap enforces that same component allowance in
the full word-area request without multiplying two independent count costs.
-/

namespace Purelib.Topology.Surface.Word.NormalFormBudgets

open Purelib.Approximation.Budget.WeightedRowBudgets (CoefficientRows)
open Purelib.Riemann.Periods.WeightedPeriods (Coordinate)

variable {count rows : Nat} {weights : Data.Vector (Data.Vector Int count) rows}

set_option genInjectivity false in
/-- Coupled component and area tolerances for retained weighted normal-form rows.

A positive row target reserves a factor of 32, and the area cap respects both its independent target and the weighted
component allowance. -/
structure RowAllocation (profile : WeightedRowBudgets.CoefficientRows weights) (weight rowTarget areaTarget :
  WeightedPeriods.Coordinate) where
  /-- The original weighted-row target is strictly positive. -/ row_positive : 0 < rowTarget
  /-- The independent boundary-area target is strictly positive. -/ area_positive : 0 < areaTarget
  /-- The retained word-area weight is nonnegative. -/ weight_nonnegative : 0 ≤ weight
  /-- Cached common component tolerance for the weighted rows. -/ component : WeightedPeriods.Coordinate
  /-- The component tolerance is computed from one thirty-second of the row target. -/ component_eq : component =
    profile.perComponent (rowTarget / 32)
  /-- Cached area target compatible with the same component allowance. -/ area : WeightedPeriods.Coordinate
  /-- The area cap is the minimum of the independent target and shifted-weight component budget. -/ area_eq : area = min
    areaTarget ((weight + 1) * component)

constructive_injectivity RowAllocation

namespace RowAllocation

variable {profile : WeightedRowBudgets.CoefficientRows weights} {weight rowTarget areaTarget :
  WeightedPeriods.Coordinate}

/-- Cache the component allowance and compatible minimum area cap for positive targets. -/
@[expose] def build (profile : WeightedRowBudgets.CoefficientRows weights) (weight : WeightedPeriods.Coordinate)
  (nonnegative : 0 ≤ weight)
    (rowTarget : WeightedPeriods.Coordinate) (rowPositive : 0 < rowTarget) (areaTarget : WeightedPeriods.Coordinate)
      (areaPositive : 0 < areaTarget) :
    NormalFormBudgets.RowAllocation profile weight rowTarget areaTarget :=
  let component := profile.perComponent (rowTarget / 32)
  ⟨rowPositive, areaPositive, nonnegative, component, rfl, min areaTarget ((weight + 1) * component), rfl⟩

/-- The retained weighted-row component allowance is strictly positive. -/
theorem component_positive (allocation : NormalFormBudgets.RowAllocation profile weight rowTarget areaTarget) : 0 <
  allocation.component := by
  rw [allocation.component_eq]
  exact profile.perComponent_positive (Fraction.Order.Field.div_pos_direct allocation.row_positive (by decide +kernel))

/-- Adding one to the nonnegative word weight gives a positive divisor. -/
theorem weight_shift_positive (allocation : NormalFormBudgets.RowAllocation profile weight rowTarget areaTarget) : 0 <
  weight + 1 := by
  have translated := Fraction.Order.Arithmetic.add_lt_add_right_direct (by
      decide : (0 : WeightedPeriods.Coordinate) < 1) weight
  rw [zero_add, add_comm 1] at translated
  exact allocation.weight_nonnegative.trans_lt translated

/-- Both positive area constraints give a positive selected area cap. -/
theorem selected_positive (allocation : NormalFormBudgets.RowAllocation profile weight rowTarget areaTarget) : 0 <
  allocation.area := by
  rw [allocation.area_eq]
  exact Data.Rat.Fraction.Order.Basic.lt_min allocation.area_positive
    (Fraction.Order.Arithmetic.mul_pos_direct allocation.weight_shift_positive allocation.component_positive)

/-- The selected area cap is at most the original area target. -/
theorem area_le (allocation : NormalFormBudgets.RowAllocation profile weight rowTarget areaTarget) : allocation.area ≤
  areaTarget := by
  rw [allocation.area_eq]
  exact Data.Rat.Fraction.Order.Basic.min_le_left _ _

/-- The selected area cap pays a word allowance no greater than the retained component budget. -/
theorem word_le (allocation : NormalFormBudgets.RowAllocation profile weight rowTarget areaTarget) :
    Weighted.allowance allocation.area weight ≤ allocation.component := by
  apply (Fraction.Order.Field.div_le_iff_pos allocation.weight_shift_positive).mpr
  have bound : allocation.area ≤ (weight + 1) * allocation.component := by
    rw [allocation.area_eq]
    exact Data.Rat.Fraction.Order.Basic.min_le_right _ _
  exact bound.trans_eq (by ring1)

/-- Two squared-error transfers cost 22 times the row mass. The reserve of 32 gives a strict positive margin even for
empty and zero-weight rows. -/
theorem row_charge_lt (allocation : NormalFormBudgets.RowAllocation profile weight rowTarget areaTarget) (row : Fin
  rows) :
    22 * (profile.coefficients.get row).mass * allocation.component < rowTarget := by
  have coefficients := Fraction.Order.Arithmetic.mul_le_mul_direct (by
      decide +kernel : (22 : WeightedPeriods.Coordinate) ≤ 32)
    (profile.mass_le_total row) (profile.coefficients.get row).mass_nonnegative (by decide +kernel)
  have charged := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct coefficients
    allocation.component_positive.le
  have reserved := Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by
      decide +kernel : (0 : WeightedPeriods.Coordinate) < 32)
    (profile.total_mul_perComponent_lt (Fraction.Order.Field.div_pos_direct allocation.row_positive (by
        decide +kernel : (0 : WeightedPeriods.Coordinate) < 32)))
  rw [← allocation.component_eq] at reserved
  have paid : 32 * (rowTarget / 32) = rowTarget := by
    rw [Fraction.Field.mul_comm]
    exact Fraction.Field.div_mul_cancel_of_ne _ _ (by decide +kernel)
  rw [paid, ← mul_assoc] at reserved
  exact charged.trans_lt reserved

end RowAllocation
end Purelib.Topology.Surface.Word.NormalFormBudgets
