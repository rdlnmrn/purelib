module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Periods.CenteredBilinearPath
public import Purelib.Integration.Path.NoisyPathArea
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib

open Purelib.Data.Rat

open Purelib.Integration.Path

open Purelib.Integration.Path.NoisyPathArea

open Purelib.Riemann.Periods

public section

/-! Select positive owner-error tolerances below a requested cap without
changing the trace count or increasing its total length allowance. -/
namespace Purelib.Approximation.Budget.RequestedLengthBudget

open Purelib.Riemann.Periods.CenteredBilinearPath (Coordinate)
open Purelib.Integration.Path.NoisyPathArea (LengthErrorBudget)
open Purelib.Integration.Path.NoisyPathArea.LengthErrorBudget (build)

open Purelib.Data.Rat.Fraction.Compatibility

set_option genInjectivity false in
/-- A finite length-error budget whose tolerance is at most the displayed request target.

The original trace count and total length allowance remain indices of the retained budget. -/
structure Requested (count : Nat) (allowance target : CenteredBilinearPath.Coordinate) where
  /-- The retained length-error budget with the original trace count and allowance. -/ budget :
    NoisyPathArea.LengthErrorBudget count allowance
  /-- The retained budget's tolerance does not exceed the displayed request target. -/ tolerance_le : budget.tolerance ≤
    target

constructive_injectivity Requested

/-- Construct a positive finite length-error budget below the requested tolerance.

The padding is reduced by the original allowance, one, and the positive target, while preserving the original trace
count and total payment bound. -/
@[expose] def requested (count : Nat) (allowance target : CenteredBilinearPath.Coordinate)
    (allowancePositive : 0 < allowance) (targetPositive : 0 < target) :
      Approximation.Budget.RequestedLengthBudget.Requested count allowance target := by
  let original := LengthErrorBudget.build count allowance allowancePositive
  let padding := min original.padding (min 1 target)
  have paddingPositive : 0 < padding := Purelib.Data.Rat.Fraction.Order.Basic.lt_min original.padding_positive
    (Purelib.Data.Rat.Fraction.Order.Basic.lt_min (by decide) targetPositive)
  have originalBound : padding ≤ original.padding := Purelib.Data.Rat.Fraction.Order.Basic.min_le_left ..
  have unitBound : padding ≤ 1 := (Purelib.Data.Rat.Fraction.Order.Basic.min_le_right ..).trans
    (Purelib.Data.Rat.Fraction.Order.Basic.min_le_left ..)
  have targetBound : padding ≤ target := (Purelib.Data.Rat.Fraction.Order.Basic.min_le_right ..).trans
    (Purelib.Data.Rat.Fraction.Order.Basic.min_le_right ..)
  have squareBound : padding^2 ≤ padding := by
    have bounded := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct unitBound paddingPositive.le
    simpa only [-eq_self, -iff_self, pow_two, mul_one] using bounded
  let budget : NoisyPathArea.LengthErrorBudget count allowance :=
    ⟨padding, paddingPositive,
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct originalBound (Fraction.Cast.Order.natCast_le_direct
        (Nat.zero_le count))).trans original.paid,
      padding^2, Fraction.Order.Arithmetic.pow_pos_direct paddingPositive 2, rfl⟩
  exact ⟨budget, squareBound.trans targetBound⟩

end Purelib.Approximation.Budget.RequestedLengthBudget
