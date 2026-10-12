module
import Purelib.Data.Rat.Fraction.Order.Arithmetic
meta import Purelib.Elab.ConstructiveInjectivity
public import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Data.Rat.Fraction.Compatibility
public import Purelib.Riemann.Readings.PreparedPrimitiveRequests
import Purelib.Riemann.Readings.PreparedPrimitiveRequestBatches
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib

open Purelib.Approximation.Rational.Budget

open Purelib.Data.Rat

open Purelib.Riemann.Readings

public section

/-!
# One finite allocation for whole-path primitive comparison

The per-piece request pays the actual piece count, the full parent count,
and the full period movement mass simultaneously. The positive count-plus-one
and mass-plus-one denominators include empty and stationary paths.
-/

namespace Purelib.Approximation.Budget.PreparedPrimitiveBatchBudget

open Purelib.Approximation.Rational.Budget.Aggregate (perTerm perTerm_positive)
open Purelib.Riemann.Readings.PreparedPrimitiveRequests (Coordinate)

set_option genInjectivity false in
/-- A positive finite error allocation for a prepared primitive batch.

Its period, parent, coefficient and piece budgets retain the original target, both finite counts and the full
nonnegative movement mass. -/
structure BatchAllocation (target : PreparedPrimitiveRequests.Coordinate) (parentCount pieceCount : Nat) (mass :
  PreparedPrimitiveRequests.Coordinate) where
  /-- The retained total period-movement tolerance. -/ periodTarget : PreparedPrimitiveRequests.Coordinate
  /-- The period tolerance is exactly one quarter of the original target. -/ periodTarget_eq : periodTarget = target / 4
  /-- The period tolerance is strictly positive. -/ periodTarget_positive : 0 < periodTarget
  /-- The retained tolerance allocated against the original parent count. -/ localTarget :
    PreparedPrimitiveRequests.Coordinate
  /-- The parent tolerance is exactly the finite per-term allocation of the period tolerance. -/ localTarget_eq :
    localTarget = Aggregate.perTerm periodTarget parentCount
  /-- The parent tolerance is strictly positive. -/ localTarget_positive : 0 < localTarget
  /-- The retained coefficient tolerance accounting for the full movement mass. -/ coefficientTarget :
    PreparedPrimitiveRequests.Coordinate
  /-- The coefficient tolerance is exactly half the period tolerance divided by mass plus one. -/ coefficientTarget_eq :
    coefficientTarget = (periodTarget / 2) / (mass + 1)
  /-- The coefficient tolerance is strictly positive. -/ coefficientTarget_positive : 0 < coefficientTarget
  /-- The retained error allowance allocated against the original piece count. -/ errorBound :
    PreparedPrimitiveRequests.Coordinate
  /-- The error allowance is exactly the finite per-term allocation of the period tolerance. -/ errorBound_eq :
    errorBound = Aggregate.perTerm periodTarget pieceCount
  /-- The retained error allowance is strictly positive. -/ errorBound_positive : 0 < errorBound
  /-- The common target supplied to every displayed piece request. -/ pieceTarget : PreparedPrimitiveRequests.Coordinate
  /-- The piece target is the minimum of the error, parent and coefficient allowances. -/ pieceTarget_eq : pieceTarget =
    min errorBound (min localTarget coefficientTarget)
  /-- The common piece target is strictly positive. -/ pieceTarget_positive : 0 < pieceTarget
  /-- One quarter of the piece target is bounded by the retained parent tolerance. -/ piece_local_le : pieceTarget / 4 ≤
    localTarget
  /-- One quarter of the piece target is bounded by the retained coefficient tolerance. -/ piece_coefficient_le :
    pieceTarget / 4 ≤ coefficientTarget
  /-- The piece target is bounded by the retained error allowance. -/ piece_error_le : pieceTarget ≤ errorBound

constructive_injectivity BatchAllocation

namespace BatchAllocation

/-- Construct positive batch tolerances from the original positive target, finite counts and nonnegative movement mass.

The shared piece request pays all retained parent, coefficient and aggregate error bounds, including empty or stationary
data. -/
@[expose] def build (target : PreparedPrimitiveRequests.Coordinate) (positive : 0 < target) (parentCount pieceCount :
  Nat)
    (mass : PreparedPrimitiveRequests.Coordinate) (massNonnegative : 0 ≤ mass) :
      Approximation.Budget.PreparedPrimitiveBatchBudget.BatchAllocation target parentCount pieceCount mass :=
  let periodTarget := target / 4
  have periodPositive : 0 < periodTarget := Fraction.Order.Field.div_pos_direct positive (by decide)
  let localTarget := Aggregate.perTerm periodTarget parentCount
  have localPositive := Aggregate.perTerm_positive periodPositive parentCount
  let coefficientTarget := (periodTarget / 2) / (mass + 1)
  have coefficientPositive : 0 < coefficientTarget := Fraction.Order.Field.div_pos_direct
    (Fraction.Order.Field.div_pos_direct periodPositive (by decide))
    (Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct massNonnegative (by decide))
  let errorBound := Aggregate.perTerm periodTarget pieceCount
  have errorPositive := Aggregate.perTerm_positive periodPositive pieceCount
  let pieceTarget := min errorBound (min localTarget coefficientTarget)
  have piecePositive : 0 < pieceTarget := Fraction.Order.Basic.lt_min errorPositive (Fraction.Order.Basic.lt_min
    localPositive coefficientPositive)
  have quarterLe : pieceTarget / 4 ≤ pieceTarget := Fraction.Order.Field.divide_le_self piecePositive.le (by decide)
  { periodTarget := periodTarget, periodTarget_eq := rfl, periodTarget_positive := periodPositive
    localTarget := localTarget, localTarget_eq := rfl, localTarget_positive := localPositive
    coefficientTarget := coefficientTarget, coefficientTarget_eq := rfl, coefficientTarget_positive :=
      coefficientPositive
    errorBound := errorBound, errorBound_eq := rfl, errorBound_positive := errorPositive
    pieceTarget := pieceTarget, pieceTarget_eq := rfl, pieceTarget_positive := piecePositive
    piece_local_le := quarterLe.trans ((Fraction.Order.Basic.min_le_right _ _).trans (Fraction.Order.Basic.min_le_left _
      _))
    piece_coefficient_le := quarterLe.trans ((Fraction.Order.Basic.min_le_right _ _).trans
      (Fraction.Order.Basic.min_le_right _ _))
    piece_error_le := Fraction.Order.Basic.min_le_left _ _ }

/-- The piece-count-squared aggregate error payment is strictly below the retained period tolerance. -/
theorem error_lt {target mass : PreparedPrimitiveRequests.Coordinate} {parentCount pieceCount : Nat}
    (allocation : Approximation.Budget.PreparedPrimitiveBatchBudget.BatchAllocation target parentCount pieceCount mass)
      :
    (pieceCount : PreparedPrimitiveRequests.Coordinate) * ((pieceCount : PreparedPrimitiveRequests.Coordinate) *
      allocation.errorBound) < allocation.periodTarget := by
  rw [allocation.errorBound_eq]
  exact Aggregate.count_mul_perTerm_lt allocation.periodTarget_positive pieceCount

end BatchAllocation
end Purelib.Approximation.Budget.PreparedPrimitiveBatchBudget
