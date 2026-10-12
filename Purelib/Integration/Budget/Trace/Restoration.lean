module
meta import Purelib.Elab.ConstructiveInjectivity
public import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Data.Rat.Fraction.Field
public import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Data.Rat.Fraction.Compatibility
public import Purelib.Integration.Path.IncrementArea
import Purelib.Integration.Path.HomogeneousTraceRestoration
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

public section

/-! Select the common source allowance before endpoint acquisition, paying
the homogeneous detour and incoming-potential costs. -/
namespace Purelib.Integration.Budget.Trace.Restoration

open Purelib.Integration.Path.IncrementArea (Coordinate)
open Purelib.Data.Rat.Fraction.Compatibility

set_option genInjectivity false in
open Purelib.Approximation.Rational in
open Purelib.Integration.Path in
/-- A positive source allowance and exact common target paying the original trace-restoration cost.

The source is capped at one quarter and the target is four times its square; retained certificates bound chart cost,
target size and the full restoration payment. -/
structure BasisCommonRestorationAllowance (allowance : IncrementArea.Coordinate) where
  /-- The exact retained positive allowance for source displacements. -/ sourceAllowance : IncrementArea.Coordinate
  /-- The source allowance is the minimum of one quarter and the original weighted restoration budget. -/ source_eq :
    sourceAllowance = min (1 / 4) (Budget.Weighted.allowance ((4 * allowance)^2) 1744)
  /-- The retained source allowance is strictly positive. -/ source_positive : 0 < sourceAllowance
  /-- The cached common restoration target. -/ target : IncrementArea.Coordinate
  /-- The target is four times the retained source allowance squared. -/ target_eq : target = 4 * sourceAllowance^2
  /-- The retained restoration target is strictly positive. -/ positive : 0 < target
  /-- The retained target is at most one. -/ small : target ≤ 1
  /-- Ten source-allowance squares are bounded by four times the retained target. -/ chart_paid : 10 * sourceAllowance^2
    ≤ 4 * target
  /-- The exact 416-plus-20 target cost is bounded by the square of four times the original allowance. -/ paid : 416 *
    target + 20 * target ≤ (4 * allowance)^2

constructive_injectivity BasisCommonRestorationAllowance

namespace BasisCommonRestorationAllowance

open Purelib.Approximation.Rational in
open Purelib.Data.Rat in
open Purelib.Integration in
open Purelib.Integration.Path in
/-- Allocate and retain a common restoration allowance for the original positive target allowance.

The exact weighted source budget and quarter cap are cached once, with the original numerical factors in every payment
certificate. -/
@[expose] def build (allowance : IncrementArea.Coordinate) (positive : 0 < allowance) :
  Budget.Trace.Restoration.BasisCommonRestorationAllowance allowance := by
  let source := min (1 / 4) (Budget.Weighted.allowance ((4 * allowance)^2) 1744)
  have sourcePositive : 0 < source := Fraction.Order.Basic.lt_min (by decide) (Budget.Weighted.allowance_positive
    (Fraction.Order.Arithmetic.pow_pos_direct (Fraction.Order.Arithmetic.mul_pos_direct (by decide) positive) 2) (by
      decide +kernel))
  have quarter : source ≤ 1 / 4 := Fraction.Order.Basic.min_le_left _ _
  have one : source ≤ 1 := quarter.trans (by decide)
  have squared : source^2 ≤ source := by
    exact (show source^2 = source * source by ring1).trans_le
      ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct one sourcePositive.le).trans_eq
        (Fraction.Field.mul_one_direct _))
  have small : 4 * source^2 ≤ 1 :=
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (squared.trans quarter) (by decide)).trans_eq (by
      decide)
  have paid := (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (squared.trans (show source ≤ Budget.Weighted.allowance ((4 * allowance)^2) 1744 from
      Fraction.Order.Basic.min_le_right _ _))
    (by decide +kernel : (0 : IncrementArea.Coordinate) ≤ 1744)).trans
      (Budget.Weighted.mul_allowance_le (Fraction.Order.Arithmetic.sq_nonneg_direct _) (by decide +kernel))
  refine ⟨source, rfl, sourcePositive, 4 * source^2, rfl,
    Fraction.Order.Arithmetic.mul_pos_direct (by decide) (Fraction.Order.Arithmetic.pow_pos_direct sourcePositive 2),
      small, ?_, ?_⟩
  · exact (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (by decide : (10 : IncrementArea.Coordinate) ≤
      16) (Fraction.Order.Arithmetic.sq_nonneg_direct source)).trans_eq (by ring1)
  · exact (show 416 * (4 * source^2) + 20 * (4 * source^2) = 1744 * source^2 by ring1).trans_le paid

open Purelib.Integration in
open Purelib.Integration.Path in
/-- Read half the exact retained source allowance for the incoming connector. -/
@[expose] def incomingAllowance {allowance : IncrementArea.Coordinate} (allocation :
  Budget.Trace.Restoration.BasisCommonRestorationAllowance allowance) : Coordinate :=
  allocation.sourceAllowance / 2

open Purelib.Data.Rat
open Purelib.Integration
open Purelib.Integration.Path
/-- The retained incoming connector allowance is strictly positive. -/
theorem incoming_positive {allowance : IncrementArea.Coordinate} (allocation :
  Budget.Trace.Restoration.BasisCommonRestorationAllowance allowance) :
    0 < allocation.incomingAllowance := Fraction.Order.Field.div_pos_direct allocation.source_positive (by decide)

/-- The incoming allowance squared is exactly one sixteenth of the retained target. -/
theorem incoming_square {allowance : IncrementArea.Coordinate} (allocation :
  Budget.Trace.Restoration.BasisCommonRestorationAllowance allowance) :
    allocation.incomingAllowance^2 = allocation.target / 16 := by
  rw [Budget.Trace.Restoration.BasisCommonRestorationAllowance.incomingAllowance, allocation.target_eq]
  calc
    (allocation.sourceAllowance / 2)^2 = allocation.sourceAllowance^2 * ((2 : IncrementArea.Coordinate)⁻¹)^2 := by
      simp only [Fraction.Field.div_eq_mul_inv_direct]; ring1
    _ = allocation.sourceAllowance^2 * (4 * (16 : IncrementArea.Coordinate)⁻¹) := by
      rw [show ((2 : IncrementArea.Coordinate)⁻¹)^2 = 4 * (16 : IncrementArea.Coordinate)⁻¹ by decide]
    _ = (4 * allocation.sourceAllowance^2) / 16 := by simp only [Fraction.Field.div_eq_mul_inv_direct]; ring1

/-- Any nonnegative source below the retained incoming allowance has squared value at most target divided by sixteen. -/
theorem incoming_paid {allowance source : IncrementArea.Coordinate} (allocation :
  Budget.Trace.Restoration.BasisCommonRestorationAllowance allowance)
    (nonnegative : 0 ≤ source) (smaller : source ≤ allocation.incomingAllowance) :
    source^2 ≤ allocation.target / 16 :=
  (Fraction.Order.Arithmetic.pow_le_pow_direct nonnegative smaller 2).trans_eq allocation.incoming_square

end BasisCommonRestorationAllowance
end Purelib.Integration.Budget.Trace.Restoration
