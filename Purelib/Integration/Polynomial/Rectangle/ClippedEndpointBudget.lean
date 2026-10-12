module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.PrimitiveJumps

public import Purelib.Riemann.Periods.ClippedBilinearBudget
public import Purelib.Integration.Path.EndpointJump
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Mathlib.Order.Basic
import Purelib.Tactic.Ring
public import Purelib.Topology.Surface.Cut.WordArea

open Purelib.Topology.Polygon.Stokes (PrimitivePoint)

public section

/-! The existing area allowance also pays normalized endpoint errors. -/
namespace Purelib.Riemann.Periods.ClippedBilinearBudget
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)

open Purelib.Riemann.Periods.CenteredBilinearPath (Sample)
open Purelib.Riemann.Periods (ClippedBilinearBudget)
variable {count : Nat} {magnitude target : Coordinate}

open Purelib.Data.Rat in
/-- For a positive retained count, sixteen times the clipped bilinear error is below the original target.

The count-square and nonnegative magnitude factors bound sixteen by the retained
weight. Its original error-payment certificate supplies the strict target bound. -/
theorem sixteen_error_lt (budget : ClippedBilinearBudget count
  magnitude target) (positive : 0 < count) :
    16 * budget.error < target := by
  have oneLe : (1 : Coordinate) ≤ (count : Coordinate) :=
    Fraction.Cast.Order.natCast_le_direct positive
  have squareLe : (1 : Coordinate) ≤ (count : Coordinate) ^ 2 := by
    have estimate := Fraction.Order.Arithmetic.mul_le_mul_direct oneLe oneLe
      (by decide +kernel : (0 : Coordinate) ≤ 1) ((by decide +kernel : (0 : Coordinate) ≤ 1).trans oneLe)
    simpa only [one_mul, pow_two] using estimate
  have magnitudeLe : (1 : Coordinate) ≤ magnitude + 1 := by
    simpa only [zero_add] using
      Fraction.Order.Arithmetic.add_le_add_direct budget.magnitude_nonnegative (le_rfl : (1 : Coordinate) ≤ 1)
  have productLe : (1 : Coordinate) ≤ (count : Coordinate) ^ 2 * (magnitude + 1) := by
    simpa only [one_mul] using Fraction.Order.Arithmetic.mul_le_mul_direct squareLe magnitudeLe
      (by decide +kernel : (0 : Coordinate) ≤ 1) ((by decide +kernel : (0 : Coordinate) ≤ 1).trans squareLe)
  have weightLe : (16 : Coordinate) ≤ budget.weight := by
    rw [budget.weight_eq]
    have estimate := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct productLe
      (by decide +kernel : (0 : Coordinate) ≤ 32)
    have rearrange : 32 * ((count : Coordinate) ^ 2 * (magnitude + 1)) =
        (count : Coordinate) ^ 2 * (32 * (magnitude + 1)) := by ring1
    rw [rearrange] at estimate
    exact (by decide +kernel : (16 : Coordinate) ≤ 32).trans (by simpa only [one_mul, mul_one] using estimate)
  exact (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct weightLe budget.error_positive.le).trans_lt
    budget.error_paid

open Purelib.Data.Gaussian in
open Purelib.Riemann.Periods in
open Purelib.Topology.Polygon in
/-- An endpoint increment error bounded by sixteen times the retained error is below the target.

The zero-count case uses the exact vanishing endpoint increments; positive counts use the retained budget payment. -/
theorem endpoint_paid (budget : ClippedBilinearBudget count
  magnitude target)
    {leftValues rightValues : Fin (count + 1) → PrimitivePoint}
    (left : Sample leftValues) (right : Sample rightValues)
    (bounded : Data.Gaussian.Norm.Basic.normSq (CenteredBilinearPath.Sample.endpointIncrementError left right) ≤ 16 *
      budget.error) :
    Data.Gaussian.Norm.Basic.normSq (CenteredBilinearPath.Sample.endpointIncrementError left right) < target := by
  cases count with
  | zero =>
      have subSelf (value : PrimitivePoint) :
          Stokes.PrimitivePoint.sub value value = PrimitivePoint.zero := by
        cases value
        change Stokes.PrimitivePoint.mk _ _ = Stokes.PrimitivePoint.mk 0 0
        exact congrArg₂ Stokes.PrimitivePoint.mk (sub_self _) (sub_self _)
      have leftZero : left.centered (Fin.last 0) = PrimitivePoint.zero := by
        rw [left.centered_eq]
        exact subSelf _
      have rightZero : right.centered (Fin.last 0) = PrimitivePoint.zero := by
        rw [right.centered_eq]
        exact subSelf _
      have zero : CenteredBilinearPath.Sample.endpointIncrementError left right = 0 := by
        rw [CenteredBilinearPath.Sample.endpointIncrementError, leftZero, rightZero]
        change (rightValues 0).left * (0 - 0) - (0 - 0) * (rightValues 0).right = 0
        rewrite [sub_self, mul_zero, zero_mul, sub_self]
        exact Eq.refl _
      rw [zero, Norm.Basic.normSq_zero]
      exact budget.target_positive
  | succ count => exact bounded.trans_lt (budget.sixteen_error_lt (Nat.succ_pos _))

end Purelib.Riemann.Periods.ClippedBilinearBudget

namespace Purelib.Riemann.Periods.CenteredBilinearPath.Sample

open Purelib.Riemann.Periods.CenteredBilinearPath (Sample Coordinate)

variable {count : Nat} {leftValues rightValues : Fin (count + 1) → PrimitivePoint}

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Riemann.Periods in
/-- Area and endpoint-increment errors below one target give a jump-corrected area error below four times that target.

The retained area and endpoint errors are each measured by their squared Gaussian norm. The two-term square bound gives
the stated factor four without changing either error. -/
theorem jump_comparison (left : Sample leftValues) (right :
  Sample rightValues) {target : Coordinate}
    (area : Data.Gaussian.Norm.Basic.normSq ((left.originalArea - right.originalArea) - (left.endpoint -
      right.endpoint)) <
      target)
    (endpoint : Data.Gaussian.Norm.Basic.normSq (CenteredBilinearPath.Sample.endpointIncrementError left right) <
      target) :
    Data.Gaussian.Norm.Basic.normSq ((left.originalArea - right.originalArea) -
      CenteredBilinearPath.Sample.endpointJump left
      right) < 4 * target := by
  have equal : (left.originalArea - right.originalArea) - CenteredBilinearPath.Sample.endpointJump left right =
      ((left.originalArea - right.originalArea) - (left.endpoint - right.endpoint)) +
        CenteredBilinearPath.Sample.endpointIncrementError left right := by
    rw [CenteredBilinearPath.Sample.endpoint_difference left right]
    ring1
  rw [equal]
  exact (Norm.Bounds.normSq_add_le_two _ _).trans_lt
    ((Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : Coordinate) < 2)
      (Fraction.Order.Arithmetic.add_lt_add_direct area endpoint)).trans_eq (by ring1))

end Purelib.Riemann.Periods.CenteredBilinearPath.Sample

end
