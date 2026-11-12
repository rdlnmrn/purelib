module

import Purelib.Data.Rat.Fraction.Order.Basic
public import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Approximation.Rational.Geometric.Basic
public import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Data.Rat.Fraction.Field
public import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Riemann.Integration.PreparedWeightedCoefficientBudget
import Purelib.Tactic.Ring
public import Purelib.Riemann.Normalization.InverseRootPolynomial
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Data.Rat.Fraction.Order

public section

/-! A pre-acquisition allocation pays the complete homogeneous trace error.
The source and origin ceilings and resampling scale are fixed inputs. -/
namespace Purelib.Riemann.Paths.PreparedWeightedTraceAllocation

open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius quarterRadius_antitone)
open Purelib.Approximation.Rational.Geometric.Search (firstQuarterBelow firstQuarterBelow_accurate)

open Purelib.Approximation in
set_option genInjectivity false in
/-- Retain a pre-acquisition budget for the complete weighted trace error.

Fixed source, origin and resampling ceilings determine a positive model tolerance and a cover floor. Separate
quarter-target payments account for the model and resampling errors. -/
structure WeightedTraceAllocation (target sourceBound originBound resamplingScale : Coordinate) where
  /-- The fixed source ceiling is nonnegative. -/ source_nonnegative : 0 ≤ sourceBound
  /-- The fixed starting-value ceiling is nonnegative. -/ origin_nonnegative : 0 ≤ originBound
  /-- The retained resampling scale is nonnegative. -/ scale_nonnegative : 0 ≤ resamplingScale
  /-- The positive model tolerance bounded by one. -/ tolerance : Coordinate
  /-- The tolerance is the minimum of one and the weighted quarter-target allowance. -/ tolerance_eq : tolerance = min 1
    (Rational.Budget.Weighted.allowance (target / 4) (64 * (sourceBound + 1) + 8 * originBound))
  /-- The selected model tolerance is strictly positive. -/ tolerance_positive : 0 < tolerance
  /-- The selected model tolerance is at most one. -/ tolerance_le_one : tolerance ≤ 1
  /-- The full model area and starting-ribbon error consume at most one quarter of the target. -/ model_paid : 64 *
    tolerance * (sourceBound + tolerance) + 8 * originBound * tolerance ≤ target / 4
  /-- The retained allowance for each of the two model-error terms. -/ half : Coordinate
  /-- The retained half is exactly half the model tolerance. -/ half_eq : half = tolerance / 2
  /-- Each model-error allowance is strictly positive. -/ half_positive : 0 < half
  /-- The retained dyadic floor paying the resampling error. -/ coverFloor : Nat
  /-- The cover floor is the explicit first-quarter search from zero. -/ coverFloor_eq : coverFloor =
    firstQuarterBelow resamplingScale 0 (target / 4)
  /-- The retained cover floor pays the resampling error within one quarter of the target. -/ resampling_paid :
    quarterRadius resamplingScale coverFloor ≤ target / 4

constructive_injectivity WeightedTraceAllocation

namespace WeightedTraceAllocation

open Purelib.Approximation in
open Purelib.Data in
/-- Select all model and resampling payments from the fixed ceilings.

For a positive target and nonnegative ceilings, the construction retains the tolerance, its two positive halves and the
explicit cover floor before acquiring a polynomial bank. -/
@[expose] def build (target sourceBound originBound resamplingScale : Coordinate)
    (positive : 0 < target) (sourceNonnegative : 0 ≤ sourceBound)
    (originNonnegative : 0 ≤ originBound) (scaleNonnegative : 0 ≤ resamplingScale) :
    WeightedTraceAllocation target sourceBound originBound resamplingScale := by
  let weight := 64 * (sourceBound + 1) + 8 * originBound
  have weightNonnegative : 0 ≤ weight := add_nonneg
    (Arithmetic.mul_nonneg_direct (by decide +kernel : (0 : Coordinate) ≤ 64) (add_nonneg
      sourceNonnegative (by decide)))
    (Arithmetic.mul_nonneg_direct (by decide : (0 : Coordinate) ≤ 8) originNonnegative)
  have quarterPositive : 0 < target / 4 := Field.div_pos_direct positive (by decide)
  let tolerance := min 1 (Rational.Budget.Weighted.allowance (target / 4) weight)
  have tolerancePositive : 0 < tolerance := Basic.lt_min (by decide)
    (Rational.Budget.Weighted.allowance_positive quarterPositive weightNonnegative)
  have paid : 64 * tolerance * (sourceBound + tolerance) + 8 * originBound * tolerance ≤ target / 4 := by
    have linear : 64 * tolerance * (sourceBound + tolerance) + 8 * originBound * tolerance ≤
        64 * tolerance * (sourceBound + 1) + 8 * originBound * tolerance :=
          Arithmetic.add_le_add_direct
      (Arithmetic.mul_le_mul_of_nonneg_left_direct (Arithmetic.add_le_add_direct
        le_rfl (Basic.min_le_left 1 _))
        (Arithmetic.mul_nonneg_direct (by decide +kernel : (0 : Coordinate) ≤ 64)
          tolerancePositive.le))
      (le_rfl : 8 * originBound * tolerance ≤ 8 * originBound * tolerance)
    have budget := (Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Basic.min_le_right 1 _) weightNonnegative).trans
      (Rational.Budget.Weighted.mul_allowance_le quarterPositive.le weightNonnegative)
    exact (linear.trans_eq (show 64 * tolerance * (sourceBound + 1) + 8 * originBound * tolerance = weight * tolerance
      by
      dsimp only [weight]; ring1)).trans budget
  exact ⟨sourceNonnegative, originNonnegative, scaleNonnegative, tolerance, rfl, tolerancePositive,
    Basic.min_le_left _ _, paid,
    tolerance / 2, rfl, Field.div_pos_direct tolerancePositive (by decide),
      firstQuarterBelow resamplingScale 0 (target / 4), rfl,
    (firstQuarterBelow_accurate resamplingScale scaleNonnegative 0 (target / 4)
      quarterPositive).le⟩

variable {target sourceBound originBound resamplingScale : Coordinate}

open Purelib.Data in
/-- The two retained half-allowances add to the selected tolerance. -/
theorem halves (allocation : WeightedTraceAllocation target sourceBound originBound resamplingScale) :
    allocation.half + allocation.half = allocation.tolerance := by
  rw [allocation.half_eq]
  exact (show allocation.tolerance / 2 + allocation.tolerance / 2 = (allocation.tolerance / 2) * 2 by ring1).trans
    (Rat.Fraction.Field.div_mul_cancel_of_ne _ _ (by decide : (2 : Coordinate) ≠ 0))

open Purelib.Approximation in
open Purelib.Data in
/-- Any later cover and any paid nonnegative model error satisfy the combined target.

The estimate includes the starting-value ribbon and twice the sum of model and resampling errors. -/
theorem paid (allocation : WeightedTraceAllocation target sourceBound originBound resamplingScale)
    {coverFloor : Nat} (later : allocation.coverFloor ≤ coverFloor) {error : Coordinate}
    (errorNonnegative : 0 ≤ error) (errorLe : error ≤ allocation.tolerance) :
    2 * (quarterRadius resamplingScale coverFloor + (64 * error * (sourceBound + error) + 8 *
      originBound * error)) ≤ target := by
  have product := Arithmetic.mul_le_mul_direct errorLe
    (Arithmetic.add_le_add_direct le_rfl errorLe)
    (add_nonneg allocation.source_nonnegative errorNonnegative) allocation.tolerance_positive.le
  have areaLe : 64 * error * (sourceBound + error) ≤
      64 * allocation.tolerance * (sourceBound + allocation.tolerance) := by
    rw [Rat.Fraction.Field.mul_assoc, Rat.Fraction.Field.mul_assoc]
    exact Arithmetic.mul_le_mul_of_nonneg_left_direct product (by
        decide +kernel : (0 : Coordinate) ≤ 64)
  have modelLe := (Arithmetic.add_le_add_direct areaLe
    (Arithmetic.mul_le_mul_of_nonneg_left_direct errorLe
      (Arithmetic.mul_nonneg_direct (by decide : (0 : Coordinate) ≤ 8)
        allocation.origin_nonnegative))).trans allocation.model_paid
  have resamplingLe := (quarterRadius_antitone allocation.scale_nonnegative
    later).trans allocation.resampling_paid
  exact (Arithmetic.mul_le_mul_of_nonneg_left_direct (Arithmetic.add_le_add_direct
    resamplingLe modelLe)
    (by decide : (0 : Coordinate) ≤ 2)).trans_eq
      ((show 2 * (target / 4 + target / 4) = (target / 4) * 4 by ring1).trans
        (Rat.Fraction.Field.div_mul_cancel_of_ne _ _ (by decide : (4 : Coordinate) ≠ 0)))

end WeightedTraceAllocation
end Purelib.Riemann.Paths.PreparedWeightedTraceAllocation
