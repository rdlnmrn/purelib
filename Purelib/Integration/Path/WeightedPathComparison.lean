module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Weighted
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Integration.Path.WeightedPathArea
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.PrimitiveJumps
public import Purelib.Integration.Path.NoisyPathArea
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Vector.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

public section

/-! Finite summation by parts bounds the complete area discrepancy by total
length. The endpoint defect stays explicit; no vertex-count factor is added. -/
namespace Purelib.Integration.Path.WeightedPathComparison

open Purelib.Data.Gaussian
open Purelib.Topology.Polygon
open Purelib.Algebra
open Purelib.Integration.Path
open Purelib.Riemann.Periods
open Purelib.Data.Rat
open Purelib.Riemann.Readings

open Purelib.Riemann.Periods.CenteredBilinearPath (Coordinate Sample)
open Purelib.Integration.Path.NoisyPathArea (LengthErrorBudget)

open Purelib.Topology.Polygon.Stokes (PrimitivePoint edgeArea)

open Purelib.Data.Rat.Fraction.Compatibility
variable {count : Nat}

/-- The terminal-minus-initial cross-area defect between the two original primitive paths. -/
@[expose] def endpointDefect (first second : Fin (count + 1) → Stokes.PrimitivePoint) : Basic.Canonical :=
  Stokes.edgeArea (second (Fin.last count)) ((Stokes.PrimitivePoint.sub (first (Fin.last count))) (second (Fin.last
    count))) -
    Stokes.edgeArea (second 0) ((Stokes.PrimitivePoint.sub (first 0)) (second 0))

/-- The original path-area difference minus endpoint defect equals its exact local error-edge sum.

Each term keeps the original vertex discrepancy and the corresponding first or second path increment; the endpoint terms
telescope with their signs intact. -/
theorem area_difference_parts (first second : Fin (count + 1) → Stokes.PrimitivePoint) :
    CenteredBilinearPath.area first - CenteredBilinearPath.area second - WeightedPathComparison.endpointDefect first
      second = FiniteSum.Fin.sumFin (fun edge : Fin count =>
      Stokes.edgeArea ((Stokes.PrimitivePoint.sub (first edge.castSucc)) (second edge.castSucc))
        ((Stokes.PrimitivePoint.sub (first edge.succ)) (first edge.castSucc)) +
      Stokes.edgeArea ((Stokes.PrimitivePoint.sub (first edge.succ)) (second edge.succ)) ((Stokes.PrimitivePoint.sub
        (second edge.succ)) (second edge.castSucc))) := by
  have scalar (a b c d : Stokes.PrimitivePoint) : Stokes.edgeArea a b - Stokes.edgeArea c d =
      (Stokes.edgeArea ((Stokes.PrimitivePoint.sub a) c) ((Stokes.PrimitivePoint.sub b) a) + Stokes.edgeArea
        ((Stokes.PrimitivePoint.sub b) d) ((Stokes.PrimitivePoint.sub d) c)) +
        (Stokes.edgeArea d ((Stokes.PrimitivePoint.sub b) d) - Stokes.edgeArea c ((Stokes.PrimitivePoint.sub a) c)) :=
          by
    dsimp only [Stokes.edgeArea, Stokes.PrimitivePoint.sub]
    ring1
  have edges := FiniteSum.Fin.sumFin_congr (fun edge : Fin count => scalar
    (first edge.castSucc) (first edge.succ) (second edge.castSucc) (second edge.succ))
  unfold CenteredBilinearPath.area
  rw [← FiniteSum.Fin.sumFin_sub, edges, FiniteSum.Fin.sumFin_add,
    BoundaryRibbon.sum_increasing (fun vertex => Stokes.edgeArea (second vertex) ((Stokes.PrimitivePoint.sub (first
      vertex)) (second vertex)))]
  unfold WeightedPathComparison.endpointDefect
  ring1

/-- Bound the corrected area difference of two original paths using common nonnegative edge weights.

Uniform vertex error and separate increment bounds give sixteen times error times density times squared total weight. -/
theorem weighted_area_difference_bound (first second : Fin (count + 1) → Stokes.PrimitivePoint)
    (weights : Fin count → CenteredBilinearPath.Coordinate) {error density : CenteredBilinearPath.Coordinate}
    (nonnegative : ∀ edge, 0 ≤ weights edge)
    (accurate : ∀ vertex, (PrimitiveAreaBounds.PrimitivePoint.Bounded ((Stokes.PrimitivePoint.sub (first vertex))
      (second vertex))) error)
    (firstIncrements : ∀ edge : Fin count,
      (PrimitiveAreaBounds.PrimitivePoint.Bounded ((Stokes.PrimitivePoint.sub (first edge.succ)) (first edge.castSucc)))
        (density * (weights edge)^2))
    (secondIncrements : ∀ edge : Fin count,
      (PrimitiveAreaBounds.PrimitivePoint.Bounded ((Stokes.PrimitivePoint.sub (second edge.succ)) (second
        edge.castSucc))) (density * (weights edge)^2)) :
    Data.Gaussian.Norm.Basic.normSq (CenteredBilinearPath.area first - CenteredBilinearPath.area second -
      WeightedPathComparison.endpointDefect first second) ≤
      16 * error * density * (FiniteSum.Fin.sumFin weights)^2 := by
  rw [WeightedPathComparison.area_difference_parts]
  apply Norm.Weighted.normSq_sumFin_weighted _ weights nonnegative
  intro edge
  have firstBound := PrimitiveAreaBounds.PrimitivePoint.area_bound (accurate edge.castSucc) (firstIncrements edge)
  have secondBound := PrimitiveAreaBounds.PrimitivePoint.area_bound (accurate edge.succ) (secondIncrements edge)
  rw [← Norm.Basic.normSq_eq_canonical] at firstBound secondBound
  exact (Norm.Bounds.normSq_add_le_two _ _).trans
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Fraction.Order.Arithmetic.add_le_add_direct
        firstBound
        secondBound) (by decide)).trans_eq (by ring1))

namespace Sample
variable {first second : Fin (count + 1) → Purelib.Topology.Polygon.Stokes.PrimitivePoint}

/-- The cross-area discrepancy between the two original centered terminal values. -/
@[expose] def endpointDiscrepancy (left : CenteredBilinearPath.Sample first) (right : CenteredBilinearPath.Sample
  second) : Basic.Canonical :=
  Stokes.edgeArea (right.centered (Fin.last count))
    ((Stokes.PrimitivePoint.sub (left.centered (Fin.last count))) (right.centered (Fin.last count)))

/-- The original centered samples satisfy the weighted comparison after their exact endpoint discrepancy is removed.

Both sample owners, their separate increment witnesses and the same nonnegative original edge weights are retained. -/
theorem weighted_comparison (left : CenteredBilinearPath.Sample first) (right : CenteredBilinearPath.Sample second)
    (weights : Fin count → CenteredBilinearPath.Coordinate) {error density : CenteredBilinearPath.Coordinate}
    (nonnegative : ∀ edge, 0 ≤ weights edge)
    (accurate : ∀ vertex, (PrimitiveAreaBounds.PrimitivePoint.Bounded ((Stokes.PrimitivePoint.sub (left.centered
      vertex)) (right.centered vertex))) error)
    (firstIncrements : ∀ edge : Fin count,
      (PrimitiveAreaBounds.PrimitivePoint.Bounded ((Stokes.PrimitivePoint.sub (first edge.succ)) (first edge.castSucc)))
        (density * (weights edge)^2))
    (secondIncrements : ∀ edge : Fin count,
      (PrimitiveAreaBounds.PrimitivePoint.Bounded ((Stokes.PrimitivePoint.sub (second edge.succ)) (second
        edge.castSucc))) (density * (weights edge)^2)) :
    Data.Gaussian.Norm.Basic.normSq (left.centeredArea - right.centeredArea -
      WeightedPathComparison.Sample.endpointDiscrepancy left right) ≤
      16 * error * density * (FiniteSum.Fin.sumFin weights)^2 := by
  have estimate := WeightedPathComparison.weighted_area_difference_bound (fun vertex => left.centered vertex)
    (fun vertex => right.centered vertex) weights nonnegative accurate
    (fun edge => (WeightedPathArea.Sample.centered_increment left edge.castSucc edge.succ) ▸ firstIncrements edge)
    (fun edge => (WeightedPathArea.Sample.centered_increment right edge.castSucc edge.succ) ▸ secondIncrements edge)
  have origin : right.centered 0 = PrimitivePoint.zero := by
    rw [right.centered_eq]
    apply congrArg₂ Stokes.PrimitivePoint.mk <;> exact sub_self _
  rw [← left.centeredArea_eq, ← right.centeredArea_eq] at estimate
  unfold WeightedPathComparison.endpointDefect at estimate
  dsimp only at estimate
  rw [origin] at estimate
  have zero (point : Stokes.PrimitivePoint) : Stokes.edgeArea Stokes.PrimitivePoint.zero point = 0 := by
    dsimp only [Stokes.edgeArea, Stokes.PrimitivePoint.zero]
    ring1
  rw [zero, Basic.sub_zero] at estimate
  exact estimate

/-- Bound the full centered-area difference, including the retained endpoint discrepancy.

The estimate has factor forty times the uniform centered vertex error, common increment density and squared total
original weight. -/
theorem weighted_full_comparison (left : CenteredBilinearPath.Sample first) (right : CenteredBilinearPath.Sample second)
    (weights : Fin count → CenteredBilinearPath.Coordinate) {error density : CenteredBilinearPath.Coordinate}
    (nonnegative : ∀ edge, 0 ≤ weights edge)
    (accurate : ∀ vertex, (PrimitiveAreaBounds.PrimitivePoint.Bounded ((Stokes.PrimitivePoint.sub (left.centered
      vertex)) (right.centered vertex))) error)
    (firstIncrements : ∀ edge : Fin count,
      (PrimitiveAreaBounds.PrimitivePoint.Bounded ((Stokes.PrimitivePoint.sub (first edge.succ)) (first edge.castSucc)))
        (density * (weights edge)^2))
    (secondIncrements : ∀ edge : Fin count,
      (PrimitiveAreaBounds.PrimitivePoint.Bounded ((Stokes.PrimitivePoint.sub (second edge.succ)) (second
        edge.castSucc))) (density * (weights edge)^2)) :
    Data.Gaussian.Norm.Basic.normSq (left.centeredArea - right.centeredArea) ≤ 40 * error * density *
      (FiniteSum.Fin.sumFin
      weights)^2 := by
  have firstEnd := Norm.Weighted.normSq_sumFin_weighted
    (fun edge : Fin count => (second edge.succ).left - (second edge.castSucc).left)
    weights nonnegative (fun edge => by
      simpa only [Norm.Basic.normSq_eq_canonical, Stokes.PrimitivePoint.sub] using (secondIncrements edge).1)
  have secondEnd := Norm.Weighted.normSq_sumFin_weighted
    (fun edge : Fin count => (second edge.succ).right - (second edge.castSucc).right)
    weights nonnegative (fun edge => by
      simpa only [Norm.Basic.normSq_eq_canonical, Stokes.PrimitivePoint.sub] using (secondIncrements edge).2)
  simp only [Norm.Basic.normSq_eq_canonical] at firstEnd secondEnd
  rw [BoundaryRibbon.sum_increasing (fun vertex => (second vertex).left)] at firstEnd
  rw [BoundaryRibbon.sum_increasing (fun vertex => (second vertex).right)] at secondEnd
  have endpoint : (PrimitiveAreaBounds.PrimitivePoint.Bounded (right.centered (Fin.last count))) (density *
    (FiniteSum.Fin.sumFin weights)^2) := by
    rw [right.centered_eq]
    exact ⟨firstEnd, secondEnd⟩
  have boundary := PrimitiveAreaBounds.PrimitivePoint.area_bound endpoint (accurate (Fin.last count))
  rw [← Norm.Basic.normSq_eq_canonical] at boundary
  have internal := WeightedPathComparison.Sample.weighted_comparison left right weights nonnegative accurate
    firstIncrements secondIncrements
  have split : left.centeredArea - right.centeredArea =
      (left.centeredArea - right.centeredArea - WeightedPathComparison.Sample.endpointDiscrepancy left right) +
        WeightedPathComparison.Sample.endpointDiscrepancy left right := by ring1
  rw [split]
  exact (Norm.Bounds.normSq_add_le_two _ _).trans
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct internal
      boundary) (by decide)).trans_eq (by ring1))

end Sample
namespace LengthErrorBudget

/-- A retained length-error budget bounds the corrected centered-area difference of two noisy original samples.

The padding absorbs both original increment-noise bounds, and the total weight is paid by original total length plus
allowance. -/
theorem centered_comparison {allowance : CenteredBilinearPath.Coordinate} (budget : NoisyPathArea.LengthErrorBudget
  count allowance)
    {first second : Fin (count + 1) → Stokes.PrimitivePoint} (left : CenteredBilinearPath.Sample first) (right :
      CenteredBilinearPath.Sample second)
    (lengths : Fin count → CenteredBilinearPath.Coordinate) {error density : CenteredBilinearPath.Coordinate}
    (errorNonnegative : 0 ≤ error) (densityNonnegative : 0 ≤ density)
    (nonnegative : ∀ edge, 0 ≤ lengths edge)
    (accurate : ∀ vertex, (PrimitiveAreaBounds.PrimitivePoint.Bounded ((Stokes.PrimitivePoint.sub (left.centered
      vertex)) (right.centered vertex))) error)
    (firstIncrements : ∀ edge : Fin count, (PrimitiveAreaBounds.PrimitivePoint.Bounded ((Stokes.PrimitivePoint.sub
      (first edge.succ)) (first edge.castSucc)))
      (3 * budget.tolerance + 4 * density * (lengths edge)^2))
    (secondIncrements : ∀ edge : Fin count, (PrimitiveAreaBounds.PrimitivePoint.Bounded ((Stokes.PrimitivePoint.sub
      (second edge.succ)) (second edge.castSucc)))
      (3 * budget.tolerance + 4 * density * (lengths edge)^2)) :
    Data.Gaussian.Norm.Basic.normSq (left.centeredArea - right.centeredArea -
      WeightedPathComparison.Sample.endpointDiscrepancy left right) ≤
      16 * error * (4 * density + 3) * (FiniteSum.Fin.sumFin lengths + allowance)^2 := by
  have weightsNonnegative : ∀ edge, 0 ≤ lengths edge + budget.padding :=
    fun edge => add_nonneg (nonnegative edge) budget.padding_positive.le
  have weighted := WeightedPathComparison.Sample.weighted_comparison left right (fun edge => lengths edge +
    budget.padding)
    weightsNonnegative accurate (fun edge =>
      ⟨(firstIncrements edge).1.trans (budget.increment_bound densityNonnegative (nonnegative edge)),
        (firstIncrements edge).2.trans (budget.increment_bound densityNonnegative (nonnegative edge))⟩)
    (fun edge =>
      ⟨(secondIncrements edge).1.trans (budget.increment_bound densityNonnegative (nonnegative edge)),
        (secondIncrements edge).2.trans (budget.increment_bound densityNonnegative (nonnegative edge))⟩)
  have sumNonnegative {n : Nat} (weights : Fin n → CenteredBilinearPath.Coordinate) (positive : ∀ edge, 0 ≤ weights
    edge) :
      0 ≤ FiniteSum.Fin.sumFin weights := by
    induction n with
    | zero => exact le_rfl
    | succ n ih => rw [FiniteSum.Fin.sumFin_succ]; exact add_nonneg (positive 0) (ih _ (fun edge => positive edge.succ))
  exact weighted.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Fraction.Order.Arithmetic.pow_le_pow_direct (sumNonnegative _ weightsNonnegative) (budget.total_weight_le lengths)
      2)
    (Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      errorNonnegative)
      (add_nonneg (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) densityNonnegative) (by decide))))

/-- A retained length-error budget bounds the full centered-area difference of two noisy original samples.

The fortyfold estimate includes endpoint discrepancy while retaining both sample owners and their separate noisy
increment certificates. -/
theorem centered_full_comparison {allowance : CenteredBilinearPath.Coordinate} (budget : NoisyPathArea.LengthErrorBudget
  count allowance)
    {first second : Fin (count + 1) → Stokes.PrimitivePoint} (left : CenteredBilinearPath.Sample first) (right :
      CenteredBilinearPath.Sample second)
    (lengths : Fin count → CenteredBilinearPath.Coordinate) {error density : CenteredBilinearPath.Coordinate}
    (errorNonnegative : 0 ≤ error) (densityNonnegative : 0 ≤ density)
    (nonnegative : ∀ edge, 0 ≤ lengths edge)
    (accurate : ∀ vertex, (PrimitiveAreaBounds.PrimitivePoint.Bounded ((Stokes.PrimitivePoint.sub (left.centered
      vertex)) (right.centered vertex))) error)
    (firstIncrements : ∀ edge : Fin count, (PrimitiveAreaBounds.PrimitivePoint.Bounded ((Stokes.PrimitivePoint.sub
      (first edge.succ)) (first edge.castSucc)))
      (3 * budget.tolerance + 4 * density * (lengths edge)^2))
    (secondIncrements : ∀ edge : Fin count, (PrimitiveAreaBounds.PrimitivePoint.Bounded ((Stokes.PrimitivePoint.sub
      (second edge.succ)) (second edge.castSucc)))
      (3 * budget.tolerance + 4 * density * (lengths edge)^2)) :
    Data.Gaussian.Norm.Basic.normSq (left.centeredArea - right.centeredArea) ≤
      40 * error * (4 * density + 3) * (FiniteSum.Fin.sumFin lengths + allowance)^2 := by
  have weightsNonnegative : ∀ edge, 0 ≤ lengths edge + budget.padding :=
    fun edge => add_nonneg (nonnegative edge) budget.padding_positive.le
  have weighted := WeightedPathComparison.Sample.weighted_full_comparison left right (fun edge => lengths edge +
    budget.padding)
    weightsNonnegative accurate (fun edge =>
      ⟨(firstIncrements edge).1.trans (budget.increment_bound densityNonnegative (nonnegative edge)),
        (firstIncrements edge).2.trans (budget.increment_bound densityNonnegative (nonnegative edge))⟩)
    (fun edge =>
      ⟨(secondIncrements edge).1.trans (budget.increment_bound densityNonnegative (nonnegative edge)),
        (secondIncrements edge).2.trans (budget.increment_bound densityNonnegative (nonnegative edge))⟩)
  have sumNonnegative {n : Nat} (weights : Fin n → CenteredBilinearPath.Coordinate) (positive : ∀ edge, 0 ≤ weights
    edge) :
      0 ≤ FiniteSum.Fin.sumFin weights := by
    induction n with
    | zero => exact le_rfl
    | succ n ih => rw [FiniteSum.Fin.sumFin_succ]; exact add_nonneg (positive 0) (ih _ (fun edge => positive edge.succ))
  exact weighted.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Fraction.Order.Arithmetic.pow_le_pow_direct (sumNonnegative _ weightsNonnegative) (budget.total_weight_le lengths)
      2)
    (Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel)
      errorNonnegative)
      (add_nonneg (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) densityNonnegative) (by decide))))

end LengthErrorBudget
end Purelib.Integration.Path.WeightedPathComparison

end
