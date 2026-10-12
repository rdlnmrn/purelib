module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Gaussian.Budget.Aggregate
public import Purelib.Approximation.Rational.Budget.Aggregate
public import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Bounds
public import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Vector.Basic
import Purelib.LinearAlgebra.Alternating.Handle.Basic

import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.PrimitiveJumps
public import Purelib.Topology.Surface.Boundary.NormalFormArea
public import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.CCL.Calculus.WeightedAggregateBudget
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Data.Int.Cast.Defs
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Data.Nat.Cast.Defs
import Purelib.Tactic.Ring

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Rational.Budget

open Purelib.CCL.Calculus

open Purelib.Data

open Purelib.Data.Gaussian.Basic

open Purelib.Data.Gaussian.Norm.Basic

open Purelib.Data.List

open Purelib.Data.Rat

open Purelib.LinearAlgebra.Alternating

open Purelib.Riemann.Readings

open Purelib.Topology.Polygon

open Purelib.Topology.Polygon.Stokes

open Purelib.Topology.Surface.Boundary

public section

/-!
# Paid finite perturbations of handle areas

The magnitude bound is fixed before the perturbed readings are requested.
Both primitive components and both factors of the handle count are paid.
No physical-boundary coordinate is removed by this estimate.
-/

namespace Purelib.Topology.Surface.Boundary.HandleAreaBounds

open Purelib.Topology.Surface.Boundary.NormalFormArea
open _root_.Purelib.Topology.Surface.Boundary renaming NormalFormArea -> NormalFormArea
open Purelib.Riemann.Readings.PrimitiveAreaBounds

open Purelib.Topology.Polygon.Stokes (PrimitivePoint edgeArea)
open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib.Data.Gaussian.Basic.Canonical
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.LinearAlgebra.Alternating.Handle.Basic (PivotIndices)

namespace PrimitivePoint

open Purelib.Topology.Surface.Boundary.HandleAreaBounds
/-- A perturbed primitive point is bounded by twice its original magnitude plus error allowance. -/
theorem perturbation_bounded {original changed : Stokes.PrimitivePoint} {magnitude error :
  PrimitiveAreaBounds.AreaCoordinate}
    (bounded : (PrimitivePoint.Bounded original) magnitude) (accurate : (PrimitivePoint.Bounded ((PrimitivePoint.sub
      changed) original)) error) :
    (PrimitivePoint.Bounded changed) (2 * (magnitude + error)) := by
  have equal : original.add ((PrimitivePoint.sub changed) original) = changed := by
    simp only [PrimitivePoint.add, PrimitivePoint.sub]
    congr 1 <;> ring1
  exact equal ▸ PrimitiveAreaBounds.PrimitivePoint.bounded_add bounded accurate

/-- The polynomial weight includes the product of the two perturbations. The unit cap makes this a linear allowance
selected before sampling. -/
theorem area_difference_bound {first last changedFirst changedLast : Stokes.PrimitivePoint}
    {magnitude error : PrimitiveAreaBounds.AreaCoordinate} (nonnegative : 0 ≤ magnitude) (errorNonnegative : 0 ≤ error)
    (small : error ≤ 1) (firstBound : (PrimitivePoint.Bounded first) magnitude) (lastBound : (PrimitivePoint.Bounded
      last) magnitude)
    (firstError : (PrimitivePoint.Bounded ((PrimitivePoint.sub changedFirst) first)) error) (lastError :
      (PrimitivePoint.Bounded ((PrimitivePoint.sub changedLast) last)) error) :
    Data.Gaussian.Norm.Basic.normSq (Stokes.edgeArea changedFirst changedLast - Stokes.edgeArea first last) ≤ 32 *
      (magnitude + 1) *
      error := by
  have expanded : Stokes.edgeArea changedFirst changedLast - Stokes.edgeArea first last =
      Stokes.edgeArea ((PrimitivePoint.sub changedFirst) first) changedLast + Stokes.edgeArea first ((PrimitivePoint.sub
        changedLast) last) := by
    simp only [Stokes.edgeArea, PrimitivePoint.sub]
    ring1
  rw [expanded]
  have firstTerm := PrimitivePoint.area_bound
    firstError (perturbation_bounded lastBound lastError)
  have lastTerm := PrimitivePoint.area_bound firstBound lastError
  rw [← Gaussian.Norm.Basic.normSq_eq_canonical] at firstTerm lastTerm
  have estimate := (Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Fraction.Order.Arithmetic.add_le_add_direct firstTerm lastTerm) (by decide))
  have quadratic := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct small errorNonnegative
  rw [_root_.one_mul] at quadratic
  have extra : 0 ≤ 8 * magnitude + 16 := add_nonneg
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) nonnegative) (by decide +kernel)
  have slack := Fraction.Order.Arithmetic.mul_nonneg_direct extra errorNonnegative
  have paid := add_le_add (le_refl (24 * magnitude * error))
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct quadratic (by
        decide +kernel : (0 : PrimitiveAreaBounds.AreaCoordinate) ≤ 16))
  calc
    _ ≤ 2 * (4 * error * (2 * (magnitude + error)) + 4 * magnitude * error) := estimate
    _ = 24 * magnitude * error + 16 * (error * error) := by ring1
    _ ≤ 24 * magnitude * error + 16 * error := paid
    _ ≤ (24 * magnitude * error + 16 * error) + (8 * magnitude + 16) * error := le_add_of_nonneg_right slack
    _ = 32 * (magnitude + 1) * error := by ring1

end PrimitivePoint

/-- Sum the edge areas of the two supplied primitive readings at each retained handle. -/
@[expose] def sampledHandleArea {count : Nat} (raw : List (Handle.Basic.PivotIndices count))
    (first last : Handle.Basic.PivotIndices count → Stokes.PrimitivePoint) : Gaussian.Basic.Canonical :=
  Data.Gaussian.Norm.Sum.Basic.gaussianSum (raw.map fun pair => Stokes.edgeArea (first pair) (last pair))

section
open Purelib.Topology.Surface.Boundary
/-- Equal readings on every retained handle give equal sampled handle areas. -/
theorem sampledHandleArea_congr {count : Nat} (raw : List (Handle.Basic.PivotIndices count))
    {first last changedFirst changedLast : Handle.Basic.PivotIndices count → Stokes.PrimitivePoint}
    (firstEq : ∀ pair ∈ raw, first pair = changedFirst pair)
    (lastEq : ∀ pair ∈ raw, last pair = changedLast pair) :
    sampledHandleArea raw first last = sampledHandleArea raw changedFirst changedLast
      := by
  induction raw with
  | nil => rfl
  | cons pair raw ih =>
      change Stokes.edgeArea (first pair) (last pair) + sampledHandleArea raw first last =
        Stokes.edgeArea (changedFirst pair) (changedLast pair) + sampledHandleArea raw changedFirst
          changedLast
      rw [firstEq pair List.mem_cons_self, lastEq pair List.mem_cons_self]
      exact congrArg (Stokes.edgeArea (changedFirst pair) (changedLast pair) + ·)
        (ih (fun next member => firstEq next (List.mem_cons_of_mem _ member))
          (fun next member => lastEq next (List.mem_cons_of_mem _ member)))

/-- The recursive normal-form handle area equals the finite sampled handle-area sum. -/
theorem handleArea_eq_sum {count : Nat} (raw : List (Handle.Basic.PivotIndices count))
    (values : Data.Vector Stokes.PrimitivePoint count) :
    NormalFormArea.handleArea raw values = sampledHandleArea raw (fun pair => values pair.1) (fun pair
      => values pair.2) := by
  induction raw with
  | nil => rfl
  | cons pair raw ih => exact congrArg (Stokes.edgeArea (values pair.1) (values pair.2) + ·) ih

/-- The difference of sampled and retained handle areas is the sum of their individual differences. -/
theorem sampledHandleArea_sub {count : Nat} (raw : List (Handle.Basic.PivotIndices count))
    (first last : Handle.Basic.PivotIndices count → Stokes.PrimitivePoint)
    (values : Data.Vector Stokes.PrimitivePoint count) :
    sampledHandleArea raw first last - NormalFormArea.handleArea raw values =
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (raw.map fun pair => Stokes.edgeArea (first pair) (last pair) -
        Stokes.edgeArea (values pair.1) (values pair.2)) := by
  induction raw with
  | nil => exact Gaussian.Basic.sub_self _
  | cons pair raw ih =>
      change (Stokes.edgeArea (first pair) (last pair) + sampledHandleArea raw first last) -
        (Stokes.edgeArea (values pair.1) (values pair.2) + NormalFormArea.handleArea raw values) = _
      change _ = (Stokes.edgeArea (first pair) (last pair) - Stokes.edgeArea (values pair.1) (values pair.2)) + _
      rw [← ih]
      ring1

end

open Purelib.Topology.Surface.Boundary in
open Purelib.Topology.Surface.Boundary.HandleAreaBounds in
/-- Paid component perturbations bound the squared norm of the complete handle-area error.

The input magnitude and error are nonnegative, each error is capped by one, and the aggregate budget pays the actual
retained handle count. -/
theorem sampledHandleArea_accurate {count : Nat} (raw : List (Handle.Basic.PivotIndices count))
    (first last : Handle.Basic.PivotIndices count → Stokes.PrimitivePoint)
    (values : Data.Vector Stokes.PrimitivePoint count) {target magnitude error :
      PrimitiveAreaBounds.AreaCoordinate}
    (positive : 0 < target) (nonnegative : 0 ≤ magnitude) (errorNonnegative : 0 ≤ error) (small : error ≤ 1)
    (paid : error ≤ Aggregate.perTerm
      (Weighted.allowance target (32 * (magnitude + 1))) raw.length)
    (bounded : ∀ pair ∈ raw, (PrimitivePoint.Bounded (values pair.1)) magnitude ∧ (PrimitivePoint.Bounded (values
      pair.2)) magnitude)
    (accurate : ∀ pair ∈ raw, (PrimitivePoint.Bounded ((PrimitivePoint.sub (first pair)) (values pair.1))) error ∧
      (PrimitivePoint.Bounded ((PrimitivePoint.sub (last pair)) (values pair.2))) error) :
    Data.Gaussian.Norm.Basic.normSq (sampledHandleArea raw first last - NormalFormArea.handleArea raw
      values) < target
      := by
  have weightNonnegative : 0 ≤ 32 * (magnitude + 1) := Fraction.Order.Arithmetic.mul_nonneg_direct
    (by decide +kernel) (add_nonneg nonnegative (by decide))
  rw [sampledHandleArea_sub]
  apply Gaussian.Budget.Aggregate.normSq_sum_lt _ positive
  intro value member
  obtain ⟨pair, member, same⟩ := Map.mem_map.mp member
  rw [← same, Data.List.Map.length_map]
  exact (PrimitivePoint.area_difference_bound nonnegative errorNonnegative small
    (bounded pair member).1 (bounded pair member).2 (accurate pair member).1 (accurate pair member).2).trans
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct paid weightNonnegative).trans
      (WeightedAggregateBudget.weighted_perTerm_le positive weightNonnegative raw.length))

end Purelib.Topology.Surface.Boundary.HandleAreaBounds
