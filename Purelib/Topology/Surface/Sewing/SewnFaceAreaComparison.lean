module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Algebra.FiniteSum.Rational.Squares
import Purelib.Approximation.Gaussian.Budget.Aggregate
public import Purelib.Approximation.Rational.Budget.Aggregate
public import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Integration.Energy.Polygon

import Purelib.CCL.Calculus.WeightedAggregateBudget
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Cut.PrimitiveJumps
public import Purelib.Integration.Surface.Sewn.Selection.Basic
import Purelib.Topology.Surface.Boundary.HandleAreaBounds
import Purelib.Riemann.Readings.PrimitiveAreaBounds
public import Purelib.Topology.Surface.Sewing.SewnPrimitiveRequests
import Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Field
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Order.Defs.LinearOrder
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Group.Defs
import Purelib.Data.Rat.Fraction
import Purelib.Data.Vector.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Data.Int.Cast.Defs
import Purelib.Tactic.Ring
import Purelib.Data.List.Filter
import Purelib.Data.List.Membership

open Purelib.Algebra.FiniteSum.Rational

open Purelib.Approximation.Gaussian

open Purelib.Approximation.Rational.Budget

open Purelib.CCL.Calculus

open Purelib.Data

open Purelib.Data.Gaussian.Norm.Basic

open Purelib.Data.List

open Purelib.Data.Rat

open Purelib.Integration.Energy

open Purelib.Integration.Surface.Sewn.Selection.Basic.SewnPrimitiveFaces

open Purelib.Polynomial.Geometry.Grid

open Purelib.Riemann.Readings.PrimitiveAreaBounds

open Purelib.Topology.Polygon

open Purelib.Topology.Polygon.Stokes

open Purelib.Topology.Surface.Boundary.HandleAreaBounds

open Purelib.Topology.Surface.Cut

open Purelib.Topology.Surface.Cut.Patch

open Purelib.Topology.Surface.Sewing

open Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces

open Purelib.Topology.Surface.Sewing.SewnPrimitiveRequests

@[expose] public section

/-!
# Requested local-area comparison on actual selected cut triangles

Only normalized corner increments enter the estimate. All inherited sewing
errors are retained, and the finite request pays the entire assembly count,
including both factors in the squared norm of the area sum. No sign or
positivity is assumed for an individual triangle's area.
-/

namespace Purelib.Topology.Surface.Sewing.SewnFaceAreaComparison

open Purelib.Topology.Polygon.Stokes (OrientedEdge OrientedTriangle PrimitivePoint edgeArea edgeListArea
  triangleWedgeArea)
open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib.Data.Gaussian.Basic.Canonical
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Algebra.FiniteSum.Rational.Squares (coordinateSum)
open Purelib.Polynomial.Geometry.Grid.CellBoundary (sumValues)
open Purelib.Topology.Surface.Sewing.PrimitiveSewing (PrimitiveValues)
open Purelib.Topology.Surface.Sewing.SewingTree (SewnPatch)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces (Coordinate FaceTrace FaceBank)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples (CachedSample)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveRequests (LocalAccuracy Request)
open Purelib.Topology.Surface.Cut.Patch (CutPatch)
open Purelib.Integration.Energy.Polygon (energyPrimitivePoint)

/-- Evaluate the Hermitian primitive wedge area of one original three-corner local reading. -/
def localTriangleArea (values : PrimitiveSewing.PrimitiveValues 3) : Gaussian.Basic.Canonical :=
  Stokes.triangleWedgeArea (Polygon.energyPrimitivePoint (values 0)) (Polygon.energyPrimitivePoint (values 1))
    (Polygon.energyPrimitivePoint (values 2))

/-- The original triangle boundary area is the pairing of its two first-corner increments. -/
private theorem triangle_area_increments {count : Nat} (values : Fin count → Stokes.PrimitivePoint)
    (triangle : Stokes.OrientedTriangle count) :
    Stokes.edgeListArea values triangle.boundary =
      Stokes.edgeArea ((Purelib.Topology.Polygon.Stokes.PrimitivePoint.sub (values triangle.second)) (values
        triangle.first))
        ((Purelib.Topology.Polygon.Stokes.PrimitivePoint.sub (values triangle.third)) (values triangle.first)) := by
  change Stokes.edgeArea (values triangle.first) (values triangle.second) +
    (Stokes.edgeArea (values triangle.second) (values triangle.third) +
      (Stokes.edgeArea (values triangle.third) (values triangle.first) + 0)) = _
  simp only [Stokes.edgeArea, PrimitivePoint.sub]
  ring1

variable {vertexCount faceCount : Nat} {faces : Fin faceCount → Stokes.OrientedTriangle vertexCount}
  {localValues : Fin faceCount → PrimitiveSewing.PrimitiveValues 3} {patch : SewingTree.SewnPatch faces}

/-- Bound the actual retained face-area discrepancy using normalized original corner increments and both inherited
sewing errors. -/
theorem FaceTrace.area_difference_bound (sample : SewnPrimitiveSamples.CachedSample patch localValues)
    (trace : SewnPrimitiveFaces.FaceTrace localValues sample.sewn.values) {magnitude error :
      SewnPrimitiveFaces.Coordinate}
    (nonnegative : 0 ≤ magnitude) (errorNonnegative : 0 ≤ error) (small : error ≤ 1)
    (bounded : ∀ index, Data.Gaussian.Norm.Basic.normSq (localValues trace.source index - localValues trace.source 0) ≤
      magnitude)
    (accurate : Data.Gaussian.Norm.Basic.normSq (trace.errors 1) ≤ error ∧ Data.Gaussian.Norm.Basic.normSq
      (trace.errors 2) ≤ error) :
    Data.Gaussian.Norm.Basic.normSq (Stokes.edgeListArea sample.energyValues trace.triangle.boundary -
      localTriangleArea (localValues trace.source)) ≤
      32 * (magnitude + 1) * error := by
  rw [triangle_area_increments]
  have conjugate (vertex) : PrimitivePoint.Conjugate
      (sample.energyValues vertex) := by rw [sample.energyValues_eq]; rfl
  have localConjugate (index) : PrimitivePoint.Conjugate
      (Polygon.energyPrimitivePoint (localValues trace.source index)) := rfl
  have firstBound := PrimitivePoint.bounded_of_conjugate
    (PrimitivePoint.sub_conjugate (localConjugate 1) (localConjugate 0)) (by
      have scalar := bounded 1
      simpa only [Gaussian.Norm.Basic.normSq_eq_canonical, PrimitivePoint.sub,
        Polygon.energyPrimitivePoint] using scalar)
  have lastBound := PrimitivePoint.bounded_of_conjugate
    (PrimitivePoint.sub_conjugate (localConjugate 2) (localConjugate 0)) (by
      have scalar := bounded 2
      simpa only [Gaussian.Norm.Basic.normSq_eq_canonical, PrimitivePoint.sub,
        Polygon.energyPrimitivePoint] using scalar)
  apply PrimitivePoint.area_difference_bound
    nonnegative errorNonnegative small firstBound lastBound
  · apply PrimitivePoint.bounded_of_conjugate
      (PrimitivePoint.sub_conjugate
        (PrimitivePoint.sub_conjugate (conjugate _) (conjugate _))
        (PrimitivePoint.sub_conjugate (localConjugate 1) (localConjugate 0)))
    simpa only [Gaussian.Norm.Basic.normSq_eq_canonical, PrimitivePoint.sub, sample.energyValues_eq,
      Polygon.energyPrimitivePoint, trace.errors_eq,
      show SewnPrimitiveFaces.corner trace.triangle 1 = trace.triangle.second from rfl] using accurate.1
  · apply PrimitivePoint.bounded_of_conjugate
      (PrimitivePoint.sub_conjugate
        (PrimitivePoint.sub_conjugate (conjugate _) (conjugate _))
        (PrimitivePoint.sub_conjugate (localConjugate 2) (localConjugate 0)))
    simpa only [Gaussian.Norm.Basic.normSq_eq_canonical, PrimitivePoint.sub, sample.energyValues_eq,
      Polygon.energyPrimitivePoint, trace.errors_eq,
      show SewnPrimitiveFaces.corner trace.triangle 2 = trace.triangle.third from rfl] using accurate.2

/-- One retained face trace's squared errors are bounded by the complete original trace-error sum. -/
private theorem trace_errors_le_sum {count : Nat} {values : PrimitiveSewing.PrimitiveValues count}
    (entries : List (SewnPrimitiveFaces.FaceTrace localValues values)) (trace : SewnPrimitiveFaces.FaceTrace localValues
      values) (member : trace ∈ entries) :
    trace.squaredErrors ≤ Purelib.Algebra.FiniteSum.Rational.Squares.coordinateSum (entries.map FaceTrace.squaredErrors)
      := by
  have nonnegative (items : List (SewnPrimitiveFaces.FaceTrace localValues values)) :
      0 ≤ Squares.coordinateSum (items.map FaceTrace.squaredErrors) := by
    induction items with
    | nil => exact le_rfl
    | cons first remaining ih =>
      exact add_nonneg (add_nonneg (Gaussian.Norm.Basic.normSq_nonneg _) (Gaussian.Norm.Basic.normSq_nonneg _)) ih
  induction entries with
  | nil => exact (List.not_mem_nil member).elim
  | cons first remaining ih =>
    rcases Membership.mem_cons.mp member with rfl | member
    · exact le_add_of_nonneg_right (nonnegative remaining)
    · exact (ih member).trans (le_add_of_nonneg_left (add_nonneg (Gaussian.Norm.Basic.normSq_nonneg _)
        (Gaussian.Norm.Basic.normSq_nonneg _)))

/-- Both retained corner errors are bounded by the original face bank's complete squared-error cache. -/
theorem FaceBank.trace_errors_le {indices : List (Fin faceCount)} {boundary : List (Stokes.OrientedEdge vertexCount)}
    {cut : Patch.CutPatch faces indices boundary} {values : PrimitiveSewing.PrimitiveValues cut.count}
    (bank : SewnPrimitiveFaces.FaceBank cut localValues values) (trace : SewnPrimitiveFaces.FaceTrace localValues
      values) (member : trace ∈ bank.entries) :
    Data.Gaussian.Norm.Basic.normSq (trace.errors 1) ≤ bank.squaredErrors ∧ Data.Gaussian.Norm.Basic.normSq
      (trace.errors 2) ≤ bank.squaredErrors := by
  have total := trace_errors_le_sum bank.entries trace member
  rw [← bank.squaredErrors_eq] at total
  exact ⟨(le_add_of_nonneg_right (Gaussian.Norm.Basic.normSq_nonneg _)).trans total,
    (le_add_of_nonneg_left (Gaussian.Norm.Basic.normSq_nonneg _)).trans total⟩

end Purelib.Topology.Surface.Sewing.SewnFaceAreaComparison

namespace Purelib.Integration.Surface.Sewn.Selection.Basic.SewnPrimitiveFaces.CachedSample.FaceSelection

open Purelib.Topology.Surface.Sewing.SewnFaceAreaComparison
open Purelib.Integration.Surface.Sewn.Selection.Basic.SewnPrimitiveFaces.CachedSample
open Purelib.Topology.Polygon.Stokes (OrientedTriangle edgeListArea)
open Purelib.Data.Gaussian.Basic (Canonical)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Polynomial.Geometry.Grid.CellBoundary (sumValues)
open Purelib.Topology.Surface.Sewing.PrimitiveSewing (PrimitiveValues)
open Purelib.Topology.Surface.Sewing.SewingTree (SewnPatch)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces (FaceTrace)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples (CachedSample)

variable {vertexCount faceCount : Nat} {faces : Fin faceCount → Stokes.OrientedTriangle vertexCount}
  {localValues : Fin faceCount → PrimitiveSewing.PrimitiveValues 3} {patch : SewingTree.SewnPatch faces}

variable {sample : SewnPrimitiveSamples.CachedSample patch localValues} {keep : Fin faceCount → Bool}

set_option genInjectivity false in
/-- The local area is computed from exactly the retained source occurrences, not from a projected vertex assignment or a
separately prepared surface. -/
structure LocalArea (selected : CachedSample.FaceSelection sample keep) where
  /-- Cached local area sum over the exact retained original selection. -/ value : Gaussian.Basic.Canonical
  /-- The local-area cache reads the source of every retained selected trace. -/ value_eq : value =
    CellBoundary.sumValues (fun trace : SewnPrimitiveFaces.FaceTrace localValues sample.sewn.values =>
    Topology.Surface.Sewing.SewnFaceAreaComparison.localTriangleArea (localValues trace.source)) selected.traces

constructive_injectivity LocalArea

/-- Cache the local triangle-area sum of the exact original selected face traces. -/
def LocalArea.build (selected : CachedSample.FaceSelection sample keep) : selected.LocalArea :=
  ⟨sumValues (fun trace : SewnPrimitiveFaces.FaceTrace localValues sample.sewn.values =>
    Topology.Surface.Sewing.SewnFaceAreaComparison.localTriangleArea (localValues trace.source)) selected.traces, rfl⟩

/-- The original selected area discrepancy is the full trace-bank sum of selected local differences and zero elsewhere.
-/
theorem LocalArea.difference (selected : CachedSample.FaceSelection sample keep) (area : selected.LocalArea) :
    selected.area - area.value = Data.Gaussian.Norm.Sum.Basic.gaussianSum (sample.faces.entries.map fun trace =>
      if keep trace.source then Stokes.edgeListArea sample.energyValues trace.triangle.boundary -
        Topology.Surface.Sewing.SewnFaceAreaComparison.localTriangleArea (localValues trace.source) else 0) := by
  rw [selected.area_readback, area.value_eq, selected.traces_eq,
    ← CellBoundary.sumValues_sub]
  induction sample.faces.entries with
  | nil => rfl
  | cons first remaining ih =>
    cases equal : keep first.source with
    | false =>
        rw [Filter.filter_cons_of_neg (predicate := fun trace => keep trace.source) (head := first) (tail := remaining)
          (by rw [equal]; exact Bool.noConfusion)]
        simp only [equal, if_neg (show (false : Bool) ≠ true from fun h => Bool.noConfusion h), List.map_cons,
          Data.Gaussian.Norm.Sum.Basic.gaussianSum, -eq_self, -iff_self]
        rw [Gaussian.Basic.zero_add]
        exact ih
    | true =>
        rw [Filter.filter_cons_of_pos (predicate := fun trace => keep trace.source) (head := first) (tail := remaining)
          equal]
        simp only [equal, if_pos (rfl : true = true), CellBoundary.sumValues, List.map_cons,
          Data.Gaussian.Norm.Sum.Basic.gaussianSum, -eq_self, -iff_self]
        exact congrArg (_ + ·) ih

end Purelib.Integration.Surface.Sewn.Selection.Basic.SewnPrimitiveFaces.CachedSample.FaceSelection

namespace Purelib.Topology.Surface.Sewing.SewnFaceAreaComparison

open Purelib.Topology.Polygon.Stokes (OrientedEdge OrientedTriangle PrimitivePoint edgeArea edgeListArea
  triangleWedgeArea)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Basic.Canonical
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Algebra.FiniteSum.Rational.Squares (coordinateSum)
open Purelib.Polynomial.Geometry.Grid.CellBoundary (sumValues)
open Purelib.Topology.Surface.Sewing.PrimitiveSewing (PrimitiveValues)
open Purelib.Topology.Surface.Sewing.SewingTree (SewnPatch)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces (Coordinate FaceTrace FaceBank)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples (CachedSample)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveRequests (LocalAccuracy Request)
open Purelib.Topology.Surface.Cut.Patch (CutPatch)
open Purelib.Integration.Energy.Polygon (energyPrimitivePoint)

variable {vertexCount faceCount : Nat} {faces : Fin faceCount → Stokes.OrientedTriangle vertexCount}
  {localValues : Fin faceCount → PrimitiveSewing.PrimitiveValues 3} {patch : SewingTree.SewnPatch faces}

variable {indices : List (Fin faceCount)} {boundary : List (Stokes.OrientedEdge vertexCount)}
  {cut : Patch.CutPatch faces indices boundary} {assembly : CutPatch.Assembly faces cut}

set_option genInjectivity false in
/-- A cached sewing request paying the area error for original selected face occurrences.

The local error is capped at one and weighted by magnitude and the complete assembly face count. -/
structure FaceAreaRequest (assembly : CutPatch.Assembly faces cut) (magnitude target : SewnPrimitiveFaces.Coordinate)
  where
  /-- The supplied normalized local primitive magnitude bound is nonnegative. -/ nonnegative : 0 ≤ magnitude
  /-- The requested total selected-area error target is strictly positive. -/ positive : 0 < target
  /-- Cached local error allowance used by the original dependent sewing request. -/ error :
    SewnPrimitiveFaces.Coordinate
  /-- The local error is capped at one and pays the full weighted original face-count allocation. -/ error_eq : error =
    min 1 (Aggregate.perTerm
    (Weighted.allowance target (32 * (magnitude + 1))) indices.length)
  /-- Retained sewing request for this exact original assembly and cached local error. -/ sewing :
    SewnPrimitiveRequests.Request assembly error

constructive_injectivity FaceAreaRequest

namespace FaceAreaRequest

variable {magnitude target : SewnPrimitiveFaces.Coordinate}

/-- Cache the weighted original face-area allowance and its dependent sewing request. -/
def build (assembly : CutPatch.Assembly faces cut) (magnitude target : SewnPrimitiveFaces.Coordinate)
    (nonnegative : 0 ≤ magnitude) (positive : 0 < target) : FaceAreaRequest assembly magnitude
      target :=
  let error := min 1 (Aggregate.perTerm
    (Weighted.allowance target (32 * (magnitude + 1))) indices.length)
  have weightNonnegative : 0 ≤ 32 * (magnitude + 1) := Fraction.Order.Arithmetic.mul_nonneg_direct
    (by decide +kernel) (add_nonneg nonnegative (by decide))
  have errorPositive : 0 < error := Fraction.Order.Basic.lt_min (by decide) (Aggregate.perTerm_positive
    (Weighted.allowance_positive positive weightNonnegative) _)
  ⟨nonnegative, positive, error, rfl, Request.build assembly error errorPositive⟩

/-- The retained sewing accuracy pays the complete selected original face-area discrepancy. -/
theorem accurate {patch : SewingTree.SewnPatch faces} (request : FaceAreaRequest patch.assembly
  magnitude target)
    (sample : SewnPrimitiveSamples.CachedSample patch localValues) {keep : Fin faceCount → Bool}
    (selected : CachedSample.FaceSelection sample keep)
    (area : selected.LocalArea)
    (bounded : ∀ source index, Data.Gaussian.Norm.Basic.normSq (localValues source index - localValues source 0) ≤
      magnitude)
    (locallyAccurate : SewnPrimitiveRequests.LocalAccuracy request.sewing.tolerance sample.sewn.readings) :
    Data.Gaussian.Norm.Basic.normSq (selected.area - area.value) < target := by
  have total : sample.faces.squaredErrors < request.error := by
    rw [sample.faces_eq]
    exact request.sewing.accurate sample.sewn.readings locallyAccurate
  have small : request.error ≤ 1 := request.error_eq ▸ Fraction.Order.Basic.min_le_left _ _
  have paid : request.error ≤ Aggregate.perTerm
      (Weighted.allowance target (32 * (magnitude + 1))) patch.faceIndices.length :=
    request.error_eq ▸ Fraction.Order.Basic.min_le_right _ _
  have weightNonnegative : 0 ≤ 32 * (magnitude + 1) := Fraction.Order.Arithmetic.mul_nonneg_direct
    (by decide +kernel) (add_nonneg request.nonnegative (by decide))
  have lengthEq : sample.faces.entries.length = patch.faceIndices.length :=
    (Map.length_map FaceTrace.source _).symm.trans (congrArg List.length sample.faces.sources_eq)
  rw [area.difference selected]
  apply Budget.Aggregate.normSq_sum_lt _ request.positive
  intro value member
  obtain ⟨trace, member, equal⟩ := Map.mem_map.mp member
  rw [← equal, Map.length_map, lengthEq]
  split
  · have errors := SewnFaceAreaComparison.FaceBank.trace_errors_le sample.faces trace member
    exact (SewnFaceAreaComparison.FaceTrace.area_difference_bound
      sample trace request.nonnegative request.sewing.target_positive.le small
      (bounded trace.source) ⟨errors.1.trans total.le, errors.2.trans total.le⟩).trans
      ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct paid weightNonnegative).trans
        (WeightedAggregateBudget.weighted_perTerm_le request.positive weightNonnegative _))
  · rw [Gaussian.Norm.Basic.normSq_zero]
    exact (Aggregate.perTerm_positive request.positive _).le

end FaceAreaRequest
end Purelib.Topology.Surface.Sewing.SewnFaceAreaComparison
