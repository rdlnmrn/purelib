module
import Purelib.Data.List.Map
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Data.List.OfFn.Basic

public import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingTree
public import Purelib.Topology.Surface.Sewing.SewnPrimitiveBoundary
import Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
public import Purelib.Topology.Surface.Sewing.Bilinear.Samples
import Purelib.Topology.Surface.Boundary.HandleAreaBounds
import Purelib.Data.Gaussian.Basic
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Field
import Mathlib.Data.Nat.Cast.Defs
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Algebra.Ring.Defs
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Data.Rat.Fraction
import Purelib.Data.Vector.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Data.Int.Cast.Defs
import Purelib.Tactic.QuotientFreeOmega

/-! Transfer the retained scalar seam-error certificates to the two
components of the actual sewn bilinear readings. -/

namespace Purelib.Topology.Surface.Sewing.Bilinear.Errors

open Purelib.Algebra
open Purelib.Data
open Purelib.Data.Gaussian.Norm.Basic
open Purelib.Data.Gaussian.Norm.Sum
open Purelib.Data.List
open Purelib.Riemann.Readings.PrimitiveAreaBounds
open Purelib.Topology.Polygon
open Purelib.Topology.Polygon.Stokes
open Purelib.Topology.Surface.Boundary.HandleAreaBounds
open Purelib.Topology.Surface.Sewing
open Purelib.Topology.Surface.Sewing.Bilinear
open Purelib.Topology.Surface.Sewing.SewnPrimitiveBoundary

public section

open Purelib.Topology.Polygon.Stokes (OrientedTriangle PrimitivePoint triangleEdgeOccurrences triangleWedgeArea
  triangleWedgeSum triangleWedgeSum_eq_edgeListArea)

open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Topology.Surface.Sewing.SewingTree (SewnPatch)
open Purelib.Topology.Surface.Sewing.PrimitiveSewing (PrimitiveValues)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples (CachedSample)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces (FaceTrace Coordinate)
open _root_.Purelib.Topology.Surface.Sewing.Bilinear renaming Samples -> Bilinear
open Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces (corner)

variable {vertexCount faceCount : Nat} {faces : Fin faceCount → Stokes.OrientedTriangle vertexCount}
  {patch : SewingTree.SewnPatch faces} {leftLocal rightLocal : Fin faceCount → PrimitiveSewing.PrimitiveValues 3}
  {left : SewnPrimitiveSamples.CachedSample patch leftLocal} {right : SewnPrimitiveSamples.CachedSample patch
    rightLocal}

/-- Read the retained face trace at a bounded original cut-triangle position. -/
@[expose] def traceAt (surface : SewnPrimitiveSamples.CachedSample patch leftLocal) (position : Fin
  patch.cut.triangles.length) :
    SewnPrimitiveFaces.FaceTrace leftLocal surface.sewn.values :=
  surface.faces.entries[position.val]'(by rw [FaceBank.entries_length surface.faces]; exact position.isLt)

/-- The selected cached face trace has exactly the original cut triangle at that position. -/
theorem traceAt_triangle (surface : SewnPrimitiveSamples.CachedSample patch leftLocal) (position : Fin
  patch.cut.triangles.length) :
    (traceAt surface position).triangle = patch.cut.triangles[position.val] :=
  FaceBank.triangle_at surface.faces position.val _

/-- Two samples on the same retained assembly use the same original face source at each position.

The common source list determines the source at the same retained cut-triangle position in both caches. -/
theorem traceAt_source (left : SewnPrimitiveSamples.CachedSample patch leftLocal) (right :
  SewnPrimitiveSamples.CachedSample patch rightLocal)
    (position : Fin patch.cut.triangles.length) :
    (traceAt left position).source = (traceAt right position).source := by
  have equal := left.faces.sources_eq.trans right.faces.sources_eq.symm
  have atPosition := List.getElem_of_eq equal (i := position.val) (by
    rw [Map.length_map, FaceBank.entries_length left.faces]
    exact position.isLt)
  rw [Map.getElem_map, Map.getElem_map] at atPosition
  exact atPosition

/-- The two retained scalar seam allowances jointly bound each bilinear primitive increment error. -/
theorem increment_error (sample : Samples left right)
    (first : SewnPrimitiveFaces.FaceTrace leftLocal left.sewn.values) (second : SewnPrimitiveFaces.FaceTrace rightLocal
      right.sewn.values)
    (triangleEq : first.triangle = second.triangle) (sourceEq : first.source = second.source)
    {error : SewnPrimitiveFaces.Coordinate} (leftBound : first.allowance ≤ error) (rightBound : second.allowance ≤
      error)
    (index : Fin 3) :
    (PrimitivePoint.Bounded ((PrimitivePoint.sub ((PrimitivePoint.sub (sample.values (SewnPrimitiveFaces.corner
      first.triangle index))) (sample.values first.triangle.first)))
      ⟨leftLocal first.source index - leftLocal first.source 0,
        rightLocal first.source index - rightLocal first.source 0⟩)) error := by
  constructor
  · rw [← Gaussian.Norm.Basic.normSq_eq_canonical]
    change Data.Gaussian.Norm.Basic.normSq (((sample.values (SewnPrimitiveFaces.corner first.triangle index)).left -
        (sample.values first.triangle.first).left) - _) ≤ error
    rw [sample.increment_left ⟨first.triangle.first, SewnPrimitiveFaces.corner first.triangle index⟩]
    exact (first.increment_error_bound index).trans leftBound
  · rw [← Gaussian.Norm.Basic.normSq_eq_canonical]
    change Data.Gaussian.Norm.Basic.normSq (((sample.values (SewnPrimitiveFaces.corner first.triangle index)).right -
        (sample.values first.triangle.first).right) - _) ≤ error
    rw [sample.increment_right ⟨first.triangle.first, SewnPrimitiveFaces.corner first.triangle index⟩, triangleEq,
      sourceEq]
    exact (second.increment_error_bound index).trans rightBound

/-- Bound one original bilinear face-area error by its retained scalar allowances and magnitude bound.

The common local error is nonnegative and at most one; the complete factor is thirty-two times magnitude plus one. -/
theorem triangle_area_error (sample : Samples left right)
    (first : SewnPrimitiveFaces.FaceTrace leftLocal left.sewn.values) (second : SewnPrimitiveFaces.FaceTrace rightLocal
      right.sewn.values)
    (triangleEq : first.triangle = second.triangle) (sourceEq : first.source = second.source)
    {error magnitude : SewnPrimitiveFaces.Coordinate} (nonnegative : 0 ≤ magnitude) (errorNonnegative : 0 ≤ error)
    (small : error ≤ 1) (leftBound : first.allowance ≤ error) (rightBound : second.allowance ≤ error)
    (bounded : ∀ index : Fin 3,
      (PrimitivePoint.Bounded (⟨leftLocal first.source index - leftLocal first.source 0,
        rightLocal first.source index - rightLocal first.source 0⟩ : Stokes.PrimitivePoint)) magnitude) :
    Data.Gaussian.Norm.Basic.normSq (Stokes.triangleWedgeArea (sample.values first.triangle.first)
        (sample.values first.triangle.second) (sample.values first.triangle.third) -
      Stokes.triangleWedgeArea
        ⟨leftLocal first.source 0, rightLocal first.source 0⟩
        ⟨leftLocal first.source 1, rightLocal first.source 1⟩
        ⟨leftLocal first.source 2, rightLocal first.source 2⟩) ≤ 32 * (magnitude + 1) * error := by
  have firstError := increment_error sample first second triangleEq sourceEq leftBound rightBound 1
  have lastError := increment_error sample first second triangleEq sourceEq leftBound rightBound 2
  have estimate := PrimitivePoint.area_difference_bound
    (first := ⟨leftLocal first.source 1 - leftLocal first.source 0,
      rightLocal first.source 1 - rightLocal first.source 0⟩)
    (last := ⟨leftLocal first.source 2 - leftLocal first.source 0,
      rightLocal first.source 2 - rightLocal first.source 0⟩)
    (changedFirst := (PrimitivePoint.sub (sample.values (SewnPrimitiveFaces.corner first.triangle 1))) (sample.values
      first.triangle.first))
    (changedLast := (PrimitivePoint.sub (sample.values (SewnPrimitiveFaces.corner first.triangle 2))) (sample.values
      first.triangle.first))
    nonnegative errorNonnegative small (bounded 1) (bounded 2) firstError lastError
  change Data.Gaussian.Norm.Basic.normSq (Stokes.triangleWedgeArea (sample.values first.triangle.first)
    (sample.values first.triangle.second) (sample.values first.triangle.third) -
    Stokes.triangleWedgeArea ⟨leftLocal first.source 0, rightLocal first.source 0⟩
      ⟨leftLocal first.source 1, rightLocal first.source 1⟩
      ⟨leftLocal first.source 2, rightLocal first.source 2⟩) ≤ _ at estimate
  exact estimate

/-- Apply the bilinear area error bound at an exact retained cut-triangle position and source. -/
theorem triangle_area_error_at (sample : Samples left right) (position : Fin patch.cut.triangles.length)
    {error magnitude : SewnPrimitiveFaces.Coordinate} (nonnegative : 0 ≤ magnitude) (errorNonnegative : 0 ≤ error)
    (small : error ≤ 1) (leftBound : (traceAt left position).allowance ≤ error)
    (rightBound : (traceAt right position).allowance ≤ error)
    (bounded : ∀ index : Fin 3,
      (PrimitivePoint.Bounded (⟨leftLocal (traceAt left position).source index - leftLocal (traceAt left
        position).source 0,
        rightLocal (traceAt left position).source index - rightLocal (traceAt left position).source 0⟩ :
          Stokes.PrimitivePoint)) magnitude) :
    Data.Gaussian.Norm.Basic.normSq (Stokes.triangleWedgeArea (sample.values patch.cut.triangles[position.val].first)
        (sample.values patch.cut.triangles[position.val].second)
        (sample.values patch.cut.triangles[position.val].third) -
      Stokes.triangleWedgeArea
        ⟨leftLocal (traceAt left position).source 0, rightLocal (traceAt left position).source 0⟩
        ⟨leftLocal (traceAt left position).source 1, rightLocal (traceAt left position).source 1⟩
        ⟨leftLocal (traceAt left position).source 2, rightLocal (traceAt left position).source 2⟩) ≤
          32 * (magnitude + 1) * error := by
  have estimate := triangle_area_error sample (traceAt left position) (traceAt right position)
    ((traceAt_triangle left position).trans (traceAt_triangle right position).symm)
    (traceAt_source left right position) nonnegative errorNonnegative small leftBound rightBound bounded
  rw [traceAt_triangle left position] at estimate
  exact estimate

/-- Bound the complete sewn boundary-area error using every retained original face allowance.

The finite sum includes the full triangle count factor and both scalar sample bounds. -/
theorem boundary_area_error (sample : Samples left right)
    (errors : Fin patch.cut.triangles.length → SewnPrimitiveFaces.Coordinate) {magnitude :
      SewnPrimitiveFaces.Coordinate}
    (nonnegative : 0 ≤ magnitude) (errorNonnegative : ∀ position, 0 ≤ errors position)
    (small : ∀ position, errors position ≤ 1)
    (leftBound : ∀ position, (traceAt left position).allowance ≤ errors position)
    (rightBound : ∀ position, (traceAt right position).allowance ≤ errors position)
    (bounded : ∀ position (index : Fin 3),
      (PrimitivePoint.Bounded (⟨leftLocal (traceAt left position).source index - leftLocal (traceAt left
        position).source 0,
        rightLocal (traceAt left position).source index - rightLocal (traceAt left position).source 0⟩ :
          Stokes.PrimitivePoint)) magnitude) :
    Data.Gaussian.Norm.Basic.normSq (sample.boundaryArea - FiniteSum.Fin.sumFin (fun position =>
      Stokes.triangleWedgeArea
        ⟨leftLocal (traceAt left position).source 0, rightLocal (traceAt left position).source 0⟩
        ⟨leftLocal (traceAt left position).source 1, rightLocal (traceAt left position).source 1⟩
        ⟨leftLocal (traceAt left position).source 2, rightLocal (traceAt left position).source 2⟩)) ≤
      (patch.cut.triangles.length : SewnPrimitiveFaces.Coordinate) *
        FiniteSum.Fin.sumFin (fun position => 32 * (magnitude + 1) * errors position) := by
  let actual (position : Fin patch.cut.triangles.length) :=
    Stokes.triangleWedgeArea (sample.values patch.cut.triangles[position.val].first)
      (sample.values patch.cut.triangles[position.val].second)
      (sample.values patch.cut.triangles[position.val].third)
  let original (position : Fin patch.cut.triangles.length) :=
    Stokes.triangleWedgeArea
      ⟨leftLocal (traceAt left position).source 0, rightLocal (traceAt left position).source 0⟩
      ⟨leftLocal (traceAt left position).source 1, rightLocal (traceAt left position).source 1⟩
      ⟨leftLocal (traceAt left position).source 2, rightLocal (traceAt left position).source 2⟩
  have areaEq : FiniteSum.Fin.sumFin actual = sample.boundaryArea := by
    change Stokes.triangleWedgeSum sample.values (fun position : Fin patch.cut.triangles.length =>
      patch.cut.triangles[position.val]) = _
    rw [Stokes.triangleWedgeSum_eq_edgeListArea, Stokes.triangleEdgeOccurrences, OfFn.Basic.ofFn_getElem]
    exact sample.surface_eq_boundary
  have estimate := Indexed.normSq_sumFin_le_count_mul_sumFin
    (fun position => actual position - original position)
    (fun position => 32 * (magnitude + 1) * errors position)
    (fun position => triangle_area_error_at sample position nonnegative (errorNonnegative position)
      (small position) (leftBound position) (rightBound position) (bounded position))
  rw [FiniteSum.Fin.sumFin_sub, areaEq] at estimate
  exact estimate

end

end Purelib.Topology.Surface.Sewing.Bilinear.Errors
