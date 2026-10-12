module
import Purelib.Data.Gaussian.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Data.List.OfFn.Basic

import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Boundary.HandleAreaBounds
import Purelib.Topology.Surface.Cut.PrimitiveJumps
public import Purelib.Topology.Surface.Sewing.Bilinear.Errors
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
public import Purelib.Topology.Surface.Sewing.SewnConjugateSamples
import Purelib.Topology.Surface.Sewing.Bilinear.Coverage
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

open Purelib.Topology.Surface.Sewing.SewnConjugateSamples

@[expose] public section

/-! Conjugation preserves the retained scalar seam-error bounds. Apply them
to conjugate/value wedge areas without rebuilding either sewn surface. -/
namespace Purelib.Topology.Surface.Sewing.SewnConjugateErrors

open Purelib.Topology.Surface.Sewing.SewingTree (SewnPatch)
open Purelib.Topology.Surface.Sewing.PrimitiveSewing (PrimitiveValues)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples (CachedSample)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces (Coordinate FaceTrace corner)
open Purelib.Topology.Surface.Sewing.SewnConjugateSamples (ConjugatePair)
open Purelib.Topology.Surface.Sewing.SewnConjugateSamples.ConjugatePair (conj_sub)
open Purelib.Topology.Surface.Sewing.Bilinear.Errors (traceAt traceAt_triangle traceAt_source)

open Purelib.Topology.Polygon.Stokes (OrientedTriangle PrimitivePoint triangleEdgeOccurrences triangleWedgeArea
  triangleWedgeSum triangleWedgeSum_eq_edgeListArea)

open _root_.Purelib.Data.Gaussian.Basic (conj)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Norm.Basic (normSq_conj)

variable {vertexCount faceCount : Nat} {faces : Fin faceCount → Stokes.OrientedTriangle vertexCount}
  {patch : SewingTree.SewnPatch faces} {leftLocal rightLocal : Fin faceCount → PrimitiveSewing.PrimitiveValues 3}
  {left : SewnPrimitiveSamples.CachedSample patch leftLocal} {right : SewnPrimitiveSamples.CachedSample patch
    rightLocal}

/-- Original scalar seam allowances bound the conjugate/value primitive increment discrepancy. -/
theorem increment_error (sample : SewnConjugateSamples.ConjugatePair left right)
    (first : SewnPrimitiveFaces.FaceTrace leftLocal left.sewn.values) (second : SewnPrimitiveFaces.FaceTrace rightLocal
      right.sewn.values)
    (triangleEq : first.triangle = second.triangle) (sourceEq : first.source = second.source)
    {error : SewnPrimitiveFaces.Coordinate} (leftBound : first.allowance ≤ error) (rightBound : second.allowance ≤
      error)
    (index : Fin 3) :
    (PrimitivePoint.Bounded ((PrimitivePoint.sub ((PrimitivePoint.sub (sample.values (SewnPrimitiveFaces.corner
      first.triangle index))) (sample.values first.triangle.first)))
      ⟨conj (leftLocal first.source index) - Data.Gaussian.Basic.conj (leftLocal first.source 0),
        rightLocal first.source index - rightLocal first.source 0⟩)) error := by
  constructor
  · rw [← Gaussian.Norm.Basic.normSq_eq_canonical]
    change Data.Gaussian.Norm.Basic.normSq (((sample.values (SewnPrimitiveFaces.corner first.triangle index)).left -
        (sample.values first.triangle.first).left) - _) ≤ error
    rw [sample.increment_left ⟨first.triangle.first, SewnPrimitiveFaces.corner first.triangle index⟩]
    rw [← ConjugatePair.conj_sub, ← ConjugatePair.conj_sub, Gaussian.Norm.Basic.normSq_conj]
    exact (first.increment_error_bound index).trans leftBound
  · rw [← Gaussian.Norm.Basic.normSq_eq_canonical]
    change Data.Gaussian.Norm.Basic.normSq (((sample.values (SewnPrimitiveFaces.corner first.triangle index)).right -
        (sample.values first.triangle.first).right) - _) ≤ error
    rw [sample.increment_right ⟨first.triangle.first, SewnPrimitiveFaces.corner first.triangle index⟩, triangleEq,
      sourceEq]
    exact (second.increment_error_bound index).trans rightBound

/-- Bound one original conjugate/value face-area error using both retained scalar allowances and the supplied magnitude.
-/
theorem triangle_area_error (sample : SewnConjugateSamples.ConjugatePair left right)
    (first : SewnPrimitiveFaces.FaceTrace leftLocal left.sewn.values) (second : SewnPrimitiveFaces.FaceTrace rightLocal
      right.sewn.values)
    (triangleEq : first.triangle = second.triangle) (sourceEq : first.source = second.source)
    {error magnitude : SewnPrimitiveFaces.Coordinate} (nonnegative : 0 ≤ magnitude) (errorNonnegative : 0 ≤ error)
    (small : error ≤ 1) (leftBound : first.allowance ≤ error) (rightBound : second.allowance ≤ error)
    (bounded : ∀ index : Fin 3,
      (PrimitivePoint.Bounded (⟨conj (leftLocal first.source index) - Data.Gaussian.Basic.conj (leftLocal
        first.source 0),
        rightLocal first.source index - rightLocal first.source 0⟩ : Stokes.PrimitivePoint)) magnitude) :
    Data.Gaussian.Norm.Basic.normSq (Stokes.triangleWedgeArea (sample.values first.triangle.first)
        (sample.values first.triangle.second) (sample.values first.triangle.third) -
      Stokes.triangleWedgeArea
        ⟨conj (leftLocal first.source 0), rightLocal first.source 0⟩
        ⟨conj (leftLocal first.source 1), rightLocal first.source 1⟩
        ⟨conj (leftLocal first.source 2), rightLocal first.source 2⟩) ≤ 32 * (magnitude + 1) * error := by
  have firstError := increment_error sample first second triangleEq sourceEq leftBound rightBound 1
  have lastError := increment_error sample first second triangleEq sourceEq leftBound rightBound 2
  have estimate := PrimitivePoint.area_difference_bound
    (first := ⟨conj (leftLocal first.source 1) - Data.Gaussian.Basic.conj (leftLocal first.source 0),
      rightLocal first.source 1 - rightLocal first.source 0⟩)
    (last := ⟨conj (leftLocal first.source 2) - Data.Gaussian.Basic.conj (leftLocal first.source 0),
      rightLocal first.source 2 - rightLocal first.source 0⟩)
    (changedFirst := (PrimitivePoint.sub (sample.values (SewnPrimitiveFaces.corner first.triangle 1))) (sample.values
      first.triangle.first))
    (changedLast := (PrimitivePoint.sub (sample.values (SewnPrimitiveFaces.corner first.triangle 2))) (sample.values
      first.triangle.first))
    nonnegative errorNonnegative small (bounded 1) (bounded 2) firstError lastError
  change Data.Gaussian.Norm.Basic.normSq (Stokes.triangleWedgeArea (sample.values first.triangle.first)
    (sample.values first.triangle.second) (sample.values first.triangle.third) -
    Stokes.triangleWedgeArea ⟨conj (leftLocal first.source 0), rightLocal first.source 0⟩
      ⟨conj (leftLocal first.source 1), rightLocal first.source 1⟩
      ⟨conj (leftLocal first.source 2), rightLocal first.source 2⟩) ≤ _ at estimate
  exact estimate

/-- Apply the conjugate/value area bound at the exact original cut-triangle position and face source. -/
theorem triangle_area_error_at (sample : SewnConjugateSamples.ConjugatePair left right) (position : Fin
  patch.cut.triangles.length)
    {error magnitude : SewnPrimitiveFaces.Coordinate} (nonnegative : 0 ≤ magnitude) (errorNonnegative : 0 ≤ error)
    (small : error ≤ 1) (leftBound : (Errors.traceAt left position).allowance ≤ error)
    (rightBound : (Errors.traceAt right position).allowance ≤ error)
    (bounded : ∀ index : Fin 3,
      (PrimitivePoint.Bounded (⟨conj (leftLocal (Errors.traceAt left position).source index) -
        Data.Gaussian.Basic.conj (leftLocal (Errors.traceAt left position).source 0),
        rightLocal (Errors.traceAt left position).source index - rightLocal (Errors.traceAt left position).source 0⟩ :
          Stokes.PrimitivePoint)) magnitude) :
    Data.Gaussian.Norm.Basic.normSq (Stokes.triangleWedgeArea (sample.values patch.cut.triangles[position.val].first)
        (sample.values patch.cut.triangles[position.val].second)
        (sample.values patch.cut.triangles[position.val].third) -
      Stokes.triangleWedgeArea
        ⟨conj (leftLocal (Errors.traceAt left position).source 0), rightLocal (Errors.traceAt left position).source 0⟩
        ⟨conj (leftLocal (Errors.traceAt left position).source 1), rightLocal (Errors.traceAt left position).source 1⟩
        ⟨conj (leftLocal (Errors.traceAt left position).source 2), rightLocal (Errors.traceAt left position).source 2⟩)
          ≤
          32 * (magnitude + 1) * error := by
  have estimate := triangle_area_error sample (Errors.traceAt left position) (Errors.traceAt right
    position)
    ((Errors.traceAt_triangle left position).trans (Errors.traceAt_triangle right position).symm)
    (Errors.traceAt_source left right position) nonnegative errorNonnegative small leftBound rightBound bounded
  rw [Errors.traceAt_triangle left position] at estimate
  exact estimate

/-- Bound the complete conjugate/value boundary-area error by every original face allowance and the full triangle count.
-/
theorem boundary_area_error (sample : SewnConjugateSamples.ConjugatePair left right)
    (errors : Fin patch.cut.triangles.length → SewnPrimitiveFaces.Coordinate) {magnitude :
      SewnPrimitiveFaces.Coordinate}
    (nonnegative : 0 ≤ magnitude) (errorNonnegative : ∀ position, 0 ≤ errors position)
    (small : ∀ position, errors position ≤ 1)
    (leftBound : ∀ position, (Errors.traceAt left position).allowance ≤ errors position)
    (rightBound : ∀ position, (Errors.traceAt right position).allowance ≤ errors position)
    (bounded : ∀ position (index : Fin 3),
      (PrimitivePoint.Bounded (⟨conj (leftLocal (Errors.traceAt left position).source index) -
        Data.Gaussian.Basic.conj (leftLocal (Errors.traceAt left position).source 0),
        rightLocal (Errors.traceAt left position).source index - rightLocal (Errors.traceAt left position).source 0⟩ :
          Stokes.PrimitivePoint)) magnitude) :
    Data.Gaussian.Norm.Basic.normSq (sample.boundaryArea - FiniteSum.Fin.sumFin (fun position =>
      Stokes.triangleWedgeArea
        ⟨conj (leftLocal (Errors.traceAt left position).source 0), rightLocal (Errors.traceAt left position).source 0⟩
        ⟨conj (leftLocal (Errors.traceAt left position).source 1), rightLocal (Errors.traceAt left position).source 1⟩
        ⟨conj (leftLocal (Errors.traceAt left position).source 2), rightLocal (Errors.traceAt left position).source 2⟩))
          ≤
      (patch.cut.triangles.length : SewnPrimitiveFaces.Coordinate) *
        FiniteSum.Fin.sumFin (fun position => 32 * (magnitude + 1) * errors position) := by
  let actual (position : Fin patch.cut.triangles.length) :=
    Stokes.triangleWedgeArea (sample.values patch.cut.triangles[position.val].first)
      (sample.values patch.cut.triangles[position.val].second)
      (sample.values patch.cut.triangles[position.val].third)
  let original (position : Fin patch.cut.triangles.length) :=
    Stokes.triangleWedgeArea
      ⟨conj (leftLocal (Errors.traceAt left position).source 0), rightLocal (Errors.traceAt left position).source 0⟩
      ⟨conj (leftLocal (Errors.traceAt left position).source 1), rightLocal (Errors.traceAt left position).source 1⟩
      ⟨conj (leftLocal (Errors.traceAt left position).source 2), rightLocal (Errors.traceAt left position).source 2⟩
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

end Purelib.Topology.Surface.Sewing.SewnConjugateErrors
