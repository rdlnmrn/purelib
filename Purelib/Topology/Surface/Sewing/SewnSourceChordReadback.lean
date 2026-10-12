module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic

import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Boundary.HandleAreaBounds
import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Purelib.Topology.Surface.Sewing.Bilinear.Samples
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Surface.Sewing.SewnPrimitiveBoundary
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
public import Purelib.Topology.Surface.Sewing.Bilinear.Errors
public import Purelib.Topology.Surface.Sewing.SewnPrimitivePaths
import Purelib.Data.Rat.Fraction.Field
import Mathlib.Data.Nat.Cast.Defs
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Data.Int.Cast.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Data.Nat.Init
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Vector.Basic
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Data.Rat.Fraction
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

open Purelib.Data

open Purelib.Data.Gaussian.Norm.Basic

open Purelib.Riemann.Readings.PrimitiveAreaBounds

open Purelib.Topology.Polygon

open Purelib.Topology.Polygon.Stokes

open Purelib.Topology.Surface.Boundary.HandleAreaBounds

open Purelib.Topology.Surface.Sewing

open Purelib.Topology.Surface.Sewing.Bilinear

open Purelib.Topology.Surface.Sewing.SewnPrimitiveBoundary.FaceBank

open Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts.FaceBank

open Purelib.Topology.Surface.Sewing.SewnPrimitivePaths

@[expose] public section

/-! Source-chord comparison retains the actual sewn origin contribution.
The inherited face allowances pay both endpoint errors. -/
namespace Purelib.Topology.Surface.Sewing.SewnSourceChordReadback

open Purelib.Topology.Polygon.Stokes (OrientedEdge OrientedTriangle PrimitivePoint edgeArea edgeListArea)
open Purelib.Data.Gaussian.Basic (Canonical)

open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Topology.Surface.Sewing.SewingTree (SewnPatch)
open Purelib.Topology.Surface.Sewing.PrimitiveSewing (PrimitiveValues)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples (CachedSample)
open _root_.Purelib.Topology.Surface.Sewing.Bilinear renaming Samples -> Bilinear
open Purelib.Topology.Surface.Sewing.SewnPrimitivePaths.SewnPrimitiveFaces (PathSources OrientedOwner)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces (Coordinate FaceTrace corner)
open Purelib.Riemann.Readings.PrimitiveAreaBounds.PrimitivePoint (Bounded)
open Purelib.Topology.Surface.Boundary.HandleAreaBounds.PrimitivePoint (area_difference_bound)
open Purelib.Topology.Surface.Sewing.Bilinear.Errors (traceAt traceAt_triangle traceAt_source)

variable {vertexCount faceCount : Nat} {faces : Fin faceCount → Stokes.OrientedTriangle vertexCount}
  {patch : SewingTree.SewnPatch faces} {leftLocal rightLocal : Fin faceCount → PrimitiveSewing.PrimitiveValues 3}
  {left : SewnPrimitiveSamples.CachedSample patch leftLocal} {right : SewnPrimitiveSamples.CachedSample patch
    rightLocal}

/-- Subtracting the origin contribution from an edge area gives the area of its centered endpoints. -/
private theorem origin_readback (first last origin : Stokes.PrimitivePoint) :
    Stokes.edgeArea first last - Stokes.edgeArea origin ((PrimitivePoint.sub last) first) =
      Stokes.edgeArea ((PrimitivePoint.sub first) origin) ((PrimitivePoint.sub last) origin) := by
  simp only [Stokes.edgeArea, PrimitivePoint.sub]
  ring1

/-- Centering both sewn scalar banks changes the edge area and its origin contribution by the same amount. No endpoint
closure is needed. -/
theorem origin_area_eq_raw (sample : Bilinear.Samples left right) (start finish origin : Fin patch.cut.count) :
    Stokes.edgeArea (sample.values start) (sample.values finish) -
      Stokes.edgeArea (sample.values origin) ((PrimitivePoint.sub (sample.values finish)) (sample.values start)) =
    Stokes.edgeArea ⟨left.sewn.values start, right.sewn.values start⟩ ⟨left.sewn.values finish, right.sewn.values
      finish⟩ -
      Stokes.edgeArea ⟨left.sewn.values origin, right.sewn.values origin⟩
        (⟨left.sewn.values finish - left.sewn.values start, right.sewn.values finish - right.sewn.values start⟩ :
          Stokes.PrimitivePoint) := by
  simp only [sample.values_eq, Stokes.edgeArea, PrimitivePoint.sub]
  ring1

/-- The full retained occurrence list has the same corrected area before and after centering; every original owner
contributes its own origin term. -/
theorem path_origin_area_eq_raw (sample : Bilinear.Samples left right)
    {edges : List (Stokes.OrientedEdge patch.cut.count)} (sources : SewnPrimitiveFaces.PathSources patch.cut edges) :
    let raw := fun vertex => (⟨left.sewn.values vertex, right.sewn.values vertex⟩ : Stokes.PrimitivePoint)
    Stokes.edgeListArea sample.values edges - Data.Gaussian.Norm.Sum.Basic.gaussianSum
      (sources.entries.map (fun route => Stokes.edgeArea (sample.values
        patch.cut.triangles[route.owner.position.val].first)
        ((PrimitivePoint.sub (sample.values route.cutEdge.finish)) (sample.values route.cutEdge.start)))) =
    Stokes.edgeListArea raw edges - Data.Gaussian.Norm.Sum.Basic.gaussianSum
      (sources.entries.map (fun route => Stokes.edgeArea (raw patch.cut.triangles[route.owner.position.val].first)
        ((PrimitivePoint.sub (raw route.cutEdge.finish)) (raw route.cutEdge.start)))) := by
  intro raw
  rw [← congrArg (Stokes.edgeListArea sample.values) sources.edges_eq, ← congrArg (Stokes.edgeListArea raw)
    sources.edges_eq]
  induction sources.entries with
  | nil => rfl
  | cons route tail ih =>
    simp only [List.map_cons, Stokes.edgeListArea, Data.Gaussian.Norm.Sum.Basic.gaussianSum]
    have split (a b c d : Gaussian.Basic.Canonical) : a + b - (c + d) = (a - c) + (b - d) := by ring1
    rw [split, split, ih]
    exact congrArg (· + _) (origin_area_eq_raw sample route.cutEdge.start route.cutEdge.finish
      patch.cut.triangles[route.owner.position.val].first)

/-- The raw sewn edge is compared with its original centered source chord. The anchor contribution is explicit, even
when the cut edge is not closed. -/
theorem source_chord_error (sample : Bilinear.Samples left right)
    (first : SewnPrimitiveFaces.FaceTrace leftLocal left.sewn.values) (second : SewnPrimitiveFaces.FaceTrace rightLocal
      right.sewn.values)
    (triangleEq : first.triangle = second.triangle) (sourceEq : first.source = second.source)
    (start finish : Fin 3)
    {error magnitude : SewnPrimitiveFaces.Coordinate} (nonnegative : 0 ≤ magnitude) (errorNonnegative : 0 ≤ error)
    (small : error ≤ 1) (leftBound : first.allowance ≤ error) (rightBound : second.allowance ≤ error)
    (bounded : ∀ index : Fin 3,
      (PrimitivePoint.Bounded (⟨leftLocal first.source index - leftLocal first.source 0,
        rightLocal first.source index - rightLocal first.source 0⟩ : Stokes.PrimitivePoint)) magnitude) :
    Data.Gaussian.Norm.Basic.normSq (Stokes.edgeArea (sample.values (SewnPrimitiveFaces.corner first.triangle start))
      (sample.values
      (SewnPrimitiveFaces.corner first.triangle finish)) -
      Stokes.edgeArea (sample.values first.triangle.first)
        ((PrimitivePoint.sub (sample.values (SewnPrimitiveFaces.corner first.triangle finish))) (sample.values
          (SewnPrimitiveFaces.corner first.triangle start))) -
      Stokes.edgeArea
        ⟨leftLocal first.source start - leftLocal first.source 0,
          rightLocal first.source start - rightLocal first.source 0⟩
        ⟨leftLocal first.source finish - leftLocal first.source 0,
          rightLocal first.source finish - rightLocal first.source 0⟩) ≤ 32 * (magnitude + 1) * error := by
  rw [origin_readback]
  exact PrimitivePoint.area_difference_bound nonnegative errorNonnegative small (bounded start) (bounded finish)
    (Errors.increment_error sample first second triangleEq sourceEq leftBound rightBound start)
    (Errors.increment_error sample first second triangleEq sourceEq leftBound rightBound finish)

/-- Both cached traces are selected at the actual owner position. -/
theorem source_chord_error_at (sample : Bilinear.Samples left right) (position : Fin patch.cut.triangles.length)
    (start finish : Fin 3)
    {error magnitude : SewnPrimitiveFaces.Coordinate} (nonnegative : 0 ≤ magnitude) (errorNonnegative : 0 ≤ error)
    (small : error ≤ 1) (leftBound : (Errors.traceAt left position).allowance ≤ error)
    (rightBound : (Errors.traceAt right position).allowance ≤ error)
    (bounded : ∀ index : Fin 3,
      (PrimitivePoint.Bounded (⟨leftLocal (Errors.traceAt left position).source index - leftLocal (Errors.traceAt left
        position).source 0,
        rightLocal (Errors.traceAt left position).source index - rightLocal (Errors.traceAt left position).source 0⟩ :
          Stokes.PrimitivePoint)) magnitude) :
    Data.Gaussian.Norm.Basic.normSq (Stokes.edgeArea (sample.values (SewnPrimitiveFaces.corner
      patch.cut.triangles[position.val] start))
        (sample.values (SewnPrimitiveFaces.corner patch.cut.triangles[position.val] finish)) -
      Stokes.edgeArea (sample.values patch.cut.triangles[position.val].first)
        ((PrimitivePoint.sub (sample.values (SewnPrimitiveFaces.corner patch.cut.triangles[position.val] finish)))
          (sample.values (SewnPrimitiveFaces.corner patch.cut.triangles[position.val] start))) -
      Stokes.edgeArea
        ⟨leftLocal (Errors.traceAt left position).source start - leftLocal (Errors.traceAt left position).source 0,
          rightLocal (Errors.traceAt left position).source start - rightLocal (Errors.traceAt left position).source 0⟩
        ⟨leftLocal (Errors.traceAt left position).source finish - leftLocal (Errors.traceAt left position).source 0,
          rightLocal (Errors.traceAt left position).source finish - rightLocal (Errors.traceAt left position).source 0⟩)
            ≤
      32 * (magnitude + 1) * error := by
  have estimate := source_chord_error sample (Errors.traceAt left position) (Errors.traceAt
    right position)
    ((Errors.traceAt_triangle left position).trans (Errors.traceAt_triangle right position).symm)
    (Errors.traceAt_source left right position) start finish nonnegative errorNonnegative small leftBound rightBound
      bounded
  rw [Errors.traceAt_triangle left position] at estimate
  exact estimate

/-- The trace selected at an oriented owner's retained position has that owner's original source face. -/
private theorem owner_source (surface : SewnPrimitiveSamples.CachedSample patch leftLocal) (route :
  SewnPrimitiveFaces.OrientedOwner patch.cut) :
    (Errors.traceAt surface route.owner.position).source = route.sourceEdge.source := by
  have equal := EdgeReading.source_eq (EdgeReading.build surface.faces route.owner)
  cases route with
  | mk edge owner reversed => cases reversed <;> exact equal

/-- Forward and reversed cut owners consume their original source corners and the same cached face allowances. The sewn
origin term is not discarded. -/
theorem owner_source_chord_error (sample : Bilinear.Samples left right) (route : SewnPrimitiveFaces.OrientedOwner
  patch.cut)
    {error magnitude : SewnPrimitiveFaces.Coordinate} (nonnegative : 0 ≤ magnitude) (errorNonnegative : 0 ≤ error)
    (small : error ≤ 1) (leftBound : (Errors.traceAt left route.owner.position).allowance ≤ error)
    (rightBound : (Errors.traceAt right route.owner.position).allowance ≤ error)
    (bounded : ∀ index : Fin 3,
      (PrimitivePoint.Bounded (⟨leftLocal route.sourceEdge.source index - leftLocal route.sourceEdge.source 0,
        rightLocal route.sourceEdge.source index - rightLocal route.sourceEdge.source 0⟩ : Stokes.PrimitivePoint))
          magnitude) :
    Data.Gaussian.Norm.Basic.normSq (Stokes.edgeArea (sample.values route.cutEdge.start) (sample.values
      route.cutEdge.finish) -
      Stokes.edgeArea (sample.values patch.cut.triangles[route.owner.position.val].first)
        ((PrimitivePoint.sub (sample.values route.cutEdge.finish)) (sample.values route.cutEdge.start)) -
      Stokes.edgeArea
        ⟨leftLocal route.sourceEdge.source route.sourceEdge.first - leftLocal route.sourceEdge.source 0,
          rightLocal route.sourceEdge.source route.sourceEdge.first - rightLocal route.sourceEdge.source 0⟩
        ⟨leftLocal route.sourceEdge.source route.sourceEdge.last - leftLocal route.sourceEdge.source 0,
          rightLocal route.sourceEdge.source route.sourceEdge.last - rightLocal route.sourceEdge.source 0⟩) ≤
      32 * (magnitude + 1) * error := by
  have sourceEq := owner_source left route
  have sourceBound : ∀ index : Fin 3,
      (PrimitivePoint.Bounded (⟨leftLocal (Errors.traceAt left route.owner.position).source index - leftLocal
        (Errors.traceAt left route.owner.position).source 0,
        rightLocal (Errors.traceAt left route.owner.position).source index - rightLocal (Errors.traceAt left
          route.owner.position).source 0⟩ :
          Stokes.PrimitivePoint)) magnitude := by
    rw [sourceEq]
    exact bounded
  cases route with
  | mk edge owner reversed =>
    cases reversed with
    | false =>
      have estimate := source_chord_error_at sample owner.position owner.first owner.last
        nonnegative errorNonnegative small leftBound rightBound sourceBound
      rw [owner.start_eq, owner.finish_eq, sourceEq] at estimate
      exact estimate
    | true =>
      have estimate := source_chord_error_at sample owner.position owner.last owner.first
        nonnegative errorNonnegative small leftBound rightBound sourceBound
      rw [owner.start_eq, owner.finish_eq, sourceEq] at estimate
      exact estimate

end Purelib.Topology.Surface.Sewing.SewnSourceChordReadback
