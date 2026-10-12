module
import Purelib.Data.List.Flatten
import Purelib.Topology.Surface.Cut.PrimitiveJumps

import Purelib.Integration.Path.CenteredPrimitiveArea
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
public import Purelib.Topology.Surface.Sewing.Bilinear.Samples
import Purelib.Tactic.Ring

public section

/-! Centering preserves the paired area on the actual closed cut boundary. -/

namespace Purelib.Riemann.Periods.BilinearBoundaryReadback

open Purelib.Topology.Polygon.Stokes (OrientedEdge OrientedTriangle PrimitivePoint edgeArea edgeListArea
  edgeListArea_append)
open Purelib.Topology.Surface.Sewing.SewingTree (SewnPatch)
open Purelib.Topology.Surface.Sewing.PrimitiveSewing (PrimitiveValues)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples (CachedSample)
open _root_.Purelib.Topology.Surface.Sewing.Bilinear renaming Samples -> Bilinear

variable {vertexCount faceCount : Nat} {faces : Fin faceCount → OrientedTriangle vertexCount}
  {patch : SewnPatch faces} {leftLocal rightLocal : Fin faceCount →
    PrimitiveValues 3}
  {left : CachedSample patch leftLocal} {right :
    CachedSample patch rightLocal}

open Purelib.Integration in
open Purelib.Topology in
/-- Centering the paired sewn values preserves the area of the exact closed cut boundary.

Both scalar samples use the same sewn patch, and the retained centering equation subtracts their values at its anchor.
-/
theorem boundary_eq_raw (sample : Topology.Surface.Sewing.Bilinear.Samples left right) :
    sample.boundaryArea = edgeListArea (fun vertex =>
      (⟨left.sewn.values vertex, right.sewn.values vertex⟩ : PrimitivePoint)) patch.cut.boundary := by
  let raw := fun vertex => (⟨left.sewn.values vertex, right.sewn.values vertex⟩ : PrimitivePoint)
  have values : ∀ vertex, sample.values vertex = (Polygon.Stokes.PrimitivePoint.sub (raw vertex)) (raw patch.cut.anchor)
    := sample.values_eq
  have equal : ∀ edges : List (OrientedEdge patch.cut.count), edgeListArea sample.values edges =
      edgeListArea (fun vertex => (Polygon.Stokes.PrimitivePoint.sub (raw vertex)) (raw patch.cut.anchor)) edges := by
    intro edges
    induction edges with
    | nil => rfl
    | cons edge tail ih =>
        simp only [-eq_self, -iff_self, edgeListArea, values, ih]
        rfl
  rw [sample.boundaryArea_eq, equal, Path.CenteredPrimitiveArea.edgeListArea_sub_constant_closed raw _ patch.cut.closed]

open Purelib.Topology in
/-- Centering preserves paired area for every retained list of cut triangles.

Each triangle's boundary area is preserved separately, so the result applies to any selected ordered triangle list. -/
theorem triangles_eq_raw (sample : Topology.Surface.Sewing.Bilinear.Samples left right)
    (triangles : List (OrientedTriangle patch.cut.count)) :
    edgeListArea sample.values (triangles.flatMap OrientedTriangle.boundary) =
      edgeListArea (fun vertex =>
        (⟨left.sewn.values vertex, right.sewn.values vertex⟩ : PrimitivePoint))
        (triangles.flatMap OrientedTriangle.boundary) := by
  induction triangles with
  | nil => rfl
  | cons triangle tail ih =>
    rw [Purelib.Data.List.Flatten.flatMap_cons, edgeListArea_append, edgeListArea_append, ih]
    congr 1
    simp only [-eq_self, -iff_self, OrientedTriangle.boundary, edgeListArea, edgeArea, sample.values_eq]
    ring1

end Purelib.Riemann.Periods.BilinearBoundaryReadback
