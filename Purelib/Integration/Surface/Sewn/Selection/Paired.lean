module
import Purelib.Topology.Polygon.WitnessReadbacks
import Purelib.Data.Gaussian.Basic

import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
public import Purelib.Integration.Surface.Sewn.Selection.Basic
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Tactic.Ring

public section

/-! Area partition for arbitrary paired values on the existing cached
selection triangles. Geometry and scalar sewing are not prepared again. -/

namespace Purelib.Integration.Surface.Sewn.Selection.Paired

open Purelib.Data.List

variable {vertexCount faceCount : Nat} {faces : Fin faceCount → Purelib.Topology.Polygon.Stokes.OrientedTriangle
  vertexCount}
  {localValues : Fin faceCount → Purelib.Topology.Surface.Sewing.PrimitiveSewing.PrimitiveValues 3} {patch :
    Purelib.Topology.Surface.Sewing.SewingTree.SewnPatch faces}
  {sample : Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample patch localValues} {keep : Fin faceCount →
    Bool}

open Purelib.Integration.Surface.Sewn.Selection in
open Purelib.Polynomial.Geometry.Grid in
open Purelib.Topology.Polygon in
/-- Read selected triangle area as the filtered face-trace sum.

The supplied primitive values use the retained selection triangles and
source occurrences; their exact cache readbacks determine the same sum. -/
theorem paired_area_readback (selected : Basic.SewnPrimitiveFaces.CachedSample.FaceSelection sample keep)
    (primitive : Fin patch.cut.count → Stokes.PrimitivePoint) :
    Stokes.edgeListArea primitive (selected.triangles.flatMap Stokes.OrientedTriangle.boundary) =
      CellBoundary.sumValues (fun trace => Stokes.edgeListArea primitive trace.triangle.boundary)
        (sample.faces.entries.filter (fun trace => keep trace.source)) := by
  rw [WitnessReadbacks.triangles_area, selected.triangles_eq, CellBoundary.sumValues_map, selected.traces_eq]

open Purelib.Integration.Surface.Sewn.Selection in
open Purelib.Polynomial.Geometry.Grid in
open Purelib.Topology.Polygon in
open Purelib.Topology.Surface.Sewing in
/-- A retained disjoint face-selection family and complement partition the original primitive boundary area.

The same original sewn patch, face bank and primitive values are used throughout; every selected occurrence keeps its
original source index. -/
theorem paired_family_partition {Label : Type} (labels : List Label) (keep : Label → Fin faceCount → Bool)
    (disjoint : labels.Pairwise (fun first second => ∀ index,
      keep first index = true → keep second index = true → False))
    (selected : (label : Label) → Basic.SewnPrimitiveFaces.CachedSample.FaceSelection sample (keep label))
    (remaining : Basic.SewnPrimitiveFaces.CachedSample.FaceSelection sample (fun index => !(labels.any (fun label =>
      keep label index))))
    (primitive : Fin patch.cut.count → Stokes.PrimitivePoint) :
    CellBoundary.sumValues (fun label => Stokes.edgeListArea primitive
      ((selected label).triangles.flatMap Stokes.OrientedTriangle.boundary)) labels +
      Stokes.edgeListArea primitive (remaining.triangles.flatMap Stokes.OrientedTriangle.boundary) =
        Stokes.edgeListArea primitive patch.cut.boundary := by
  have areas := CellBoundary.sumValues_congr _ _ labels
    (fun label _ => Paired.paired_area_readback (selected label) primitive)
  have separate : labels.Pairwise (fun first second => ∀ trace : SewnPrimitiveFaces.FaceTrace localValues
    sample.sewn.values,
      keep first trace.source = true → keep second trace.source = true → False) :=
    disjoint.imp (fun separated (trace : SewnPrimitiveFaces.FaceTrace localValues sample.sewn.values) => separated
      trace.source)
  rw [areas, ← CellBoundary.sum_filter_family _ _ labels separate,
    Paired.paired_area_readback remaining primitive, CellBoundary.sum_filter_partition]
  rw [← CellBoundary.sumValues_map (fun triangle : Stokes.OrientedTriangle patch.cut.count =>
    Stokes.edgeListArea primitive triangle.boundary) SewnPrimitiveFaces.FaceTrace.triangle,
    sample.faces.triangles_eq, ← WitnessReadbacks.triangles_area]
  exact (patch.cut.boundary_area primitive).symm

end Purelib.Integration.Surface.Sewn.Selection.Paired
