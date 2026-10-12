module
import Purelib.Data.List.Membership
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.List.Flatten
import Purelib.Data.List.Map
public import Purelib.Integration.Energy.Polygon
import Purelib.Topology.Chain.PathBoundary

import Purelib.Integration.Path.IncrementArea
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Boundary.BoundaryPotential
import Purelib.Topology.Surface.Cut.Patch
public import Purelib.Topology.Surface.Cut.PotentialReadings
import Purelib.Topology.Surface.Sewing.SewingProjection
import Purelib.Topology.Surface.Sewing.SewnPrimitivePaths
import Purelib.Topology.Surface.Sewing.VertexSewing
import Purelib.Topology.Surface.Cut.PotentialClosed
import Purelib.Topology.Surface.Sewing.SewnPathArea
public import Purelib.Topology.Mesh.RetracingWords
import Purelib.Data.Vector.Basic

section

open Purelib

public section

/-! Exact whole-cut area readback for the retained closed surface valuations. -/
namespace Purelib.Topology.Surface.Cut.PotentialAreas

open Purelib.Topology.Polygon.Stokes (OrientedEdge OrientedTriangle edgeListArea edgeListArea_append)
open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib.Topology.Chain.PathBoundary (PathEndpoints)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Topology.Surface.Cut.Patch (CutPatch)
open _root_.Purelib.Topology.Surface.Boundary (BoundaryPotential)
open _root_.Purelib.Topology.Surface.Cut (PotentialReadings)
open Purelib.Topology.Mesh.RetracingWords (wordArea)
open Purelib.Integration.Energy.Polygon (energyPrimitivePoint)

variable {vertices facesCount : Nat} {faces : Fin facesCount → Topology.Polygon.Stokes.OrientedTriangle vertices}
  {indices : List (Fin facesCount)} {boundary : List (Topology.Polygon.Stokes.OrientedEdge vertices)}
  {patch : Topology.Surface.Cut.Patch.CutPatch faces indices boundary}
  {sourceValue : Topology.Polygon.Stokes.OrientedEdge vertices → Data.Gaussian.Basic.Canonical}
  {potential : Boundary.BoundaryPotential patch.boundary (fun edge => sourceValue
    (Topology.Surface.Sewing.VertexSewing.OrientedEdge.map patch.vertexLabels edge))}
  (data : PotentialReadings patch sourceValue potential)
  (unique : ((patch.triangles.flatMap Topology.Polygon.Stokes.OrientedTriangle.boundary).map
    (Topology.Surface.Sewing.VertexSewing.OrientedEdge.map patch.vertexLabels)).Nodup)

include unique

/-- Only actual cut occurrences telescope; projected vertex labels are not identified. -/
theorem closed_path_area {word : List (Topology.Polygon.Stokes.OrientedEdge patch.count)} {anchor : Fin patch.count}
    (closed : Topology.Chain.PathBoundary.PathEndpoints Topology.Polygon.Stokes.OrientedEdge.start
      Topology.Polygon.Stokes.OrientedEdge.finish word anchor anchor)
    (supported : ∀ edge ∈ word, edge ∈ patch.triangles.flatMap Topology.Polygon.Stokes.OrientedTriangle.boundary) :
    Topology.Mesh.RetracingWords.wordArea data.value (word.map (Topology.Surface.Sewing.VertexSewing.OrientedEdge.map
      patch.vertexLabels)) =
      Topology.Polygon.Stokes.edgeListArea (fun vertex => Integration.Energy.Polygon.energyPrimitivePoint
        (potential.values vertex)) word := by
  have equal := Topology.Surface.Sewing.SewnPathArea.traceArea_edges potential.values closed
  rw [Integration.Path.IncrementArea.traceArea_eq,
    Topology.Surface.Sewing.SewnPrimitivePaths.SewnPrimitiveFaces.PathSources.Sample.telescope potential.values closed,
    sub_self, Integration.Path.IncrementArea.area_zero_right, add_zero] at equal
  apply Eq.trans _ equal
  unfold Topology.Mesh.RetracingWords.wordArea
  rw [Data.List.Map.map_map]
  apply congrArg Integration.Path.IncrementArea.pathArea
  exact Data.List.Map.map_congr_left (fun edge member => data.value_occurrence unique edge (supported edge member))

open Purelib
/-- The retained potential gives the same area on an original cut triangle as its projected increment word. -/
theorem triangle_area (triangle : Topology.Polygon.Stokes.OrientedTriangle patch.count) (member : triangle ∈
  patch.triangles) :
    Topology.Mesh.RetracingWords.wordArea data.value (Topology.Surface.Sewing.VertexSewing.OrientedTriangle.map
      patch.vertexLabels triangle).boundary =
      Topology.Polygon.Stokes.edgeListArea (fun vertex => Integration.Energy.Polygon.energyPrimitivePoint
        (potential.values vertex)) triangle.boundary := by
  have closed : Topology.Chain.PathBoundary.PathEndpoints Topology.Polygon.Stokes.OrientedEdge.start
    Topology.Polygon.Stokes.OrientedEdge.finish triangle.boundary triangle.first triangle.first :=
    .cons (.cons (.cons (.nil triangle.first)))
  exact closed_path_area data unique closed
    (fun edge onTriangle => Data.List.Flatten.mem_flatMap.mpr ⟨triangle, member, onTriangle⟩)

/-- Reading the projected original boundary word recovers its retained cut-potential edge area. -/
theorem boundary_area : Topology.Mesh.RetracingWords.wordArea data.value boundary =
    Topology.Polygon.Stokes.edgeListArea (fun vertex => Integration.Energy.Polygon.energyPrimitivePoint
      (potential.values vertex)) patch.boundary := by
  apply (congrArg (Topology.Mesh.RetracingWords.wordArea data.value) patch.boundary_eq.symm).trans
  exact closed_path_area data unique patch.closed (fun edge member =>
    (Topology.Surface.Sewing.SewingProjection.EdgeReordering.mem_iff patch.incidence edge).mpr
      (Data.List.Membership.mem_append.mpr (Or.inl member)))

/-- Finite Stokes reads every retained face, with no complementary region omitted. -/
theorem surface_area : Topology.Mesh.RetracingWords.wordArea data.value boundary =
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (indices.map (fun index => Topology.Mesh.RetracingWords.wordArea
      data.value (faces index).boundary)) := by
  rw [boundary_area data unique, patch.boundary_area]
  have triangles (items : List (Topology.Polygon.Stokes.OrientedTriangle patch.count))
      (supported : ∀ triangle ∈ items, triangle ∈ patch.triangles) :
      Topology.Polygon.Stokes.edgeListArea (fun vertex => Integration.Energy.Polygon.energyPrimitivePoint
        (potential.values vertex))
        (items.flatMap Topology.Polygon.Stokes.OrientedTriangle.boundary) =
        Data.Gaussian.Norm.Sum.Basic.gaussianSum (items.map (fun triangle => Topology.Mesh.RetracingWords.wordArea
          data.value (Topology.Surface.Sewing.VertexSewing.OrientedTriangle.map patch.vertexLabels triangle).boundary))
          := by
    induction items with
    | nil => rfl
    | cons triangle rest ih =>
        rw [Data.List.Flatten.flatMap_cons, Topology.Polygon.Stokes.edgeListArea_append]
        exact congrArg₂ (· + ·) (triangle_area data unique triangle (supported
          triangle List.mem_cons_self)).symm
          (ih (fun other member => supported other (List.mem_cons_of_mem _ member)))
  rw [triangles patch.triangles (fun _ member => member)]
  have equal := congrArg (List.map (fun triangle => Topology.Mesh.RetracingWords.wordArea data.value triangle.boundary))
    patch.triangles_eq
  simp only [Data.List.Map.map_map, Function.comp_def] at equal
  exact congrArg Data.Gaussian.Norm.Sum.Basic.gaussianSum equal

end Purelib.Topology.Surface.Cut.PotentialAreas

end
