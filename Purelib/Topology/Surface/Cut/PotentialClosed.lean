module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.List.Flatten
import Purelib.Data.List.Map

import Purelib.Data.List.Permutation
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Boundary.BoundaryPotential
import Purelib.Topology.Surface.Cut.BoundaryPairs
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Topology.Surface.Sewing.VertexSewing
public import Purelib.Topology.Surface.Cut.PotentialReadings
import Purelib.Data.Vector.Basic
import Purelib.Tactic.Ring

section

open Purelib.Data

open Purelib.Data.List

open Purelib.Topology.Polygon

open Purelib.Topology.Polygon.Stokes

open Purelib.Topology.Surface.Boundary

open Purelib.Topology.Surface.Cut

open Purelib.Topology.Surface.Cut.BoundaryPairs

open Purelib.Topology.Surface.Sewing

open Purelib.Topology.Surface.Sewing.VertexSewing

public section

/-! Exact face closure for surface readings descended from the retained cut potential. -/
namespace Purelib.Topology.Surface.Cut.PotentialClosed

open Purelib.Topology.Surface.Cut.PotentialReadings
open _root_.Purelib.Topology.Surface.Cut renaming PotentialReadings -> PotentialReadings
open Purelib.Topology.Surface.Cut.Patch (CutPatch)
open _root_.Purelib.Topology.Surface.Boundary (BoundaryPotential)

open Purelib.Topology.Polygon.Stokes (OrientedEdge OrientedTriangle)
open Purelib.Data.Gaussian.Basic (Canonical)

variable {vertices facesCount : Nat} {faces : Fin facesCount → Stokes.OrientedTriangle vertices}
  {indices : List (Fin facesCount)} {boundary : List (Stokes.OrientedEdge vertices)}
  {patch : Patch.CutPatch faces indices boundary}
  {sourceValue : Stokes.OrientedEdge vertices → Gaussian.Basic.Canonical}
  {potential : Boundary.BoundaryPotential patch.boundary (fun edge => sourceValue (OrientedEdge.map
    patch.vertexLabels edge))}

namespace PotentialReadings
variable (data : PotentialReadings patch sourceValue potential)
  (unique : ((patch.triangles.flatMap OrientedTriangle.boundary).map (OrientedEdge.map patch.vertexLabels)).Nodup)

include unique

/-- The retained potential reading telescopes to zero around each original cut triangle. -/
theorem cut_triangle_zero (triangle : Stokes.OrientedTriangle patch.count) (member : triangle ∈ patch.triangles) :
    SewingRetraction.wordValue data.value (OrientedTriangle.map patch.vertexLabels triangle).boundary = 0 := by
  have included (edge : Stokes.OrientedEdge patch.count) (onTriangle : edge ∈ triangle.boundary) :
      edge ∈ patch.triangles.flatMap OrientedTriangle.boundary :=
    Flatten.mem_flatMap.mpr ⟨triangle, member, onTriangle⟩
  change data.value (OrientedEdge.map patch.vertexLabels (⟨triangle.first, triangle.second⟩ : Stokes.OrientedEdge
    patch.count)) +
    (data.value (OrientedEdge.map patch.vertexLabels (⟨triangle.second, triangle.third⟩ : Stokes.OrientedEdge
      patch.count)) +
      (data.value (OrientedEdge.map patch.vertexLabels (⟨triangle.third, triangle.first⟩ : Stokes.OrientedEdge
        patch.count)) + 0)) = 0
  rw [data.value_occurrence unique _ (included _ List.mem_cons_self),
    data.value_occurrence unique _ (included _ (List.mem_cons_of_mem _ List.mem_cons_self)),
    data.value_occurrence unique _ (included _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))]
  ring1

open Purelib.Topology.Surface.Cut.PotentialClosed in
/-- The retained reading vanishes around each included original face by its exact cut-triangle projection. -/
theorem face_zero (index : Fin facesCount) (covered : index ∈ indices) :
    SewingRetraction.wordValue data.value (faces index).boundary = 0 := by
  have member : faces index ∈ patch.triangles.map (OrientedTriangle.map patch.vertexLabels) := by
    rw [patch.triangles_eq]
    exact Map.mem_map_of_mem covered
  obtain ⟨triangle, member, equal⟩ := Map.mem_map.mp member
  rw [← equal]
  exact cut_triangle_zero data unique triangle member

end PotentialReadings

/-- The exposed generator incidences inherit uniqueness from the original face incidences. -/
theorem boundary_unique_of_occurrences
    (unique : ((patch.triangles.flatMap OrientedTriangle.boundary).map (OrientedEdge.map patch.vertexLabels)).Nodup) :
    (patch.boundary.map (OrientedEdge.map patch.vertexLabels)).Nodup := by
  have ordering := EdgeReordering.map patch.vertexLabels patch.incidence
  rw [Map.map_append] at ordering
  exact (List.Permutation.nodup_append_parts
    (List.Permutation.nodup (EdgeReordering.toPerm ordering) unique)).1

end Purelib.Topology.Surface.Cut.PotentialClosed

end
