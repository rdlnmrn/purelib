module
import Purelib.Data.List.Membership
import Purelib.Data.List.Nodup
import Purelib.Tactic.Ring
import Purelib.Data.Gaussian.Basic
import Purelib.Data.List.Map

import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.SewingProjection
import Purelib.Topology.Surface.Sewing.VertexSewing
import Purelib.Topology.Surface.Cut.BoundaryPairs
public import Purelib.Topology.Surface.Boundary.BoundaryPotential
import Purelib.Data.Vector.Basic

public section

/-! Boundary-compatible primitive increments agree across every actual cut seam. -/
namespace Purelib.Topology.Surface.Cut.PotentialCompatibility.CutPatch

open Purelib.Data

open Purelib.Data.List

open Purelib.Topology.Polygon

open Purelib.Topology.Polygon.Stokes

open Purelib.Topology.Surface.Boundary

open Purelib.Topology.Surface.Cut

open Purelib.Topology.Surface.Sewing.SewingProjection

open Purelib.Topology.Surface.Sewing.VertexSewing

open Purelib.Topology.Polygon.Stokes (OrientedEdge OrientedTriangle pairedEdgeOccurrences)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Topology.Surface.Cut.BoundaryPairs (pairedEdgeOccurrences_reverse_mem)
open Purelib.Topology.Surface.Cut.Patch (CutPatch)
open _root_.Purelib.Topology.Surface.Boundary (BoundaryPotential)

section
variable {vertices facesCount : Nat} {faces : Fin facesCount → Stokes.OrientedTriangle vertices}
  {indices : List (Fin facesCount)} {boundary : List (Stokes.OrientedEdge vertices)}
  (patch : Patch.CutPatch faces indices boundary)

open Purelib.Topology.Surface.Cut in
/-- Unique projected incidence identifies occurrences with equal projected edges.

Injectivity of the mapped original triangle-edge list identifies the two
retained occurrences from their membership and projected-edge equality. -/
theorem occurrence_eq_of_projected_eq
    (unique : ((patch.triangles.flatMap OrientedTriangle.boundary).map (OrientedEdge.map patch.vertexLabels)).Nodup)
    {first last : Stokes.OrientedEdge patch.count}
    (firstMember : first ∈ patch.triangles.flatMap OrientedTriangle.boundary)
    (lastMember : last ∈ patch.triangles.flatMap OrientedTriangle.boundary)
    (equal : OrientedEdge.map patch.vertexLabels first = OrientedEdge.map patch.vertexLabels last) : first = last :=
  Nodup.eq_of_map_eq_of_mem _ unique firstMember lastMember equal

/-- Each retained seam orientation is an original triangle-edge occurrence.

The incidence reordering contains the ordered boundary and seam lists.
A seam membership certificate selects its occurrence in that same list. -/
theorem seam_occurrence {edge : Stokes.OrientedEdge patch.count}
    (member : edge ∈ Stokes.pairedEdgeOccurrences patch.seams) :
    edge ∈ patch.triangles.flatMap OrientedTriangle.boundary :=
  (EdgeReordering.mem_iff patch.incidence edge).mpr (Membership.mem_append.mpr (Or.inr member))

open Purelib.Topology.Surface.Cut.PotentialCompatibility
/-- Opposite projected incidences are exposed together or literally reversed.

The incidence split and unique projection certificate distinguish boundary
occurrences from retained seam orientations without changing their labels. -/
theorem opposite_occurrences
    (unique : ((patch.triangles.flatMap OrientedTriangle.boundary).map (OrientedEdge.map patch.vertexLabels)).Nodup)
    {first last : Stokes.OrientedEdge patch.count}
    (firstMember : first ∈ patch.triangles.flatMap OrientedTriangle.boundary)
    (lastMember : last ∈ patch.triangles.flatMap OrientedTriangle.boundary)
    (opposite : OrientedEdge.map patch.vertexLabels last = (OrientedEdge.map patch.vertexLabels first).reverse) :
    (first ∈ patch.boundary ∧ last ∈ patch.boundary) ∨ last = first.reverse := by
  rcases Membership.mem_append.mp ((EdgeReordering.mem_iff patch.incidence first).mp firstMember) with firstBoundary |
    firstSeam
  · rcases Membership.mem_append.mp ((EdgeReordering.mem_iff patch.incidence last).mp lastMember) with lastBoundary |
      lastSeam
    · exact Or.inl ⟨firstBoundary, lastBoundary⟩
    · have same : last.reverse = first := occurrence_eq_of_projected_eq patch unique
        (seam_occurrence patch (BoundaryPairs.pairedEdgeOccurrences_reverse_mem _ lastSeam)) firstMember
        ((congrArg OrientedEdge.reverse opposite).trans (OrientedEdge.reverse_reverse _))
      exact Or.inr ((congrArg OrientedEdge.reverse same).symm.trans (OrientedEdge.reverse_reverse _)).symm
  · exact Or.inr (occurrence_eq_of_projected_eq patch unique lastMember
      (seam_occurrence patch (BoundaryPairs.pairedEdgeOccurrences_reverse_mem _ firstSeam)) opposite)

/-- Boundary-compatible potentials reverse across opposite incidences.

Exposed occurrences use the retained increment equations and the supplied
antisymmetry. Sewn occurrences share the exact reversed endpoint labels. -/
theorem potential_opposite
    (unique : ((patch.triangles.flatMap OrientedTriangle.boundary).map (OrientedEdge.map patch.vertexLabels)).Nodup)
    (value : Stokes.OrientedEdge vertices → Gaussian.Basic.Canonical) (anti : ∀ edge, value edge.reverse = -value edge)
    (potential : Boundary.BoundaryPotential patch.boundary (fun edge => value (OrientedEdge.map
      patch.vertexLabels edge)))
    {first last : Stokes.OrientedEdge patch.count}
    (firstMember : first ∈ patch.triangles.flatMap OrientedTriangle.boundary)
    (lastMember : last ∈ patch.triangles.flatMap OrientedTriangle.boundary)
    (opposite : OrientedEdge.map patch.vertexLabels last = (OrientedEdge.map patch.vertexLabels first).reverse) :
    potential.values last.finish - potential.values last.start =
      -(potential.values first.finish - potential.values first.start) := by
  rcases opposite_occurrences patch unique firstMember lastMember opposite with exposed | sewn
  · rw [potential.increments first exposed.1, potential.increments last exposed.2, opposite, anti]
  · cases sewn
    change potential.values first.start - potential.values first.finish =
      -(potential.values first.finish - potential.values first.start)
    ring1

end
end Purelib.Topology.Surface.Cut.PotentialCompatibility.CutPatch
