module
import Purelib.Data.List.Membership
import Purelib.Data.List.OfFn.Basic
import Purelib.Data.List.Map
import Purelib.Topology.Chain.PathBoundary

import Purelib.Data.List.Permutation
import Purelib.Topology.Mesh.CornerWalks
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.PolygonSewing
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingForest
import Purelib.Topology.Surface.Sewing.SewingProjection
import Purelib.Topology.Surface.Sewing.VertexSewing
public import Purelib.Topology.Surface.Cut.VertexGluing
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Data.Vector.Basic

public section

/-!
# Every active vertex of the assembled cut disk is on its boundary

Sewing two disks across one edge preserves all their active vertices on
the new boundary: each removed source endpoint survives as the other
side's seam finish. Induction on the retained assembly excludes hidden
interior vertices and unused allocation slots from the cut-vertex census.
-/

namespace Purelib.Topology.Surface.Cut.BoundaryVertices

open Purelib.Data
open Purelib.Data.List
open Purelib.Topology.Chain
open Purelib.Topology.Mesh.CornerWalks
open Purelib.Topology.Polygon
open Purelib.Topology.Polygon.Stokes
open Purelib.Topology.Surface.Cut
open Purelib.Topology.Surface.Cut.Patch
open Purelib.Topology.Surface.Cut.VertexGluing
open Purelib.Topology.Surface.Sewing
open Purelib.Topology.Surface.Sewing.PolygonSewing
open Purelib.Topology.Surface.Sewing.SewingConnected
open Purelib.Topology.Surface.Sewing.SewingProjection

open Purelib.Topology.Surface.Sewing.PolygonSewing.PolygonStokes (BoundarySplit)
open Purelib.Topology.Surface.Cut.Patch (CutPatch)
open Purelib.Topology.Surface.Sewing.VertexSewing
open Purelib.Topology.Surface.Cut.Patch.CutPatch (Assembly Seam)
open _root_.Purelib.Topology.Surface.Sewing (SewingForest)
open Purelib.Topology.Mesh.CornerWalks (VertexConnection)

open Purelib.Topology.Polygon.Stokes (OrientedEdge OrientedTriangle)

open Purelib.Topology.Chain.PathBoundary (PathEndpoints)

namespace BoundarySplit

variable {count : Nat} {boundary : List (Stokes.OrientedEdge count)}

/-- Removing the selected edge preserves every boundary source distinct from its start. -/
theorem start_mem_rest (split : PolygonStokes.BoundarySplit boundary) {vertex : Fin count}
    (member : vertex ∈ boundary.map OrientedEdge.start) (different : vertex ≠ split.edge.start) :
    vertex ∈ split.rest.map OrientedEdge.start := by
  rcases Map.mem_map.mp member with ⟨edge, edgeMember, equal⟩
  rcases Membership.mem_cons.mp ((EdgeReordering.mem_iff split.ordering edge).mp edgeMember) with same | inRest
  · exact (different (equal.symm.trans (congrArg OrientedEdge.start same))).elim
  · exact Map.mem_map.mpr ⟨edge, inRest, equal⟩

/-- The finish of a nonloop selected edge survives as a source in the remaining closed boundary. -/
theorem finish_mem_rest (split : PolygonStokes.BoundarySplit boundary) {anchor : Fin count}
    (closed : PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish boundary anchor anchor)
    (nonloop : split.edge.start ≠ split.edge.finish) : split.edge.finish ∈ split.rest.map OrientedEdge.start := by
  have path := split.rest_path closed
  have starts {word : List (Stokes.OrientedEdge count)} {first last : Fin count}
      (path : PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish word first last) (different : first ≠
        last) :
      first ∈ word.map OrientedEdge.start := by
    cases path with
    | nil => exact (different rfl).elim
    | cons => exact List.mem_cons_self
  exact starts path (Ne.symm nonloop)

end BoundarySplit

namespace CutPatch

variable {vertexCount faceCount : Nat} {faces : Fin faceCount → Stokes.OrientedTriangle vertexCount}

section
open Purelib.Topology.Surface.Cut.BoundaryVertices
/-- Every active left boundary source survives on the sewn boundary.

The removed source is represented by the opposite seam's surviving finish. -/
private theorem sew_boundary_left {firstIndices secondIndices : List (Fin faceCount)}
    {firstBoundary secondBoundary : List (Stokes.OrientedEdge vertexCount)}
    (first : Patch.CutPatch faces firstIndices firstBoundary) (second : Patch.CutPatch faces secondIndices
      secondBoundary)
    (firstBase : PolygonStokes.BoundarySplit firstBoundary) (secondBase : PolygonStokes.BoundarySplit secondBoundary)
    (opposite : secondBase.edge = firstBase.edge.reverse) (seam : CutPatch.Seam first second firstBase secondBase)
    {vertex : Fin first.count} (member : vertex ∈ first.boundary.map OrientedEdge.start) :
    Purelib.Topology.Surface.Sewing.VertexSewing.EndpointGluing.left vertex ∈ (first.sew second firstBase secondBase
      opposite seam).boundary.map OrientedEdge.start := by
  change EndpointGluing.left vertex ∈
    (((BoundarySplit.map EndpointGluing.left seam.firstLift.split).rest ++
      (BoundarySplit.map (EndpointGluing.right seam.firstLift.split.edge seam.secondLift.split.edge)
        seam.secondLift.split).rest).map OrientedEdge.start)
  rw [Map.map_append, BoundarySplit.map_rest, BoundarySplit.map_rest, SewingProjection.edgeStarts_map,
    SewingProjection.edgeStarts_map]
  by_cases removed : vertex = seam.firstLift.split.edge.start
  · apply List.mem_append_right
    have surviving := BoundarySplit.finish_mem_rest seam.secondLift.split second.closed
      (second.nonloop _ seam.secondLift.split.edge_mem)
    have mapped := Map.mem_map_of_mem
      (f := EndpointGluing.right seam.firstLift.split.edge seam.secondLift.split.edge) surviving
    rw [EndpointGluing.right_finish _ _ (second.nonloop _ seam.secondLift.split.edge_mem), ← removed] at mapped
    exact mapped
  · exact List.mem_append_left _ (Map.mem_map_of_mem (BoundarySplit.start_mem_rest seam.firstLift.split member removed))

/-- Every active right boundary source survives on the sewn boundary.

The removed source is represented by the left seam's surviving finish. -/
private theorem sew_boundary_right {firstIndices secondIndices : List (Fin faceCount)}
    {firstBoundary secondBoundary : List (Stokes.OrientedEdge vertexCount)}
    (first : Patch.CutPatch faces firstIndices firstBoundary) (second : Patch.CutPatch faces secondIndices
      secondBoundary)
    (firstBase : PolygonStokes.BoundarySplit firstBoundary) (secondBase : PolygonStokes.BoundarySplit secondBoundary)
    (opposite : secondBase.edge = firstBase.edge.reverse) (seam : CutPatch.Seam first second firstBase secondBase)
    {vertex : Fin second.count} (member : vertex ∈ second.boundary.map OrientedEdge.start) :
    Purelib.Topology.Surface.Sewing.VertexSewing.EndpointGluing.right seam.firstLift.split.edge
      seam.secondLift.split.edge vertex ∈
      (first.sew second firstBase secondBase opposite seam).boundary.map OrientedEdge.start := by
  change EndpointGluing.right seam.firstLift.split.edge seam.secondLift.split.edge vertex ∈
    (((BoundarySplit.map EndpointGluing.left seam.firstLift.split).rest ++
      (BoundarySplit.map (EndpointGluing.right seam.firstLift.split.edge seam.secondLift.split.edge)
        seam.secondLift.split).rest).map OrientedEdge.start)
  rw [Map.map_append, BoundarySplit.map_rest, BoundarySplit.map_rest, SewingProjection.edgeStarts_map,
    SewingProjection.edgeStarts_map]
  by_cases removed : vertex = seam.secondLift.split.edge.start
  · rw [removed, EndpointGluing.right_start]
    exact List.mem_append_left _ (Map.mem_map_of_mem
      (BoundarySplit.finish_mem_rest seam.firstLift.split first.closed (first.nonloop _ seam.firstLift.split.edge_mem)))
  · exact List.mem_append_right _ (Map.mem_map_of_mem (BoundarySplit.start_mem_rest seam.secondLift.split member
      removed))

end

/-- A corner of a relabeled triangle has an original corner preimage. -/
private theorem triangle_map_vertex {source target : Nat} (labels : Fin source → Fin target)
    {triangle : Stokes.OrientedTriangle source} {vertex : Fin target} (member : OrientedTriangle.ContainsVertex
      (Purelib.Topology.Surface.Sewing.VertexSewing.OrientedTriangle.map labels triangle) vertex) :
    ∃ original, OrientedTriangle.ContainsVertex triangle original ∧ labels original = vertex := by
  rcases member with first | second | third
  · exact ⟨triangle.first, .inl rfl, first.symm⟩
  · exact ⟨triangle.second, .inr (.inl rfl), second.symm⟩
  · exact ⟨triangle.third, .inr (.inr rfl), third.symm⟩

open Purelib.Topology.Surface.Cut.BoundaryVertices.CutPatch in
open Purelib.Topology.Surface.Cut.BoundaryVertices in
/-- This uses the actual assembly, not just a record asserting that some boundary is simple. Such an arbitrary record
could hide interior vertices. -/
theorem Assembly.active_on_boundary {indices : List (Fin faceCount)} {boundary : List (Stokes.OrientedEdge vertexCount)}
    {patch : Patch.CutPatch faces indices boundary} (assembly : CutPatch.Assembly faces patch)
    {vertex : Fin patch.count} (active : CutPatch.ActiveVertex patch vertex) : vertex ∈ patch.boundary.map
      OrientedEdge.start := by
  induction assembly with
  | triangle index =>
      rcases active with ⟨triangle, member, atVertex⟩
      have equal : triangle = (⟨0, 1, 2⟩ : Stokes.OrientedTriangle 3) := Membership.mem_singleton.mp member
      cases equal
      rcases atVertex with rfl | rfl | rfl
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  | @sew firstIndices secondIndices firstBoundary secondBoundary first second left right firstBase secondBase opposite
    seam ihLeft ihRight =>
      rcases active with ⟨triangle, member, atVertex⟩
      change triangle ∈ first.triangles.map (OrientedTriangle.map EndpointGluing.left) ++
        second.triangles.map (OrientedTriangle.map (EndpointGluing.right seam.firstLift.split.edge
          seam.secondLift.split.edge)) at member
      rcases Membership.mem_append.mp member with onLeft | onRight
      · rcases Map.mem_map.mp onLeft with ⟨original, originalMember, equal⟩
        rw [← equal] at atVertex
        rcases triangle_map_vertex EndpointGluing.left atVertex with ⟨originalVertex, onTriangle, vertexEq⟩
        rw [← vertexEq]
        exact sew_boundary_left first second firstBase secondBase opposite seam (ihLeft ⟨original,
          originalMember, onTriangle⟩)
      · rcases Map.mem_map.mp onRight with ⟨original, originalMember, equal⟩
        rw [← equal] at atVertex
        rcases triangle_map_vertex (EndpointGluing.right seam.firstLift.split.edge seam.secondLift.split.edge) atVertex
          with
          ⟨originalVertex, onTriangle, vertexEq⟩
        rw [← vertexEq]
        exact sew_boundary_right first second firstBase secondBase opposite seam (ihRight ⟨original,
          originalMember, onTriangle⟩)

open Purelib.Topology.Surface.Cut.BoundaryVertices.CutPatch in
/-- The active vertices of an assembled cut disk are exactly its boundary sources. -/
theorem Assembly.active_iff_boundary {indices : List (Fin faceCount)} {boundary : List (Stokes.OrientedEdge
  vertexCount)}
    {patch : Patch.CutPatch faces indices boundary} (assembly : CutPatch.Assembly faces patch) (vertex : Fin
      patch.count) :
    CutPatch.ActiveVertex patch vertex ↔ vertex ∈ patch.boundary.map OrientedEdge.start := by
  constructor
  · exact Assembly.active_on_boundary assembly
  · intro member
    rcases Map.mem_map.mp member with ⟨edge, edgeMember, equal⟩
    exact CutPatch.boundary_vertex_active patch edgeMember (.inl equal.symm)

end CutPatch

namespace SewingForest.SinglePolygon

variable {vertexCount faceCount : Nat} {faces : Fin faceCount → Stokes.OrientedTriangle vertexCount}
  {forest : Sewing.SewingForest faces}

open Purelib.Topology.Surface.Cut.BoundaryVertices.CutPatch in
/-- The projected source list covers exactly the original triangle vertices, not the whole allocated target carrier. -/
theorem boundary_projection_mem_iff (polygon : SewingForest.SinglePolygon forest) (vertex : Fin vertexCount) :
    vertex ∈ (polygon.patch.cut.boundary.map OrientedEdge.start).map polygon.patch.cut.vertexLabels ↔
      ∃ index, OrientedTriangle.ContainsVertex (faces index) vertex := by
  constructor
  · intro member
    rcases Map.mem_map.mp member with ⟨source, sourceMember, same⟩
    have active := (Assembly.active_iff_boundary polygon.patch.assembly source).mpr sourceMember
    rcases active with ⟨triangle, triangleMember, contains⟩
    have projected := Map.mem_map_of_mem (f := OrientedTriangle.map polygon.patch.cut.vertexLabels) triangleMember
    rw [polygon.patch.cut.triangles_eq] at projected
    rcases Map.mem_map.mp projected with ⟨index, _, triangleEq⟩
    refine ⟨index, ?_⟩
    rw [triangleEq, ← same]
    exact contains.map polygon.patch.cut.vertexLabels
  · rintro ⟨index, contains⟩
    have faceMember : index ∈ polygon.patch.faceIndices :=
      (List.Permutation.mem_iff polygon.coverage index).mpr (OfFn.Basic.mem_ofFn.mpr ⟨index, rfl⟩)
    have triangleMember := Map.mem_map_of_mem (f := faces) faceMember
    rw [← polygon.patch.cut.triangles_eq] at triangleMember
    rcases Map.mem_map.mp triangleMember with ⟨triangle, inCut, triangleEq⟩
    rw [← triangleEq] at contains
    rcases contains with first | second | third
    · exact Map.mem_map.mpr ⟨triangle.first,
        Assembly.active_on_boundary polygon.patch.assembly ⟨triangle, inCut, .inl rfl⟩, first.symm⟩
    · exact Map.mem_map.mpr ⟨triangle.second,
        Assembly.active_on_boundary polygon.patch.assembly ⟨triangle, inCut, .inr (.inl rfl)⟩, second.symm⟩
    · exact Map.mem_map.mpr ⟨triangle.third,
        Assembly.active_on_boundary polygon.patch.assembly ⟨triangle, inCut, .inr (.inr rfl)⟩, third.symm⟩

end SewingForest.SinglePolygon
end Purelib.Topology.Surface.Cut.BoundaryVertices
