module
import Purelib.Data.List.Append
import Purelib.Data.List.Membership
import Purelib.Data.List.OfFn.Basic
import Purelib.Data.List.Flatten
import Purelib.Data.List.Map

import Purelib.Data.List.Permutation
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.SewingForest
import Purelib.Topology.Surface.Sewing.SewingProjection
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Surface.Sewing.VertexSewing
public import Purelib.Topology.Surface.Word.ProjectedEdgePairs
public import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Data.Vector.Basic

public section

/-!
# Complete classification of the remaining cut-polygon edges

On a mesh with unique oriented incidence, an exposed edge whose reverse
exists anywhere in the mesh still has its reverse exposed. It cannot have
been consumed by a sewing seam, because that would consume both orientations.
Thus pairing projected cut occurrences leaves exactly the genuine one-sided
mesh boundary. This does not yet identify the paired cuts with A/B cycles.
-/

namespace Purelib.Topology.Surface.Cut.BoundaryPairs

open Purelib.Data

open Purelib.Data.List

open Purelib.Topology.Polygon

open Purelib.Topology.Polygon.Stokes

open Purelib.Topology.Surface.Sewing

open Purelib.Topology.Surface.Sewing.SewingConnected

open Purelib.Topology.Surface.Sewing.SewingProjection

open Purelib.Topology.Surface.Sewing.VertexSewing

open Purelib.Topology.Surface.Word

open Purelib.Topology.Surface.Word.ProjectedEdgePairs

open Purelib.Topology.Polygon.Stokes (EdgeReordering OrientedEdge OrientedTriangle pairedEdgeOccurrences
  triangleEdgeOccurrences)
open Purelib.Topology.Surface.Word.ProjectedEdgePairs (ProjectedEdgePair ProjectedEdgePairing)
open Purelib.Topology.Surface.Sewing.SewingTree (SewnPatch)
open _root_.Purelib.Topology.Surface.Sewing (SewingForest)

/-- Finite indexed nondegeneracy data suffice for every actual face-edge occurrence.

Each retained triangle has three distinct consecutive vertices. Membership in its materialized edge bank identifies one
of those same oriented edges and supplies the corresponding endpoint inequality. -/
theorem triangleEdgeOccurrences_nonloop {vertexCount faceCount : Nat}
    (faces : Fin faceCount → Stokes.OrientedTriangle vertexCount)
    (distinct : ∀ index, (faces index).first ≠ (faces index).second ∧
      (faces index).second ≠ (faces index).third ∧ (faces index).third ≠ (faces index).first)
    (edge : Stokes.OrientedEdge vertexCount) (member : edge ∈ Stokes.triangleEdgeOccurrences faces) :
    edge.start ≠ edge.finish := by
  obtain ⟨triangle, triangleMember, member⟩ := Flatten.mem_flatMap.mp member
  obtain ⟨index, equal⟩ := OfFn.Basic.mem_ofFn.mp triangleMember
  cases equal
  rcases Membership.mem_cons.mp member with same | member
  · cases same; exact (distinct index).1
  · rcases Membership.mem_cons.mp member with same | member
    · cases same; exact (distinct index).2.1
    · rcases Membership.mem_cons.mp member with same | member
      · cases same; exact (distinct index).2.2
      · exact (List.not_mem_nil member).elim

/-- Convert a constructive edge-occurrence reordering into the corresponding list permutation. -/
theorem EdgeReordering.toPerm {count : Nat} {left right : List (Stokes.OrientedEdge count)}
    (ordering : Stokes.EdgeReordering left right) : List.Perm left right := by
  induction ordering with
  | nil => exact .nil
  | cons edge rest ih => exact .cons edge ih
  | swap first second rest => exact .swap second first rest
  | trans first second ihFirst ihSecond => exact .trans ihFirst ihSecond

/-- A retained internal edge occurrence is accompanied by its reverse.

Every selected seam contributes both orientations to the ordered occurrence list. Structural membership identifies
either member of that pair or the same retained occurrence in the remaining seams. -/
theorem pairedEdgeOccurrences_reverse_mem {count : Nat} {edge : Stokes.OrientedEdge count} :
    (seams : List (Stokes.OrientedEdge count)) → edge ∈ Stokes.pairedEdgeOccurrences seams →
    edge.reverse ∈ Stokes.pairedEdgeOccurrences seams
  | [], member => (List.not_mem_nil member).elim
  | first :: rest, member => by
      rcases Membership.mem_cons.mp member with same | member
      · cases same; exact List.Mem.tail _ (List.Mem.head _)
      · rcases Membership.mem_cons.mp member with same | member
        · cases same; rw [OrientedEdge.reverse_reverse]; exact (List.Mem.head _)
        · exact List.Mem.tail _ (List.Mem.tail _
            (pairedEdgeOccurrences_reverse_mem rest member))

namespace ProjectedEdgePairing

variable {source target : Nat} {labels : Fin source → Fin target} {edges : List (Stokes.OrientedEdge source)}

open Purelib.Topology.Surface.Cut.BoundaryPairs in
/-- The residual projected occurrences are precisely the input occurrences without an opposite anywhere in the input.

The supplied projected-incidence uniqueness separates residual boundary occurrences from selected paired occurrences.
Reversal membership then classifies each retained input edge without discarding its orientation or multiplicity. -/
theorem boundary_iff (pairing : ProjectedEdgePairs.ProjectedEdgePairing labels edges)
    (unique : (edges.map (OrientedEdge.map labels)).Nodup) (edge : Stokes.OrientedEdge target) :
    edge ∈ pairing.boundary.map (OrientedEdge.map labels) ↔
      edge ∈ edges.map (OrientedEdge.map labels) ∧ edge.reverse ∉ edges.map (OrientedEdge.map labels) := by
  have ordering := EdgeReordering.map labels pairing.incidence
  rw [Map.map_append] at ordering
  have disjoint := (List.Permutation.nodup_append_parts
    (List.Permutation.nodup (EdgeReordering.toPerm ordering) unique)).2.2
  constructor
  · intro member
    refine ⟨(EdgeReordering.mem_iff ordering edge).mpr (Membership.mem_append.mpr (Or.inl member)), ?_⟩
    intro reverseMember
    rcases Membership.mem_append.mp ((EdgeReordering.mem_iff ordering edge.reverse).mp reverseMember) with onBoundary |
      inPairs
    · obtain ⟨first, firstMember, firstEq⟩ := Map.mem_map.mp member
      obtain ⟨second, secondMember, secondEq⟩ := Map.mem_map.mp onBoundary
      exact pairing.noReverse first firstMember second secondMember
        (secondEq.trans (congrArg OrientedEdge.reverse firstEq.symm))
    · have inPairs := ProjectedEdgePair.reverse_mem pairing.pairs inPairs
      rw [OrientedEdge.reverse_reverse] at inPairs
      exact disjoint edge member edge inPairs rfl
  · rintro ⟨member, missing⟩
    rcases Membership.mem_append.mp ((EdgeReordering.mem_iff ordering edge).mp member) with onBoundary | inPairs
    · exact onBoundary
    · exact (missing ((EdgeReordering.mem_iff ordering edge.reverse).mpr
        (Membership.mem_append.mpr (Or.inr (ProjectedEdgePair.reverse_mem pairing.pairs inPairs))))).elim

end ProjectedEdgePairing

namespace SewnPatch

variable {vertexCount faceCount : Nat} {faces : Fin faceCount → Stokes.OrientedTriangle vertexCount}

open Purelib.Topology.Surface.Cut.BoundaryPairs in
/-- Unique original face-edge incidence gives a duplicate-free exposed patch boundary. -/
theorem boundary_unique (patch : SewingTree.SewnPatch faces) (unique : (SewnPatch.originalEdges patch).Nodup) :
  patch.boundary.Nodup :=
  (List.Permutation.nodup_append_parts
    (List.Permutation.nodup (EdgeReordering.toPerm patch.incidence) unique)).1

open Purelib.Topology.Surface.Cut in
open Purelib.Topology.Surface.Cut.BoundaryPairs in
/-- An opposite of an exposed edge occurs in the exposed boundary exactly when it occurs in the retained input bank.

Unique input incidence separates exposed occurrences from selected seams. Each selected seam retains both orientations,
so the reverse of an exposed occurrence cannot belong to that internal paired bank. -/
theorem reverse_mem_boundary_iff (patch : SewingTree.SewnPatch faces) (unique : (SewnPatch.originalEdges patch).Nodup)
    {edge : Stokes.OrientedEdge vertexCount} (member : edge ∈ patch.boundary) :
    edge.reverse ∈ patch.boundary ↔ edge.reverse ∈ (SewnPatch.originalEdges patch) := by
  constructor
  · intro reversed
    exact (EdgeReordering.mem_iff patch.incidence edge.reverse).mpr (Membership.mem_append.mpr (Or.inl reversed))
  · intro reversed
    rcases Membership.mem_append.mp ((EdgeReordering.mem_iff patch.incidence edge.reverse).mp reversed) with exposed |
      internal
    · exact exposed
    · have paired := pairedEdgeOccurrences_reverse_mem patch.seams internal
      rw [OrientedEdge.reverse_reverse] at paired
      exact ((List.Permutation.nodup_append_parts
        (List.Permutation.nodup (EdgeReordering.toPerm patch.incidence) unique)).2.2 edge member edge paired rfl).elim

end SewnPatch

namespace SewingForest.SinglePolygon

variable {vertexCount faceCount : Nat} {faces : Fin faceCount → Stokes.OrientedTriangle vertexCount}
  {forest : Sewing.SewingForest faces}

/-- The original occurrences of the single retained patch cover the complete triangle-edge bank.

The forest coverage certificate retains its ordered patch occurrence lists. Its single-polygon equation specializes that
coverage to the one retained patch without changing edge data. -/
theorem originalEdges_coverage (polygon : SewingForest.SinglePolygon forest) :
    List.Perm (SewnPatch.originalEdges polygon.patch) (Stokes.triangleEdgeOccurrences faces) := by
  have coverage := SewingForest.originalEdges_coverage forest
  rw [polygon.equation] at coverage
  change List.Perm (SewnPatch.originalEdges polygon.patch ++ []) _ at coverage
  rw [Append.append_nil] at coverage
  exact coverage

section
open Purelib.Topology.Surface.Cut.BoundaryPairs.SewingForest
/-- Unique global triangle incidence gives unique original occurrences in the single patch. -/
theorem originalEdges_unique (polygon : SewingForest.SinglePolygon forest) (unique : (Stokes.triangleEdgeOccurrences
  faces).Nodup) :
    (SewnPatch.originalEdges polygon.patch).Nodup :=
  List.Permutation.nodup (List.Permutation.symm (originalEdges_coverage polygon)) unique

/-- Every exposed edge of the single patch occurs in the original triangle bank. -/
theorem boundary_member (polygon : SewingForest.SinglePolygon forest) {edge : Stokes.OrientedEdge vertexCount}
    (member : edge ∈ polygon.patch.boundary) : edge ∈ Stokes.triangleEdgeOccurrences faces :=
  (List.Permutation.mem_iff (originalEdges_coverage polygon) edge).mp
    ((EdgeReordering.mem_iff polygon.patch.incidence edge).mpr (Membership.mem_append.mpr (Or.inl member)))

/-- Construct the complete pairing in the cut-vertex bank.

The retained vertex labels and cut boundary are passed directly to the pairing builder. The supplied nonloop certificate
for the triangle-edge bank proves nondegeneracy of those same projected occurrences. -/
@[expose] def edgePairing (polygon : SewingForest.SinglePolygon forest)
    (nonloop : ∀ edge ∈ Stokes.triangleEdgeOccurrences faces, edge.start ≠ edge.finish) :
    ProjectedEdgePairs.ProjectedEdgePairing polygon.patch.cut.vertexLabels polygon.patch.cut.boundary :=
  ProjectedEdgePairing.build _ _ (by
    intro edge member
    apply nonloop (OrientedEdge.map polygon.patch.cut.vertexLabels edge)
    apply (boundary_member polygon)
    have mapped := Map.mem_map_of_mem (f := OrientedEdge.map polygon.patch.cut.vertexLabels) member
    rw [polygon.patch.cut.boundary_eq] at mapped
    exact mapped)

end

open Purelib.Topology.Surface.Cut in
open Purelib.Topology.Surface.Cut.BoundaryPairs in
open Purelib.Topology.Surface.Cut.BoundaryPairs.SewingForest in
/-- Residual paired-cut occurrences are exactly the one-sided original mesh edges.

The supplied pairing may be constructed automatically or retained as checked data. Unique global incidence and the patch
coverage certificate identify the same input occurrences, while reversal membership distinguishes the residual mesh
boundary. -/
theorem boundary_iff (polygon : SewingForest.SinglePolygon forest) (unique : (Stokes.triangleEdgeOccurrences
  faces).Nodup)
    (pairing : ProjectedEdgePairs.ProjectedEdgePairing polygon.patch.cut.vertexLabels polygon.patch.cut.boundary)
    (edge : Stokes.OrientedEdge vertexCount) :
    edge ∈ pairing.boundary.map (OrientedEdge.map polygon.patch.cut.vertexLabels) ↔
      edge ∈ Stokes.triangleEdgeOccurrences faces ∧ edge.reverse ∉ Stokes.triangleEdgeOccurrences faces := by
  have patchUnique := (originalEdges_unique polygon) unique
  have cutUnique : (polygon.patch.cut.boundary.map (OrientedEdge.map polygon.patch.cut.vertexLabels)).Nodup := by
    rw [polygon.patch.cut.boundary_eq]
    exact SewnPatch.boundary_unique polygon.patch patchUnique
  have classified := ProjectedEdgePairing.boundary_iff pairing cutUnique edge
  rw [polygon.patch.cut.boundary_eq] at classified
  have covers := List.Permutation.mem_iff (originalEdges_coverage polygon)
  constructor
  · intro boundary
    rcases classified.mp boundary with ⟨member, missing⟩
    exact ⟨(boundary_member polygon) member, fun reversed => missing
      ((SewnPatch.reverse_mem_boundary_iff polygon.patch patchUnique member).mpr ((covers edge.reverse).mpr reversed))⟩
  · rintro ⟨member, missing⟩
    apply classified.mpr
    have original := (covers edge).mpr member
    rcases Membership.mem_append.mp ((EdgeReordering.mem_iff polygon.patch.incidence edge).mp original) with exposed |
      internal
    · exact ⟨exposed, fun reversed => missing ((boundary_member polygon) reversed)⟩
    · exact (missing ((covers edge.reverse).mp ((EdgeReordering.mem_iff polygon.patch.incidence edge.reverse).mpr
        (Membership.mem_append.mpr (Or.inr (pairedEdgeOccurrences_reverse_mem polygon.patch.seams
          internal)))))).elim

end SewingForest.SinglePolygon

end Purelib.Topology.Surface.Cut.BoundaryPairs
