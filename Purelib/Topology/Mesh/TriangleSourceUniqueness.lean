module
import Purelib.Data.Fin
import Purelib.Data.List.Flatten
import Purelib.Data.List.Map
import Purelib.Data.List.OfFn.Basic

import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.SewnPrimitiveBoundary
import Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces
import Purelib.Topology.Surface.Sewing.VertexSewing
public import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Data.List.Permutation

/-!
# Unique positive source occurrences in a finite triangle mesh

The incidence condition distinguishes original oriented occurrences, not
reversed shared edges. Injective triangle corners then identify the full
source data, even for generated owners with independently supplied corners.
-/

public section

namespace Purelib.Topology.Mesh.TriangleSourceUniqueness

open Purelib.Data
open Purelib.Data.List
open Purelib.Topology.Mesh
open Purelib.Topology.Polygon
open Purelib.Topology.Polygon.Stokes
open Purelib.Topology.Surface.Cut
open Purelib.Topology.Surface.Sewing
open Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
open Purelib.Topology.Surface.Sewing.VertexSewing

open Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts (SourceEdge)
open Purelib.Topology.Surface.Cut.Patch (CutPatch)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveBoundary (TriangleEdgeOwner)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces (corner corner_map)

open Purelib.Topology.Polygon.Stokes (OrientedEdge OrientedTriangle triangleEdgeOccurrences)

variable {vertexCount faceCount : Nat} {faces : Fin faceCount → Stokes.OrientedTriangle vertexCount}

/-- An edge in a retained face boundary occurs in the complete triangle edge list. -/
private theorem boundary_member (faces : Fin faceCount → Stokes.OrientedTriangle vertexCount)
    (index : Fin faceCount) {edge : Stokes.OrientedEdge vertexCount} (member : edge ∈ (faces index).boundary) :
    edge ∈ Stokes.triangleEdgeOccurrences faces :=
  Flatten.mem_flatMap.mpr
    ⟨faces index, List.Permutation.ofFn_mem faces index, member⟩

/-- A duplicate-free oriented edge list identifies the face containing a shared edge.

If the same oriented edge occurs in two indexed face boundaries, their bounded face indices are equal. -/
private theorem same_face : ∀ {faceCount : Nat} (faces : Fin faceCount → Stokes.OrientedTriangle vertexCount),
    (Stokes.triangleEdgeOccurrences faces).Nodup → ∀ (first last : Fin faceCount) (edge : Stokes.OrientedEdge
      vertexCount),
      edge ∈ (faces first).boundary → edge ∈ (faces last).boundary → first = last
  | 0, _, _, first, _, _, _, _ => Fin.elim0 first
  | count + 1, faces, unique, first, last, edge, firstMember, lastMember => by
      have literalZero : (0 : Fin (count + 1)) = ⟨0, Nat.zero_lt_succ count⟩ := by
        apply Fin.ext
        rfl
      have parts : ((faces (⟨0, Nat.zero_lt_succ count⟩ : Fin (count + 1))).boundary ++ Stokes.triangleEdgeOccurrences
        (fun index : Fin count => faces index.succ)).Nodup := by
        simpa only [Stokes.triangleEdgeOccurrences, OfFn.Basic.ofFn_succ, Flatten.flatMap_cons, literalZero, -eq_self]
          using unique
      have split := Permutation.nodup_append_parts parts
      revert firstMember lastMember
      refine Purelib.Data.Fin.cases_induction ?_ (fun first => ?_) first
      · refine Purelib.Data.Fin.cases_induction ?_ (fun last => ?_) last
        · intro _ _; rfl
        · intro firstMember lastMember
          exact (split.2.2 edge firstMember edge
            (TriangleSourceUniqueness.boundary_member (fun index : Fin count => faces index.succ) last lastMember)
              rfl).elim
      · refine Purelib.Data.Fin.cases_induction ?_ (fun last => ?_) last
        · intro firstMember lastMember
          exact (split.2.2 edge lastMember edge
            (TriangleSourceUniqueness.boundary_member (fun index : Fin count => faces index.succ) first firstMember)
              rfl).elim
        · intro firstMember lastMember
          exact congrArg Fin.succ (Purelib.Topology.Mesh.TriangleSourceUniqueness.same_face _ split.2.1 first last edge
            firstMember lastMember)

namespace SourceEdge

/-- Positive means an actual oriented occurrence of its own source face. -/
@[expose] def Positive (edge : SewnPrimitiveContacts.SourceEdge faceCount) (faces : Fin faceCount →
  Stokes.OrientedTriangle vertexCount) : Prop :=
  edge.project faces ∈ (faces edge.source).boundary

/-- Decide whether a retained source edge is a positive occurrence of its own face. -/
instance (edge : SewnPrimitiveContacts.SourceEdge faceCount) (faces : Fin faceCount → Stokes.OrientedTriangle
  vertexCount) : Decidable (SourceEdge.Positive edge faces) :=
  inferInstanceAs (Decidable (edge.project faces ∈ (faces edge.source).boundary))

/-- A positive retained source edge projects to an edge of the complete triangle list. -/
theorem member {edge : SewnPrimitiveContacts.SourceEdge faceCount} (positive : SourceEdge.Positive edge faces) :
    edge.project faces ∈ Stokes.triangleEdgeOccurrences faces := TriangleSourceUniqueness.boundary_member faces
      edge.source positive

/-- Positive source edges with equal projections are identical under incidence and corner uniqueness.

The global oriented edge list must be duplicate-free, and each indexed triangle must have injective corner coordinates.
-/
theorem eq_of_project_eq (unique : (Stokes.triangleEdgeOccurrences faces).Nodup)
    (corners : ∀ index, Function.Injective (SewnPrimitiveFaces.corner (faces index)))
    {first last : SewnPrimitiveContacts.SourceEdge faceCount} (firstPositive : SourceEdge.Positive first faces)
      (lastPositive : SourceEdge.Positive last faces)
    (equal : first.project faces = last.project faces) : first = last := by
  have source := TriangleSourceUniqueness.same_face faces unique first.source last.source (first.project faces)
    firstPositive
    (equal.symm ▸ lastPositive)
  rcases first with ⟨firstSource, firstCorner, firstLast⟩
  rcases last with ⟨lastSource, lastCorner, lastLast⟩
  dsimp only at source
  subst lastSource
  have start := corners firstSource (congrArg OrientedEdge.start equal)
  have finish := corners firstSource (congrArg OrientedEdge.finish equal)
  cases start
  cases finish
  rfl

/-- Equal projected lists identify lists of positive source edges.

Duplicate-free oriented incidence and injective triangle corners recover each source occurrence, preserving list order.
-/
theorem list_eq_of_project_eq (unique : (Stokes.triangleEdgeOccurrences faces).Nodup)
    (corners : ∀ index, Function.Injective (SewnPrimitiveFaces.corner (faces index))) :
    ∀ (first last : List (SewnPrimitiveContacts.SourceEdge faceCount)),
      (∀ source ∈ first, SourceEdge.Positive source faces) → (∀ source ∈ last, SourceEdge.Positive source faces) →
      first.map (fun source => source.project faces) = last.map (fun source => source.project faces) → first = last
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, equal => by cases equal
  | _ :: _, [], _, _, equal => by cases equal
  | first :: rest, last :: remaining, firstPositive, lastPositive, equal => by
      have parts := List.cons.inj equal
      exact congrArg₂ List.cons
        (SourceEdge.eq_of_project_eq unique corners (firstPositive first List.mem_cons_self) (lastPositive last
          List.mem_cons_self) parts.1)
        (Purelib.Topology.Mesh.TriangleSourceUniqueness.SourceEdge.list_eq_of_project_eq unique corners rest remaining
          (fun source member => firstPositive source (List.mem_cons_of_mem _ member))
          (fun source member => lastPositive source (List.mem_cons_of_mem _ member)) parts.2)

end SourceEdge

variable {indices : List (Fin faceCount)} {boundary : List (Stokes.OrientedEdge vertexCount)}
  {patch : Patch.CutPatch faces indices boundary} {edge : Stokes.OrientedEdge patch.count}

/-- A retained triangle boundary owner determines a positive original source occurrence.

The patch triangle equations transport its stored boundary membership to the indexed source face. -/
theorem TriangleEdgeOwner.sourceEdge_positive (owner : SewnPrimitiveBoundary.TriangleEdgeOwner patch.triangles edge) :
    SourceEdge.Positive (TriangleEdgeOwner.sourceEdge owner) faces := by
  have triangle := List.getElem_of_eq patch.triangles_eq (i := owner.position.val)
    (by rw [Map.length_map]; exact owner.position.isLt)
  have sourceBound : owner.position.val < indices.length := by
    rewrite [← patch.triangles_length]
    exact owner.position.isLt
  rewrite [Map.getElem_map (OrientedTriangle.map patch.vertexLabels) patch.triangles
    owner.position.val owner.position.isLt (by rewrite [Map.length_map]; exact owner.position.isLt),
    Map.getElem_map faces indices owner.position.val sourceBound
      (by rewrite [Map.length_map]; exact sourceBound)] at triangle
  change (TriangleEdgeOwner.sourceEdge owner).project faces ∈ (faces _).boundary
  rw [TriangleEdgeOwner.sourceEdge_project owner]
  dsimp only [TriangleEdgeOwner.sourceEdge]
  rw [← triangle, OrientedTriangle.boundary_map]
  exact Map.mem_map_of_mem owner.boundary_mem

end Purelib.Topology.Mesh.TriangleSourceUniqueness

end
