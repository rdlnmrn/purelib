module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Append
import Purelib.Data.List.Membership
import Purelib.Data.List.Flatten
import Purelib.Data.List.OfFn.Basic

import Purelib.Data.List.Permutation
import Purelib.Topology.Polygon.Stokes
public import Purelib.Topology.Surface.Sewing.SewingForest
import Purelib.Topology.Surface.Sewing.SewingProjection
import Purelib.Topology.Surface.Sewing.SewingTree
public import Purelib.Topology.Mesh.DualWalks
import Purelib.Topology.Surface.Cut.Patch

public section

/-!
# One cut polygon from finite face connectivity

Oriented edge occurrences must be unique in the original mesh.  Under this
finite manifold-incidence condition, a shared edge between different patches
cannot have disappeared into an internal seam.  Maximality therefore makes
each patch closed under dual walks, and connectedness leaves exactly one.
The hypotheses here are internal geometric obligations, not a replacement
for constructing them on the actual lifted grid.
-/

namespace Purelib.Topology.Surface.Sewing.SewingConnected

open Purelib.Data

open Purelib.Data.List

open Purelib.Topology.Mesh

open Purelib.Topology.Polygon

open Purelib.Topology.Polygon.Stokes

open Purelib.Topology.Surface.Sewing

open Purelib.Topology.Surface.Sewing.SewingForest
open _root_.Purelib.Topology.Surface.Sewing renaming SewingForest -> SewingForest

open Purelib.Topology.Surface.Sewing.SewingProjection

open Purelib.Topology.Surface.Sewing.SewingTree
open _root_.Purelib.Topology.Surface.Sewing renaming SewingTree -> SewingTree

open Purelib.Topology.Polygon.Stokes (OrientedEdge OrientedTriangle pairedEdgeOccurrences triangleEdgeOccurrences)
open _root_.Purelib.Topology.Surface.Sewing (SewingTree)
open _root_.Purelib.Topology.Surface.Sewing.SewingTree (SewnPatch)
open _root_.Purelib.Topology.Surface.Sewing (SewingForest)
open Purelib.Topology.Mesh.DualWalks (DualConnection)

variable {vertexCount faceCount : Nat} {faces : Fin faceCount → Stokes.OrientedTriangle vertexCount}

namespace SewingTree

/-- Read the first original face leaf of a retained nonempty sewing tree. -/
@[expose] def firstFace : SewingTree faceCount → Fin faceCount
  | .leaf index => index
  | .join first _ _ _ => (firstFace first)

/-- The first original face belongs to the retained tree's leaf list.

A leaf supplies its stored index. A join retains that same first-child leaf
inside the concatenation with its second child's leaf list. -/
theorem firstFace_mem : (tree : SewingTree faceCount) → (firstFace tree) ∈ tree.leaves
  | .leaf _ => List.mem_cons_self
  | .join first _ _ _ => Membership.mem_append.mpr (Or.inl
    (firstFace_mem first))

end SewingTree

/-- Every retained seam occurrence has its reverse in the same paired occurrence bank.

The paired list retains each original seam followed by its reverse. Structural
recursion transports membership in that exact ordered occurrence bank. -/
private theorem paired_reverse_mem {count : Nat} {edge : Stokes.OrientedEdge count} :
    (seams : List (Stokes.OrientedEdge count)) → edge ∈ Stokes.pairedEdgeOccurrences seams → edge.reverse ∈
      Stokes.pairedEdgeOccurrences seams
  | [], member => (List.not_mem_nil member).elim
  | first :: remaining, member => by
      rcases Membership.mem_cons.mp member with same | member
      · cases same
        exact List.mem_cons_of_mem _ List.mem_cons_self
      · rcases Membership.mem_cons.mp member with same | member
        · cases same
          rw [OrientedEdge.reverse_reverse]
          exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
            (paired_reverse_mem remaining member))

namespace SewnPatch

/-- Expand the original face-index occurrences into their ordered triangle boundary edges. -/
@[expose] def originalEdges (patch : SewingTree.SewnPatch faces) : List (Stokes.OrientedEdge vertexCount) :=
  patch.faceIndices.flatMap fun index => (faces index).boundary

/-- The retained tree's first face belongs to the original patch face list. -/
theorem firstFace_mem (patch : SewingTree.SewnPatch faces) : (SewingConnected.SewingTree.firstFace patch.tree) ∈
  patch.faceIndices := by
  rw [patch.faceIndices_eq]
  exact (SewingConnected.SewingTree.firstFace_mem patch.tree)

/-- An edge of any included original face belongs to the patch's original incidence list. -/
theorem original_edge_mem (patch : SewingTree.SewnPatch faces) {index : Fin faceCount} (faceMember : index ∈
  patch.faceIndices)
    {edge : Stokes.OrientedEdge vertexCount} (edgeMember : edge ∈ (faces index).boundary) : edge ∈
      (originalEdges patch) :=
  Flatten.mem_flatMap.mpr ⟨index, faceMember, edgeMember⟩

/-- An original occurrence is either still exposed, or its reverse already belongs to the same patch through one of that
patch's selected seams.

The retained incidence reordering places occurrences in the boundary or paired
seam bank. Every internal seam retains both orientations. -/
theorem exposed_or_reverse (patch : SewingTree.SewnPatch faces) {edge : Stokes.OrientedEdge vertexCount} (member : edge
  ∈ (originalEdges patch)) :
    edge ∈ patch.boundary ∨ edge.reverse ∈ (originalEdges patch) := by
  rcases Membership.mem_append.mp ((EdgeReordering.mem_iff patch.incidence edge).mp member) with exposed | internal
  · exact Or.inl exposed
  · exact Or.inr ((EdgeReordering.mem_iff patch.incidence edge.reverse).mpr
      (Membership.mem_append.mpr (Or.inr (paired_reverse_mem patch.seams internal))))

/-- Distinct patches with disjoint original incidence and no exposed seam cannot share a dual step. -/
theorem no_dual_step (first second : SewingTree.SewnPatch faces) (noSeam : (SewnPatch.NoSeam first second))
    (disjoint : ∀ edge ∈ (originalEdges first), edge ∉ (originalEdges second))
    {edge : Stokes.OrientedEdge vertexCount} (firstMember : edge ∈ (originalEdges first))
    (secondMember : edge.reverse ∈ (originalEdges second)) : False := by
  rcases (exposed_or_reverse first) firstMember with firstExposed | firstInternal
  · rcases (exposed_or_reverse second) secondMember with secondExposed | secondInternal
    · exact noSeam edge firstExposed secondExposed
    · rw [OrientedEdge.reverse_reverse] at secondInternal
      exact disjoint edge firstMember secondInternal
  · exact disjoint edge.reverse firstInternal secondMember

end SewnPatch

namespace SewingForest

/-- Flattening original patch incidences agrees with expanding their complete retained face-index list.

Each stored patch supplies its own ordered face occurrences. Concatenating their
edge fibers preserves the same occurrences and their original order. -/
private theorem originalEdges_flatMap : (patches : List (SewingTree.SewnPatch faces)) →
    patches.flatMap SewingConnected.SewnPatch.originalEdges = (patches.flatMap SewnPatch.faceIndices).flatMap (fun index
      => (faces index).boundary)
  | [] => rfl
  | first :: remaining => by
      change SewingConnected.SewnPatch.originalEdges first ++
        remaining.flatMap SewingConnected.SewnPatch.originalEdges =
          (first.faceIndices ++ remaining.flatMap SewnPatch.faceIndices).flatMap
            (fun index => (faces index).boundary)
      rw [Flatten.flatMap_append]
      exact congrArg (List.append (SewingConnected.SewnPatch.originalEdges first))
        (originalEdges_flatMap remaining)

/-- The forest's original incidences cover all original triangle-edge occurrences exactly up to permutation.

The checked face-index coverage transports each original triangle boundary.
Flattening the retained lists preserves their actual repeated edge occurrences. -/
theorem originalEdges_coverage (forest : SewingForest faces) :
    List.Perm (forest.patches.flatMap SewingConnected.SewnPatch.originalEdges) (Stokes.triangleEdgeOccurrences faces) :=
      by
  have mapped : (List.ofFn (fun index : Fin faceCount => index)).map faces = List.ofFn faces := OfFn.Basic.map_ofFn
  have listed : (List.ofFn (fun index : Fin faceCount => index)).flatMap (fun index => (faces index).boundary) =
    Stokes.triangleEdgeOccurrences faces := by
    unfold Stokes.triangleEdgeOccurrences
    rw [← mapped, Flatten.flatMap_map]
  exact (List.Perm.of_eq (originalEdges_flatMap forest.patches)).trans
    ((List.Permutation.flatMap (fun index => (faces index).boundary) forest.coverage).trans (.of_eq listed))

/-- Every original face belongs to the retained forest's face-index coverage. -/
theorem face_mem (forest : SewingForest faces) (index : Fin faceCount) : index ∈ forest.patches.flatMap
  SewnPatch.faceIndices :=
  (List.Permutation.mem_iff forest.coverage index).mpr (List.Permutation.ofFn_mem _ index)

/-- Unique original incidence and seam maximality keep every dual neighbor inside the first patch. -/
private theorem head_closed (head : SewingTree.SewnPatch faces) (remaining : List (SewingTree.SewnPatch faces))
    (covers : ∀ index : Fin faceCount, index ∈ head.faceIndices ++ remaining.flatMap SewnPatch.faceIndices)
    (unique : ((SewingConnected.SewnPatch.originalEdges head) ++ remaining.flatMap
      SewingConnected.SewnPatch.originalEdges).Nodup)
    (maximal : ∀ other ∈ remaining, (SewnPatch.NoSeam head other)) :
    ∀ {first next}, ∀ edge ∈ (faces first).boundary, edge.reverse ∈ (faces next).boundary →
      first ∈ head.faceIndices → next ∈ head.faceIndices := by
  intro first next edge firstEdge nextEdge firstMember
  by_cases nextMember : next ∈ head.faceIndices
  · exact nextMember
  · have inRemaining := (Membership.mem_append.mp (covers next)).resolve_left nextMember
    rcases Flatten.mem_flatMap.mp inRemaining with ⟨other, otherMember, nextFace⟩
    have disjoint : ∀ edge ∈ (SewingConnected.SewnPatch.originalEdges head), edge ∉
      (SewingConnected.SewnPatch.originalEdges other) := by
      intro shared inHead inOther
      exact (List.Permutation.nodup_append_parts unique).2.2 shared inHead shared
        (Flatten.mem_flatMap.mpr ⟨other, otherMember, inOther⟩) rfl
    exact ((SewingConnected.SewnPatch.no_dual_step head) other (maximal other otherMember) disjoint
      ((SewingConnected.SewnPatch.original_edge_mem head) firstMember firstEdge)
        ((SewingConnected.SewnPatch.original_edge_mem other) nextFace nextEdge)).elim

/-- Dual connectedness forces a maximal forest with unique original incidence to have no patches after its first. -/
theorem remaining_nil (head : SewingTree.SewnPatch faces) (remaining : List (SewingTree.SewnPatch faces))
    (covers : ∀ index : Fin faceCount, index ∈ head.faceIndices ++ remaining.flatMap SewnPatch.faceIndices)
    (unique : ((SewingConnected.SewnPatch.originalEdges head) ++ remaining.flatMap
      SewingConnected.SewnPatch.originalEdges).Nodup)
    (maximal : ∀ other ∈ remaining, (SewnPatch.NoSeam head other)) (connected : DualWalks.DualConnection faces) :
      remaining = [] := by
  cases remaining with
  | nil => rfl
  | cons other tail =>
      have remains := (connected.connect (SewingConnected.SewingTree.firstFace head.tree)
        (SewingConnected.SewingTree.firstFace other.tree)).preserves
        (fun index => index ∈ head.faceIndices) (head_closed head (other :: tail) covers unique maximal)
          (SewingConnected.SewnPatch.firstFace_mem head)
      let edge : Stokes.OrientedEdge vertexCount := ⟨(faces (SewingConnected.SewingTree.firstFace other.tree)).first,
        (faces (SewingConnected.SewingTree.firstFace other.tree)).second⟩
      have member : edge ∈ (faces (SewingConnected.SewingTree.firstFace other.tree)).boundary := List.mem_cons_self
      exact ((List.Permutation.nodup_append_parts unique).2.2 edge
        ((SewingConnected.SewnPatch.original_edge_mem head) remains member) edge
        (Flatten.mem_flatMap.mpr ⟨other, List.mem_cons_self, (SewingConnected.SewnPatch.original_edge_mem other)
          (SewingConnected.SewnPatch.firstFace_mem other) member⟩) rfl).elim

set_option genInjectivity false in
/-- A displayed sole patch, retaining the exact checked forest it came from.

The stored patch is the original forest's only entry. Its defining list equation
retains that same checked forest rather than replacing its ownership. -/
structure SinglePolygon (forest : SewingForest faces) where
  /-- Original retained sewn patch constituting the complete forest. -/ patch : SewingTree.SewnPatch faces
  /-- The exact original forest contains this patch and no others. -/ equation : forest.patches = [patch]

constructive_injectivity SinglePolygon

/-- This total construction applies equally to automatic and externally generated checked forests. It does not test for
a successful one-patch scan. -/
@[expose] def singlePolygon (forest : SewingForest faces) (unique : (Stokes.triangleEdgeOccurrences
  faces).Nodup)
    (connected : DualWalks.DualConnection faces) : SinglePolygon forest := by
  have allUnique := List.Permutation.nodup (List.Permutation.symm (originalEdges_coverage forest)) unique
  cases equation : forest.patches with
  | nil =>
      have member := (face_mem forest) connected.root
      rw [equation] at member
      exact (List.not_mem_nil member).elim
  | cons head remaining =>
      have covers : ∀ index : Fin faceCount, index ∈ head.faceIndices ++ remaining.flatMap SewnPatch.faceIndices := by
        intro index
        have member := (face_mem forest) index
        rw [equation] at member
        exact member
      rw [equation] at allUnique
      have maximal := forest.maximal
      rw [equation] at maximal
      have empty := remaining_nil head remaining covers allUnique (List.pairwise_cons.mp maximal).1
        connected
      exact ⟨head, equation.trans (congrArg (List.cons head) empty)⟩

/-- The retained sole polygon covers every original face exactly once.

Its one-entry forest equation transports the original coverage permutation
to the same stored patch and original bounded face-index enumeration. -/
theorem SinglePolygon.coverage {forest : SewingForest faces} (polygon : SinglePolygon forest)
  :
    List.Perm polygon.patch.faceIndices (List.ofFn fun index : Fin faceCount => index) := by
  have coverage := forest.coverage
  rw [polygon.equation] at coverage
  change List.Perm (polygon.patch.faceIndices ++ [])
    (List.ofFn fun index : Fin faceCount => index) at coverage
  rw [Append.append_nil] at coverage
  exact coverage

/-- The retained sole polygon has exactly the original number of face occurrences.

Its checked coverage permutation preserves list length. The original bounded
face enumeration has precisely the retained finite face count. -/
theorem SinglePolygon.face_count {forest : SewingForest faces} (polygon : SinglePolygon
  forest) :
    polygon.patch.faceIndices.length = faceCount :=
  (List.Permutation.length_eq polygon.coverage).trans OfFn.Basic.length_ofFn

/-- The actual cut polygon has two more boundary edges than original faces. -/
theorem SinglePolygon.boundaryCount {forest : SewingForest faces} (polygon : SinglePolygon
  forest) :
    polygon.patch.cut.boundary.length = faceCount + 2 := by
  rw [polygon.patch.cut.boundary_length, polygon.patch.boundary_length, polygon.face_count]

end SewingForest

end Purelib.Topology.Surface.Sewing.SewingConnected
