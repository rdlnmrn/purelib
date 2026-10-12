module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Membership
import Purelib.Data.List.Append
import Purelib.Data.List.Map
import Purelib.Data.List.Reverse
import Purelib.Data.List.Flatten
import Purelib.Data.List.OfFn.Basic

import Purelib.Topology.Mesh.EdgeCancellation
import Purelib.Topology.Polygon.Stokes
public import Purelib.Topology.Surface.Sewing.SewingTree
public import Purelib.Topology.Surface.Sewing.SewingSearch
public import Purelib.Data.List.Permutation
import Purelib.Data.Gaussian.Basic
import Purelib.Topology.Surface.Sewing.PolygonSewing
import Batteries.Logic
import Purelib.Tactic.QuotientFreeOmega
meta import Mathlib.Tactic.Linter.Lint

open Purelib.Data

open Purelib.Data.List

open Purelib.Topology.Mesh.EdgeCancellation
open _root_.Purelib.Topology.Mesh renaming EdgeCancellation -> EdgeCancellation

open Purelib.Topology.Polygon

open Purelib.Topology.Surface.Sewing

open Purelib.Topology.Surface.Sewing.SewingSearch

open Purelib.Topology.Surface.Sewing.SewingTree
open _root_.Purelib.Topology.Surface.Sewing renaming SewingTree -> SewingTree

public section

/-!
# Automatic maximal forests of sewn triangle polygons

Each merge joins two different patches along one checked seam.  The finite
patch count decreases, and the final forest has no sewable edge between
distinct patches.  Its face-index permutation covers every original face
exactly once.  A connectedness theorem is still needed to conclude that a
particular mesh produces one polygon; this constructor assumes no such fact.
-/

namespace Purelib.Topology.Surface.Sewing

open Purelib.Topology.Polygon.Stokes (EdgeReordering OrientedEdge OrientedTriangle PrimitivePoint edgeListArea
  edgeListArea_append edgeListArea_reordering triangleWedgeSum triangleWedgeSum_eq_edgeListArea)
open _root_.Purelib.Topology.Surface.Sewing (SewingTree)
open _root_.Purelib.Topology.Surface.Sewing.SewingTree (SewnPatch)
open Purelib.Topology.Surface.Sewing.SewingSearch (SeamSearch)

variable {vertexCount faceCount : Nat} {faces : Fin faceCount → Stokes.OrientedTriangle vertexCount}

namespace SewingForest.SewnPatch

/-- No exposed edge of the first original patch has its reverse in the second boundary. -/
@[expose] def NoSeam (first second : SewingTree.SewnPatch faces) : Prop :=
  ∀ edge ∈ first.boundary, edge.reverse ∉ second.boundary

end SewingForest.SewnPatch

namespace SewingForest

/-- Decide the absence of a seam by the exact finite boundary search. -/
instance (first second : SewingTree.SewnPatch faces) : Decidable (SewingForest.SewnPatch.NoSeam first second) :=
  match SeamSearch.find first.boundary second.boundary with
  | .absent missing => .isTrue missing
  | .found firstSplit secondSplit opposite => .isFalse (by
      intro missing
      have secondMember := secondSplit.edge_mem
      rw [opposite] at secondMember
      exact missing firstSplit.edge firstSplit.edge_mem secondMember)

end SewingForest

namespace SewingForest

set_option genInjectivity false in
/-- One checked merge of an original patch list preserving complete face coverage.

The retained output has exactly one fewer patch and a permutation certificate for the original face occurrences. -/
structure ForestMerge (patches : List (SewingTree.SewnPatch faces)) where
  /-- Cached patch list after the original selected seam merge. -/ remaining : List (SewingTree.SewnPatch faces)
  /-- The retained list contains exactly one fewer patch than the original input. -/ shorter : remaining.length + 1 =
    patches.length
  /-- The merge preserves every original face occurrence up to permutation. -/ coverage : List.Perm (patches.flatMap
    SewnPatch.faceIndices) (remaining.flatMap SewnPatch.faceIndices)

constructive_injectivity ForestMerge

end SewingForest

namespace SewingForest

set_option genInjectivity false in
/-- A checked merge partner for the first patch, or evidence that no remaining patch has a seam with it.

Success retains one selected merge of the supplied first patch and candidate list. Absence proves that each original
candidate boundary has no seam with the first patch. -/
inductive MateSearch (first : SewingTree.SewnPatch faces) (remaining : List (SewingTree.SewnPatch faces)) where
  /-- Certify that the first original patch has no seam with any remaining candidate. -/ | absent (missing : ∀ other ∈
    remaining, SewingForest.SewnPatch.NoSeam first other)
  /-- Retain one checked merge of the first patch with an original remaining candidate. -/ | found (merge :
    ForestMerge (first :: remaining))

constructive_injectivity MateSearch

end SewingForest

namespace SewingForest

/-- Search the original remaining patches for a seam with the supplied first patch.

A successful result retains the merged patch list; absence certifies every original candidate. -/
@[expose] def findMate (first : SewingTree.SewnPatch faces) : (remaining : List (SewingTree.SewnPatch faces)) →
  MateSearch first remaining
  | [] => .absent (fun _ member => (List.not_mem_nil member).elim)
  | second :: tail =>
      match SeamSearch.find first.boundary second.boundary with
      | .found firstSplit secondSplit opposite =>
          .found
            { remaining := first.sew second firstSplit secondSplit opposite :: tail
              shorter := rfl
              coverage := by
                change List.Perm (first.faceIndices ++ (second.faceIndices ++ tail.flatMap SewnPatch.faceIndices))
                  ((first.faceIndices ++ second.faceIndices) ++ tail.flatMap SewnPatch.faceIndices)
                rw [Append.append_assoc] }
      | .absent missing =>
          match findMate first tail with
          | .absent remaining => .absent (by
              intro other member
              rcases Membership.mem_cons.mp member with same | tailMember
              · cases same; exact missing
              · exact remaining other tailMember)
          | .found merge =>
              .found
                { remaining := second :: merge.remaining
                  shorter := by have shorter := merge.shorter; simp only [List.length_cons] at shorter ⊢; omega
                  coverage := by
                    have swapped : List.Perm (first :: second :: tail) (second :: first :: tail) := .swap _ _ _
                    exact (List.Permutation.flatMap SewnPatch.faceIndices swapped).trans
                      (merge.coverage.append_left second.faceIndices) }

end SewingForest

namespace SewingForest

set_option genInjectivity false in
/-- A checked merge of the original patch list, or its complete pairwise seam-maximality certificate.

A found result retains the selected complete-list transition and coverage witness. An absent result proves pairwise
seam-maximality of the same original patch bank. -/
inductive MergeSearch (patches : List (SewingTree.SewnPatch faces)) where
  /-- Certify pairwise absence of seams throughout the original patch list. -/ | absent (maximal : patches.Pairwise
    SewingForest.SewnPatch.NoSeam)
  /-- Retain one checked seam merge of the original patch list. -/ | found (merge : ForestMerge patches)

constructive_injectivity MergeSearch

end SewingForest

namespace SewingForest

/-- Search the original patch list for one seam merge while preserving exact face coverage. -/
@[expose] def findMerge : (patches : List (SewingTree.SewnPatch faces)) → MergeSearch patches
  | [] => .absent .nil
  | first :: remaining =>
      match findMate first remaining with
      | .found merge => .found merge
      | .absent missing =>
          match findMerge remaining with
          | .absent maximal => .absent (.cons missing maximal)
          | .found merge => .found
              { remaining := first :: merge.remaining
                shorter := by have shorter := merge.shorter; simp only [List.length_cons] at shorter ⊢; omega
                coverage := merge.coverage.append_left first.faceIndices }

end SewingForest

namespace SewingForest

set_option genInjectivity false in
/-- A retained seam-maximal patch list with the exact original face-occurrence coverage.

The cached output list is indexed by its original input bank. Its coverage and maximality certificates concern those
exact retained sewn patches and face occurrences. -/
structure NormalizedForest (original : List (SewingTree.SewnPatch faces)) where
  /-- Cached seam-maximal output patches. -/ patches : List (SewingTree.SewnPatch faces)
  /-- Output patches preserve the exact original face-occurrence multiset. -/ coverage : List.Perm (original.flatMap
    SewnPatch.faceIndices) (patches.flatMap SewnPatch.faceIndices)
  /-- No two retained output patches share a sewable exposed seam. -/ maximal : patches.Pairwise
    SewingForest.SewnPatch.NoSeam

constructive_injectivity NormalizedForest

end SewingForest

namespace SewingForest

/-- Repeatedly merge original patches within their certified finite patch-count bound.

Each merge reduces the retained list by one, and the returned forest certifies pairwise absence of seams and unchanged
face coverage. -/
@[expose] def normalizeFuel : (fuel : Nat) → (original : List (SewingTree.SewnPatch faces)) → original.length ≤ fuel →
  NormalizedForest original
  | 0, [], _ => ⟨[], .nil, .nil⟩
  | 0, _ :: _, impossible => (Nat.not_succ_le_zero _ impossible).elim
  | fuel + 1, original, bound =>
      match findMerge original with
      | .absent maximal => ⟨original, .refl _, maximal⟩
      | .found merge =>
          let remaining := normalizeFuel fuel merge.remaining (by
            have shorter := merge.shorter
            omega)
          ⟨remaining.patches, merge.coverage.trans remaining.coverage, remaining.maximal⟩

end SewingForest

set_option genInjectivity false in
/-- A complete triangle partition with a retained sewing tree per patch. The explicit permutation rules out missing or
duplicated face occurrences.

Its patch cache covers every original finite face exactly once by permutation. Pairwise seam-maximality refers to those
same retained patch boundaries. -/
structure SewingForest (faces : Fin faceCount → Stokes.OrientedTriangle vertexCount) where
  /-- Retained sewn patches covering the original finite face bank. -/ patches : List (SewingTree.SewnPatch faces)
  /-- The retained face-index occurrences permute the complete original index list. -/ coverage : List.Perm
    (patches.flatMap SewnPatch.faceIndices) (List.ofFn fun index : Fin faceCount => index)
  /-- Distinct retained patches have no sewable exposed seam. -/ maximal : patches.Pairwise
    SewingForest.SewnPatch.NoSeam

constructive_injectivity SewingForest

namespace SewingForest

/-- The initial triangle-patch list reads exactly the supplied original face indices. -/
theorem initial_indices (faces : Fin faceCount → Stokes.OrientedTriangle vertexCount) (indices : List (Fin faceCount)) :
    ((indices.map (SewnPatch.triangle faces)).flatMap SewnPatch.faceIndices) = indices := by
  induction indices with
  | nil => rfl
  | cons index tail ih => exact congrArg (List.cons index) ih

/-- At most one merge per initial face is needed. The bound is structural, not a successful-search premise or a Lean
elaboration resource override. -/
@[expose] def build (faces : Fin faceCount → Stokes.OrientedTriangle vertexCount) : SewingForest faces :=
  let original := (List.ofFn fun index : Fin faceCount => index).map (SewnPatch.triangle faces)
  let normalized := normalizeFuel original.length original (Nat.le_refl _)
  { patches := normalized.patches
    coverage := normalized.coverage.symm.trans (.of_eq (initial_indices faces _))
    maximal := normalized.maximal }

set_option genInjectivity false in
/-- Materialized results of exactly the supplied list of trees.

The cached patches are the checked results of the supplied original tree list. Their tree projection retains its exact
order without re-running replay. -/
structure ReplayedTrees (faces : Fin faceCount → Stokes.OrientedTriangle vertexCount) (trees : List
  (SewingTree faceCount)) where
  /-- Cached checked patches produced by the supplied original tree list. -/ patches : List (SewingTree.SewnPatch faces)
  /-- Reading each cached patch's tree recovers the exact supplied tree list. -/ source : patches.map SewnPatch.tree =
    trees

constructive_injectivity ReplayedTrees

set_option genInjectivity false in
/-- Locate a failed tree while retaining the already checked prefix. The equation identifies its exact position in the
supplied list.

The retained checked prefix, failed tree and unprocessed suffix reconstruct the original schedule. The typed replay
obstruction concerns that precise failed tree. -/
structure InvalidTreeList (faces : Fin faceCount → Stokes.OrientedTriangle vertexCount) (trees : List
  (SewingTree faceCount)) where
  /-- Already checked original tree prefix retained as cached patches. -/ before : List (SewingTree.SewnPatch faces)
  /-- Exact original tree at which replay failed. -/ tree : SewingTree faceCount
  /-- Unprocessed original tree suffix following the failure. -/ after : List (SewingTree faceCount)
  /-- The checked prefix, failed tree and remaining suffix reconstruct the original request. -/ source : trees =
    before.map SewnPatch.tree ++ tree :: after
  /-- Typed certificate of the failed original tree replay. -/ invalid : SewnPatch.InvalidReplay faces tree

constructive_injectivity InvalidTreeList

/-- Replay the supplied tree list once, retaining either all checked patches or the exact first failed tree and checked
prefix. -/
@[expose] def replayTrees (faces : Fin faceCount → Stokes.OrientedTriangle vertexCount) : (trees : List
  (SewingTree faceCount)) →
    Except (InvalidTreeList faces trees) (ReplayedTrees faces trees)
  | [] => .ok ⟨[], rfl⟩
  | tree :: trees =>
      match SewnPatch.replay faces tree with
      | .error invalid => .error ⟨[], tree, trees, rfl, invalid⟩
      | .ok first =>
          match replayTrees faces trees with
          | .error invalid => .error
              ⟨first.patch :: invalid.before, invalid.tree, invalid.after, by
                simpa only [List.map_cons, List.cons_append, first.tree_eq] using
                  congrArg (List.cons tree) invalid.source, invalid.invalid⟩
          | .ok remaining => .ok
              ⟨first.patch :: remaining.patches, congrArg₂ List.cons first.tree_eq remaining.source⟩

set_option genInjectivity false in
/-- Each rejection proves the failed condition of this supplied schedule. Coverage and maximality failures retain all
replayed patches, so diagnostics do not need to replay a large sewing tree again.

Each outcome retains the checked work and evidence of the violated replay, coverage or pairwise maximality condition. It
makes no global obstruction claim about other sewing schedules. -/
inductive Invalid (faces : Fin faceCount → Stokes.OrientedTriangle vertexCount) (trees : List (SewingTree
  faceCount)) where
  /-- Retain the failed tree and already checked prefix of the original schedule. -/ | replay (invalid :
    InvalidTreeList faces trees)
  /-- Retain all replayed patches and proof that their original face coverage is invalid. -/ | coverage (checked :
    ReplayedTrees faces trees)
      (invalid : List.Permutation.Invalid (checked.patches.flatMap SewnPatch.faceIndices)
        (List.ofFn fun index : Fin faceCount => index))
  /-- Retain all replayed patches and proof that the supplied forest is not seam-maximal. -/ | nonmaximal (checked :
    ReplayedTrees faces trees) (failed : ¬ checked.patches.Pairwise SewingForest.SewnPatch.NoSeam)

constructive_injectivity Invalid

/-- Generated trees are untrusted data. Every rejection carries evidence of invalid replay, incomplete/repeated
coverage, or a nonmaximal supplied forest. It does not claim that the mesh cannot be sewn. The independent canonical
`build` is total and needs no successful-check premise. -/
@[expose] def checkTrees (faces : Fin faceCount → Stokes.OrientedTriangle vertexCount) (trees : List
  (SewingTree faceCount)) :
    Except (Invalid faces trees) (SewingForest faces) :=
  match SewingForest.replayTrees faces trees with
  | .error invalid => .error (.replay invalid)
  | .ok checked =>
      match List.Permutation.certify (checked.patches.flatMap SewnPatch.faceIndices)
          (List.ofFn fun index : Fin faceCount => index) with
      | .error invalid => .error (.coverage checked invalid)
      | .ok coverage =>
          if maximal : checked.patches.Pairwise SewingForest.SewnPatch.NoSeam then
            .ok ⟨checked.patches, coverage.permutation, maximal⟩
          else .error (.nonmaximal checked maximal)

/-- Expand an original list permutation into a finite edge-occurrence reordering.

Structural permutation induction expands the same retained entry fibers on both sides. The resulting edge reordering
preserves repeated oriented occurrences and their full list order. -/
private theorem flatMap_reordering {Alpha : Type} (value : Alpha → List (Stokes.OrientedEdge vertexCount))
    {left right : List Alpha} (permutation : List.Perm left right) :
    Stokes.EdgeReordering (left.flatMap value) (right.flatMap value) := by
  induction permutation with
  | nil => exact .nil
  | cons head tail ih => exact EdgeReordering.append_left (value head) ih
  | swap first second remaining =>
      simpa only [Flatten.flatMap_cons, Append.append_assoc] using
        EdgeReordering.append_swap (value second) (value first) (remaining.flatMap value)
  | trans first second ihFirst ihSecond => exact ihFirst.trans ihSecond

/-- The complete retained patch-boundary area equals the original indexed face-boundary area.

Each retained patch carries its own boundary-area certificate. Finite concatenation composes those exact cached
boundaries and original indexed face occurrences. -/
private theorem patches_area (primitive : Fin vertexCount → Stokes.PrimitivePoint) : (patches : List
  (SewingTree.SewnPatch faces)) →
    Stokes.edgeListArea primitive (patches.flatMap SewnPatch.boundary) =
      Stokes.edgeListArea primitive ((patches.flatMap SewnPatch.faceIndices).flatMap fun index => (faces
        index).boundary)
  | [] => rfl
  | patch :: patches => by
      simp only [Flatten.flatMap_cons, Flatten.flatMap_append]
      rw [Stokes.edgeListArea_append, Stokes.edgeListArea_append, patch.boundary_area,
        patches_area primitive patches]

/-- Exact finite Stokes survives the selected tree sewings. The right side includes unglued cut occurrences, not just
the mesh's outer boundary.

The retained forest coverage permutation orders every original face occurrence exactly once. Reordering preserves the
complete patch-boundary area, including all unglued cut occurrences. -/
theorem boundary_area (forest : SewingForest faces) (primitive : Fin vertexCount → Stokes.PrimitivePoint) :
    Stokes.edgeListArea primitive (forest.patches.flatMap SewnPatch.boundary) = Stokes.triangleWedgeSum primitive faces
      := by
  rw [SewingForest.patches_area, Stokes.triangleWedgeSum_eq_edgeListArea,
    Stokes.edgeListArea_reordering primitive (flatMap_reordering (fun index => (faces index).boundary)
      forest.coverage)]
  have mapped : (List.ofFn (fun index : Fin faceCount => index)).map faces = List.ofFn faces :=
    OfFn.Basic.map_ofFn
  have listed : (List.ofFn (fun index : Fin faceCount => index)).flatMap (fun index => (faces index).boundary) =
      (List.ofFn faces).flatMap OrientedTriangle.boundary := by
    rw [← mapped, Flatten.flatMap_map]
  exact congrArg (Stokes.edgeListArea primitive) listed

end SewingForest

end Purelib.Topology.Surface.Sewing
