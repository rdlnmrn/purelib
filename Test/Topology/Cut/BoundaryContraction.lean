module
import Purelib.Data.Vector.Basic
import Purelib.Data.List.Membership
import Purelib.Topology.Chain.PathBoundary

public import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Boundary.BoundaryContraction
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Sewing.SimpleBoundaryCycles
import Purelib.Topology.Surface.Word.PairedWord
import Purelib.Topology.Surface.Word.ProjectedEdgePairs
import Purelib.Topology.Surface.Word.Vertices
import Purelib.Topology.Surface.Boundary.BoundaryContractionIndices
import Purelib.Topology.Surface.Cut.ContractedWord
import Purelib.Topology.Surface.Cut.VertexReading
import Purelib.Tactic.QuotientFreeOmega

open Purelib

open Purelib.Topology.Chain

open Purelib.Topology.Polygon

open Purelib.Topology.Polygon.Stokes

open Purelib.Topology.Surface.Boundary

open Purelib.Topology.Surface.Boundary.BoundaryContraction
open _root_.Purelib.Topology.Surface.Boundary renaming BoundaryContraction -> BoundaryContraction

open Purelib.Topology.Surface.Boundary.BoundaryContractionIndices

open Purelib.Topology.Surface.Cut.BoundaryWord

open Purelib.Topology.Surface.Sewing

open Purelib.Topology.Surface.Word

open Purelib.Topology.Surface.Word.PairedWord

open Purelib.Topology.Surface.Word.ProjectedEdgePairs

@[expose] public section

/-!
# Exact regressions for physical boundary contraction

Two disjoint triangles must remain distinct after contraction. Interior
vertices survive, unused cache slots are excluded, and a cut annulus keeps
two vertices in its cancelling paired word. These are small kernel checks
of the executable constructors, independent of the generic count proofs.
-/

namespace Test.Topology.Cut.BoundaryContraction

open Purelib.Topology.Surface.Sewing.SimpleBoundaryCycles
open Purelib.Topology.Surface.Cut.ContractedWord
open Purelib.Topology.Surface.Cut.VertexReading
open Purelib.Topology.Polygon.Stokes (OrientedEdge)

/-- Two disjoint triangular boundary cycles in a nine-vertex ambient type. -/
private def cycles : List (List (Stokes.OrientedEdge 9)) :=
  [[⟨0, 1⟩, ⟨1, 2⟩, ⟨2, 0⟩], [⟨3, 4⟩, ⟨4, 5⟩, ⟨5, 3⟩]]

/-- Each of the two triangular boundary cycles closes at its original anchor. -/
private theorem closed : ∀ cycle ∈ cycles, ∃ anchor,
    PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish cycle anchor anchor := by
  intro cycle member
  simp only [cycles, -eq_self, -iff_self] at member
  cases member with
  | head => exact ⟨0, .cons (.cons (.cons (.nil _)))⟩
  | tail _ member =>
      cases member with
      | head => exact ⟨3, .cons (.cons (.cons (.nil _)))⟩
      | tail _ impossible => cases impossible

/-- The certified decomposition of the two disjoint triangular boundaries. -/
private def boundary : PolygonStokes.BoundaryCycleDecomposition BoundaryContraction.cycles.flatten where
  cycles := cycles
  closed := closed
  min_length := by
    intro cycle member
    cases member with
    | head => exact Nat.le_refl 3
    | tail _ member =>
        cases member with
        | head => exact Nat.le_refl 3
        | tail _ impossible => cases impossible
  sources_unique := by decide
  edge_iff := fun _ => ⟨fun member => ⟨member,
    SimpleBoundaryCycles.flatten_no_reverse closed (by decide) (by
      intro cycle member
      cases member with
      | head => exact Nat.le_refl 3
      | tail _ member =>
          cases member with
          | head => exact Nat.le_refl 3
          | tail _ impossible => cases impossible) member⟩, And.left⟩

/-- Contract each boundary component while retaining the two specified interior vertices. -/
private def withInterior : Topology.Surface.Boundary.BoundaryContraction boundary ([0, 1, 2, 3, 4,
  5, 6,
  7] : List (Fin 9)) :=
  BoundaryContraction.build boundary _ 7 (by decide) (by decide) (by
    intro vertex member
    have retained : vertex ∈ ([0, 1, 2, 3, 4, 5] : List (Fin 9)) := member
    exact (Purelib.Data.List.Membership.mem_append
      (left := ([0, 1, 2, 3, 4, 5] : List (Fin 9)))
      (right := [6, 7])).mpr (.inl retained))

/-- Dense indices for the boundary contraction and its retained interior vertices. -/
private def dense := Indexed.build withInterior

/-- The contraction lists its two interior vertices before the two boundary representatives. -/
example : BoundaryContraction.withInterior.representatives = [6, 7, 0, 3] := by decide
/-- Vertices on the same triangular boundary have the same normalized representative. -/
example : BoundaryContraction.withInterior.normalize 0 = BoundaryContraction.withInterior.normalize 2 := by decide
/-- Vertices on distinct triangular boundaries have distinct normalized representatives. -/
example : BoundaryContraction.withInterior.normalize 0 ≠ BoundaryContraction.withInterior.normalize 3 := by decide
/-- The two interior vertices remain distinct after contraction. -/
example : BoundaryContraction.withInterior.normalize 6 ≠ BoundaryContraction.withInterior.normalize 7 := by decide
/-- An unused ambient vertex is unchanged and excluded from the representative list. -/
example : BoundaryContraction.withInterior.normalize 8 = 8 ∧ 8 ∉ withInterior.representatives := by decide
/-- Dense projection identifies each boundary component and separates the two components. -/
example : BoundaryContraction.dense.projection 0 = BoundaryContraction.dense.projection 2 ∧
  BoundaryContraction.dense.projection 0 ≠ BoundaryContraction.dense.projection 3 := by decide
/-- Dense projection separates the two retained interior vertices. -/
example : BoundaryContraction.dense.projection 6 ≠ BoundaryContraction.dense.projection 7 := by decide
/-- Dense projection sends each enumerated representative to its own list index. -/
example : ∀ index : Fin BoundaryContraction.withInterior.representatives.length,
    BoundaryContraction.dense.projection BoundaryContraction.withInterior.representatives[index.val] = index := by
      decide

/-- An integer assignment constant on each boundary component and distinct on the interior vertices. -/
private def values (vertex : Fin 9) : Int := if vertex.val < 3 then 11 else if vertex.val < 6 then 23 else vertex.val +
  31

/-- Factoring the componentwise constant assignment preserves every retained vertex value. -/
example : ∀ vertex ∈ ([0, 1, 2, 3, 4, 5, 6, 7] : List (Fin 9)),
    BoundaryContraction.dense.factor values (BoundaryContraction.dense.projection vertex) =
      values vertex := by decide

/-- Contract the two annular boundary components without adding interior vertices. -/
private def annulusVertices : Topology.Surface.Boundary.BoundaryContraction boundary ([0, 1, 2, 3,
  4, 5] :
  List (Fin 9)) :=
  BoundaryContraction.build boundary _ 0 (by decide) (by decide) (by
    intro vertex member
    exact member)

/-- Dense indices for the two retained annular boundary representatives. -/
private def annulusIndices := Indexed.build annulusVertices

/-- The eight-edge polygon obtained by cutting the annular example. -/
private def polygon : List (Stokes.OrientedEdge 8) :=
  [⟨0, 1⟩, ⟨1, 2⟩, ⟨2, 3⟩, ⟨3, 4⟩, ⟨4, 5⟩, ⟨5, 6⟩, ⟨6, 7⟩, ⟨7, 0⟩]

/-- The original boundary labels of the eight polygon vertices. -/
private def labels : Data.Vector (Fin 9) 8 :=
  .cons 0 (.cons 1 (.cons 2 (.cons 0 (.cons 3 (.cons 4 (.cons 5 (.cons 3 .nil)))))))

/-- The checked pairing of polygon edges under the retained vertex labels. -/
private def pairing : ProjectedEdgePairs.ProjectedEdgePairing labels polygon :=
  ProjectedEdgePairing.build labels polygon (by decide)

/-- The contracted annular word with two distinct endpoint vertices. -/
private def annulusWord : Vertices.WordVertexRealization (CutBoundaryWord.pairedLetters
  (ProjectedEdgePairing.boundaryWord pairing)) annulusVertices.representatives.length :=
  ProjectedEdgePairing.contractedWord pairing BoundaryContraction.annulusIndices.projection (by
    intro edge member
    have retained : edge ∈ ([⟨0, 1⟩, ⟨1, 2⟩, ⟨2, 3⟩, ⟨4, 5⟩, ⟨5, 6⟩, ⟨6, 7⟩] : List (Stokes.OrientedEdge 8)) := member
    cases retained with
    | head => decide
    | tail _ member =>
        cases member with
        | head => decide
        | tail _ member =>
            cases member with
            | head => decide
            | tail _ member =>
                cases member with
                | head => decide
                | tail _ member =>
                    cases member with
                    | head => decide
                    | tail _ member =>
                        cases member with
                        | head => decide
                        | tail _ impossible => cases impossible) 0
    (.cons (.cons (.cons (.cons (.cons (.cons (.cons (.cons (.nil _)))))))))

/-- The alphabet entry of the annular cut edge. -/
private def cutIndex : Fin (ProjectedEdgePairing.boundaryWord pairing).alphabet.count := ⟨6, by
  decide⟩

/-- The annular paired word consists of the cut edge in its two orientations. -/
example : (CutBoundaryWord.pairedLetters (ProjectedEdgePairing.boundaryWord pairing)) = [⟨cutIndex,
  false⟩, ⟨cutIndex, true⟩] := by decide
/-- The annular contraction has the two original boundary representatives. -/
example : BoundaryContraction.annulusVertices.representatives = [0, 3] := by decide
/-- The cut edge joins the two distinct dense annular vertices. -/
example : BoundaryContraction.annulusWord.edges cutIndex = ⟨⟨0, by decide⟩, ⟨1, by decide⟩⟩ := by
  decide
/-- The contracted cut edge is not a loop. -/
example : (BoundaryContraction.annulusWord.edges cutIndex).start ≠
  (BoundaryContraction.annulusWord.edges cutIndex).finish := by decide
/-- The contracted annular word retains its initial anchor. -/
example : BoundaryContraction.annulusWord.anchor.val = 0 := by decide

/-- Recover the annular polygon vertices from the contracted word and its anchor. -/
private def annulusReading := CutVertexReading.build (ProjectedEdgePairing.boundaryWord pairing)
  annulusWord 0
  (.cons (.cons (.cons (.cons (.cons (.cons (.cons (.cons (.nil _))))))))) (by decide)

/-- Reading the annular word assigns four polygon vertices to each boundary component. -/
example : List.ofFn (fun index : Fin 8 => (BoundaryContraction.annulusReading.values index).val) = [0, 0, 0, 0, 1, 1, 1,
  1] := by decide

/-- Translate both contracted word vertices by one in a three-vertex ambient type. -/
private def shiftedWord := BoundaryContraction.annulusWord.map (fun index =>
  (⟨index.val + 1, by have bound : index.val < 2 := index.isLt; omega0⟩ : Fin 3))

/-- Recover polygon vertices using the translated word and its retained anchor. -/
private def shiftedReading := CutVertexReading.build (ProjectedEdgePairing.boundaryWord pairing)
  shiftedWord 0
  (.cons (.cons (.cons (.cons (.cons (.cons (.cons (.cons (.nil _))))))))) (by decide)

/-- The backward reading respects the supplied assignment, including its anchor; it does not silently replace it by
canonical vertex numbers. -/
example : List.ofFn (fun index : Fin 8 => (BoundaryContraction.shiftedReading.values index).val) = [1, 1, 1, 1, 2, 2, 2,
  2] := by decide

end Test.Topology.Cut.BoundaryContraction
