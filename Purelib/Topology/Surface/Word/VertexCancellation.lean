module
public import Purelib.Data.List.Membership
import Purelib.Data.Nat.Subtraction
import Purelib.Data.Vector.Basic

import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.PolygonSewing
import Purelib.Topology.Surface.Sewing.VertexSewing
import Purelib.Topology.Surface.Word.Pairing
import Purelib.Topology.Surface.Word.Selection
import Purelib.Topology.Surface.Word.SignedWord
import Purelib.Topology.Surface.Word.Surgery
public import Purelib.Topology.Surface.Word.VertexRotation
import Purelib.Topology.Surface.Word.Vertices
import Purelib.Topology.Surface.Chord.WordVertexTrace
public import Purelib.Topology.Surface.Word.ZeroReduction
import Purelib.Tactic.QuotientFreeOmega

/-!
# The exact vertex tree of a terminal cancellation

Two recursively constructed vertex banks remain disjoint and are joined by
the displayed cancelling edge. This gives one more vertex than cancelling
pairs, together with coverage and executable universal factorization.
-/

public section

namespace Purelib.Topology.Surface.Word.VertexCancellation

open Purelib.Data.List
open Purelib.Data.Nat

open Purelib
open Purelib.Topology.Polygon
open Purelib.Topology.Polygon.Stokes
open Purelib.Topology.Surface.Sewing.PolygonSewing
open Purelib.Topology.Surface.Sewing.VertexSewing
open Purelib.Topology.Surface.Word
open Purelib.Topology.Surface.Word.Selection
open Purelib.Topology.Surface.Word.SignedWord
open Purelib.Topology.Surface.Word.Surgery
open Purelib.Topology.Surface.Word.VertexRotation
open Purelib.Topology.Surface.Word.Vertices
open Purelib.Topology.Surface.Word.ZeroReduction

open Purelib.Topology.Surface.Word.SignedWord (SignedGenerator)
open Purelib.Topology.Surface.Word.Surgery (IntegralWordSignature)
open Purelib.Topology.Surface.Word.NormalForm (WordSurgeryTrace)
open Purelib.Topology.Surface.Word.Vertices (WordVertexModel WordVertexRealization)
open Purelib.Topology.Surface.Word.ZeroReduction (WordCancellation)
open Purelib.Topology.Surface.Word.Selection (ChordWord)

open Purelib.Topology.Polygon.Stokes (OrientedEdge)

open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)
open Purelib.Topology.Surface.Word.Vertices.WordVertexPath (Path)

namespace ChordWord

variable {count leftSize rightSize : Nat} (chord : Selection.ChordWord count)

/-- Decide whether either orientation of a generator occurs in the retained inside segment. -/
@[expose] def insideUsed (index : Fin count) : Bool :=
  decide (0 < SignedGenerator.occurrences ⟨index, false⟩ chord.inside + SignedGenerator.occurrences ⟨index, true⟩
    chord.inside)

/-- An original inside occurrence makes its generator's support test true. -/
private theorem insideUsed_of_mem (letter : SignedWord.SignedGenerator count) (member : letter ∈ chord.inside) :
    ChordWord.insideUsed chord letter.index = true := by
  have positive := SignedGenerator.occurrences_positive letter chord.inside member
  unfold ChordWord.insideUsed
  apply decide_eq_true
  cases letter with
  | mk index reversed => cases reversed <;> dsimp only at positive ⊢ <;> omega

/-- A true inside support test yields an actual signed occurrence of that generator. -/
private theorem insideUsed_member (index : Fin count) (present : ChordWord.insideUsed chord index = true) :
    ∃ letter ∈ chord.inside, letter.index = index := by
  have positive : 0 < SignedGenerator.occurrences ⟨index, false⟩ chord.inside +
      SignedGenerator.occurrences ⟨index, true⟩ chord.inside := of_decide_eq_true present
  by_cases first : 0 < SignedGenerator.occurrences ⟨index, false⟩ chord.inside
  · exact ⟨⟨index, false⟩, (SignedGenerator.locate ⟨index, false⟩ chord.inside first).member, rfl⟩
  · exact ⟨⟨index, true⟩, (SignedGenerator.locate ⟨index, true⟩ chord.inside (by omega)).member, rfl⟩

/-- Signed uniqueness and inside balance exclude every outside generator from inside support. -/
private theorem insideUnused_of_outside
    (unique : ∀ index reversed, SignedGenerator.occurrences ⟨index, reversed⟩ chord.word ≤ 1)
    (balanced : ∀ index, Pairing.totalAt (chord.inside.map SignedGenerator.coefficients) index = 0)
    (letter : SignedWord.SignedGenerator count) (member : letter ∈ chord.outside) : ChordWord.insideUsed chord
      letter.index = false := by
  have positive := SignedGenerator.occurrences_positive letter chord.outside member
  have equation := balanced letter.index
  rw [SignedGenerator.total_eq_counts] at equation
  have bounded := unique letter.index letter.reversed
  rw [chord.occurrences, ChordWord.tail,
    SignedGenerator.occurrences_append] at bounded
  unfold ChordWord.insideUsed
  apply decide_eq_false
  cases letter with
  | mk index reversed => cases reversed <;> dsimp only at positive bounded equation ⊢ <;> omega

/-- Combine disjoint inside and outside vertex banks and retain the cancelling edge between their anchors.

Nonpivot generators use their original supported side; the pivot joins the outside anchor to the inside anchor. -/
@[expose] def joinedEdges (inside : Vertices.WordVertexRealization chord.inside leftSize)
    (outside : Vertices.WordVertexRealization chord.outside rightSize) :
    Data.Vector (Stokes.OrientedEdge (leftSize + rightSize)) count :=
  Data.Vector.Basic.vectorOfFn fun index => if index = chord.index then ⟨outside.anchor.natAdd leftSize,
    inside.anchor.castAdd rightSize⟩
    else if ChordWord.insideUsed chord index then OrientedEdge.map (Fin.castAdd rightSize) (inside.edges index)
    else OrientedEdge.map (Fin.natAdd leftSize) (outside.edges index)

/-- The retained cancelling generator runs from the outside anchor to the inside anchor. -/
private theorem joined_pivot (inside : Vertices.WordVertexRealization chord.inside leftSize)
    (outside : Vertices.WordVertexRealization chord.outside rightSize) :
    ChordWord.joinedEdges chord inside outside chord.index = ⟨outside.anchor.natAdd leftSize, inside.anchor.castAdd
      rightSize⟩ := by
  rw [ChordWord.joinedEdges, Data.Vector.Basic.vectorOfFn_apply, if_pos rfl]

/-- Every inside occurrence reads its original edge through the left disjoint-bank embedding. -/
private theorem joined_inside (inside : Vertices.WordVertexRealization chord.inside leftSize)
    (outside : Vertices.WordVertexRealization chord.outside rightSize)
    (unique : ∀ index reversed, SignedGenerator.occurrences ⟨index, reversed⟩ chord.word ≤ 1)
    (letter : SignedWord.SignedGenerator count) (member : letter ∈ chord.inside) :
    ChordWord.joinedEdges chord inside outside letter.index = OrientedEdge.map (Fin.castAdd rightSize) (inside.edges
      letter.index) := by
  rw [ChordWord.joinedEdges, Data.Vector.Basic.vectorOfFn_apply, if_neg (chord.tail_avoids unique letter
    (List.mem_append_left _ member)),
    ChordWord.insideUsed_of_mem chord letter member]
  rfl

/-- Every outside occurrence reads its original edge through the right disjoint-bank embedding. -/
private theorem joined_outside (inside : Vertices.WordVertexRealization chord.inside leftSize)
    (outside : Vertices.WordVertexRealization chord.outside rightSize)
    (unique : ∀ index reversed, SignedGenerator.occurrences ⟨index, reversed⟩ chord.word ≤ 1)
    (balanced : ∀ index, Pairing.totalAt (chord.inside.map SignedGenerator.coefficients) index = 0)
    (letter : SignedWord.SignedGenerator count) (member : letter ∈ chord.outside) :
    ChordWord.joinedEdges chord inside outside letter.index = OrientedEdge.map (Fin.natAdd leftSize) (outside.edges
      letter.index) := by
  rw [ChordWord.joinedEdges, Data.Vector.Basic.vectorOfFn_apply, if_neg (chord.tail_avoids unique letter
    (List.mem_append_right _ member)),
    ChordWord.insideUnused_of_outside chord unique balanced letter member]
  rfl

/-- Realize a cancelling chord word on the disjoint union of its two retained vertex banks. -/
@[expose] def joinVertices (inside : Vertices.WordVertexRealization chord.inside leftSize)
    (outside : Vertices.WordVertexRealization chord.outside rightSize)
    (unique : ∀ index reversed, SignedGenerator.occurrences ⟨index, reversed⟩ chord.word ≤ 1)
    (balanced : ∀ index, Pairing.totalAt (chord.inside.map SignedGenerator.coefficients) index = 0) :
    Vertices.WordVertexRealization chord.word (leftSize + rightSize) where
  edges := ChordWord.joinedEdges chord inside outside
  anchor := outside.anchor.natAdd leftSize
  closed := by
    have inner := WordVertexPath.congr (WordVertexPath.map inside.closed (Fin.castAdd rightSize))
      (fun letter member => (ChordWord.joined_inside chord inside outside unique letter member).symm)
    have outer := WordVertexPath.congr (WordVertexPath.map outside.closed (Fin.natAdd leftSize))
      (fun letter member => (ChordWord.joined_outside chord inside outside unique balanced letter member).symm)
    have forward : WordVertexPath.Path (ChordWord.joinedEdges chord inside outside) [⟨chord.index, false⟩]
        (outside.anchor.natAdd leftSize) (inside.anchor.castAdd rightSize) := by
      have edge : SignedGenerator.vertexEdge (ChordWord.joinedEdges chord inside outside) ⟨chord.index, false⟩ =
          ⟨outside.anchor.natAdd leftSize, inside.anchor.castAdd rightSize⟩ := ChordWord.joined_pivot chord inside
            outside
      simpa only [edge] using WordVertexPath.single
        (ChordWord.joinedEdges chord inside outside) ⟨chord.index, false⟩
    have backward : WordVertexPath.Path (ChordWord.joinedEdges chord inside outside) [⟨chord.index, true⟩]
        (inside.anchor.castAdd rightSize) (outside.anchor.natAdd leftSize) := by
      have edge : SignedGenerator.vertexEdge (ChordWord.joinedEdges chord inside outside) ⟨chord.index, true⟩ =
          ⟨inside.anchor.castAdd rightSize, outside.anchor.natAdd leftSize⟩ :=
        congrArg OrientedEdge.reverse (ChordWord.joined_pivot chord inside outside)
      simpa only [edge] using WordVertexPath.single
        (ChordWord.joinedEdges chord inside outside) ⟨chord.index, true⟩
    exact PathEndpoints.append forward
      (PathEndpoints.append inner
        (PathEndpoints.append backward outer))

/-- Coverage of the two original models covers the entire joined vertex bank. -/
private theorem join_covered (inside : Vertices.WordVertexModel chord.inside leftSize)
    (outside : Vertices.WordVertexModel chord.outside rightSize)
    (unique : ∀ index reversed, SignedGenerator.occurrences ⟨index, reversed⟩ chord.word ≤ 1)
    (balanced : ∀ index, Pairing.totalAt (chord.inside.map SignedGenerator.coefficients) index = 0) :
    ∀ vertex, (ChordWord.joinVertices chord inside.toWordVertexRealization outside.toWordVertexRealization unique
      balanced).Supported vertex := by
  have leftCovered (vertex : Fin leftSize) :
      (ChordWord.joinVertices chord inside.toWordVertexRealization outside.toWordVertexRealization unique
        balanced).Supported
        (vertex.castAdd rightSize) := by
    rcases inside.covered vertex with same | ⟨letter, member, same⟩
    · refine .inr ⟨⟨chord.index, false⟩, List.mem_cons_self, .inr ?_⟩
      change vertex.castAdd rightSize = (ChordWord.joinedEdges chord _ _ chord.index).finish
      rw [ChordWord.joined_pivot chord]
      exact congrArg (Fin.castAdd rightSize) same
    · refine .inr ⟨letter, List.mem_cons_of_mem _ (List.mem_append_left _ member), ?_⟩
      change vertex.castAdd rightSize = (ChordWord.joinedEdges chord _ _ letter.index).start ∨
        vertex.castAdd rightSize = (ChordWord.joinedEdges chord _ _ letter.index).finish
      rw [ChordWord.joined_inside chord _ _ unique letter member]
      exact same.elim (fun same => .inl (congrArg (Fin.castAdd rightSize) same))
        (fun same => .inr (congrArg (Fin.castAdd rightSize) same))
  have rightCovered (vertex : Fin rightSize) :
      (ChordWord.joinVertices chord inside.toWordVertexRealization outside.toWordVertexRealization unique
        balanced).Supported
        (vertex.natAdd leftSize) := by
    rcases outside.covered vertex with same | ⟨letter, member, same⟩
    · exact .inl (congrArg (Fin.natAdd leftSize) same)
    · refine .inr ⟨letter, List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_cons_of_mem _ member)), ?_⟩
      change vertex.natAdd leftSize = (ChordWord.joinedEdges chord _ _ letter.index).start ∨
        vertex.natAdd leftSize = (ChordWord.joinedEdges chord _ _ letter.index).finish
      rw [ChordWord.joined_outside chord _ _ unique balanced letter member]
      exact same.elim (fun same => .inl (congrArg (Fin.natAdd leftSize) same))
        (fun same => .inr (congrArg (Fin.natAdd leftSize) same))
  intro vertex
  by_cases below : vertex.val < leftSize
  · exact leftCovered ⟨vertex.val, below⟩
  · let right : Fin rightSize := ⟨vertex.val - leftSize, by omega⟩
    have same : right.natAdd leftSize = vertex := by
      apply Fin.ext
      change leftSize + (vertex.val - leftSize) = vertex.val
      omega
    exact same ▸ rightCovered right

/-- A nonempty signed path begins at its first oriented generator endpoint. -/
private theorem head_start {size : Nat} {edges : Fin count → Stokes.OrientedEdge size} {head :
  SignedWord.SignedGenerator count}
    {tail : List (SignedWord.SignedGenerator count)} {first last : Fin size} (path : WordVertexPath.Path edges (head ::
      tail) first last) :
    first = (SignedGenerator.vertexEdge edges head).start := by cases path; rfl

/-- A realization of a chord word restricts to closed inside and outside paths at the pivot endpoints. -/
private theorem joined_paths {size : Nat} (other : Vertices.WordVertexRealization chord.word size) :
    WordVertexPath.Path other.edges chord.inside (other.edges chord.index).finish (other.edges chord.index).finish ∧
      WordVertexPath.Path other.edges chord.outside (other.edges chord.index).start (other.edges chord.index).start :=
        by
  have atStart : other.anchor = (other.edges chord.index).start := ChordWord.head_start other.closed
  have path := (other.closed.castStart atStart).castFinish atStart
  change WordVertexPath.Path other.edges (SignedGenerator.mk chord.index false :: _) _ _ at path
  cases path with
  | cons tail =>
      obtain ⟨middle, inside, rest⟩ := PathEndpoints.split_append chord.inside _ tail
      cases rest with
      | cons outside => exact ⟨inside, outside⟩

/-- Restrict a chord realization to the inside segment based at the pivot finish. -/
@[expose] def insideRealization {size : Nat} (other : Vertices.WordVertexRealization chord.word size) :
    Vertices.WordVertexRealization chord.inside size :=
  ⟨other.edges, (other.edges chord.index).finish, by
    exact (ChordWord.joined_paths chord other).1⟩

/-- Restrict a chord realization to the outside segment based at the pivot start. -/
@[expose] def outsideRealization {size : Nat} (other : Vertices.WordVertexRealization chord.word size) :
    Vertices.WordVertexRealization chord.outside size :=
  ⟨other.edges, (other.edges chord.index).start, by
    exact (ChordWord.joined_paths chord other).2⟩

/-- Combine two vertex maps on the exact disjoint finite bank.

The original coordinate selects its retained left bank or its right remainder. The total bank bound certifies the
corresponding original index without rebuilding either map. -/
@[expose] def joinMap {target : Nat} (left : Fin leftSize → Fin target) (right : Fin rightSize → Fin target)
    (vertex : Fin (leftSize + rightSize)) : Fin target :=
  if below : vertex.val < leftSize then left ⟨vertex.val, below⟩
  else right ⟨vertex.val - leftSize, by omega⟩

/-- The combined map reads an embedded left vertex through its original left map. -/
private theorem joinMap_left {target : Nat} (left : Fin leftSize → Fin target) (right : Fin rightSize → Fin target)
    (vertex : Fin leftSize) : ChordWord.joinMap left right (vertex.castAdd rightSize) = left vertex := by
  unfold ChordWord.joinMap
  change (if below : vertex.val < leftSize then left ⟨vertex.val, below⟩ else _) = left vertex
  rw [dif_pos vertex.isLt]

/-- The combined map reads an embedded right vertex through its original right map. -/
private theorem joinMap_right {target : Nat} (left : Fin leftSize → Fin target) (right : Fin rightSize → Fin target)
    (vertex : Fin rightSize) : ChordWord.joinMap left right (vertex.natAdd leftSize) = right vertex := by
  unfold ChordWord.joinMap
  change (if below : leftSize + vertex.val < leftSize then _ else
    right ⟨leftSize + vertex.val - leftSize, _⟩) = right vertex
  rw [dif_neg (show ¬leftSize + vertex.val < leftSize by omega)]
  congr 1
  exact Fin.ext (Subtraction.add_sub_cancel_left _ _)

/-- Factor the joined cancellation realization through another realization using both original universal maps.

Each retained inside and outside model supplies its own vertex map. Their disjoint-bank combination preserves the
original anchor and every ordered signed-edge occurrence. -/
@[expose] def joinFactor {target : Nat} (inside : Vertices.WordVertexModel chord.inside leftSize)
    (outside : Vertices.WordVertexModel chord.outside rightSize)
    (unique : ∀ index reversed, SignedGenerator.occurrences ⟨index, reversed⟩ chord.word ≤ 1)
    (balanced : ∀ index, Pairing.totalAt (chord.inside.map SignedGenerator.coefficients) index = 0)
    (other : Vertices.WordVertexRealization chord.word target) :
    (ChordWord.joinVertices chord inside.toWordVertexRealization outside.toWordVertexRealization unique balanced).Factor
      other :=
  let left := inside.lift (ChordWord.insideRealization chord other)
  let right := outside.lift (ChordWord.outsideRealization chord other)
  { vertices := ChordWord.joinMap left.vertices right.vertices
    anchor_eq := by
      exact (ChordWord.joinMap_right _ _ outside.anchor).trans
        (right.anchor_eq.trans (ChordWord.head_start other.closed).symm)
    edge_eq := fun letter member => by
      change OrientedEdge.map (ChordWord.joinMap left.vertices right.vertices)
        (ChordWord.joinedEdges chord _ _ letter.index) = other.edges letter.index
      by_cases pivot : letter.index = chord.index
      · rw [pivot, ChordWord.joined_pivot chord]
        change OrientedEdge.mk (ChordWord.joinMap _ _ (outside.anchor.natAdd leftSize)) (ChordWord.joinMap _ _
          (inside.anchor.castAdd rightSize)) = _
        rw [ChordWord.joinMap_left, ChordWord.joinMap_right, left.anchor_eq, right.anchor_eq]
        rfl
      · rw [ChordWord.joinedEdges, Data.Vector.Basic.vectorOfFn_apply, if_neg pivot]
        cases used : ChordWord.insideUsed chord letter.index
        · rw [if_neg Bool.false_ne_true]
          have outsideMember : letter ∈ chord.outside := by
            rcases Membership.mem_cons.mp member with same | rest
            · exact (pivot (congrArg SignedGenerator.index same)).elim
            · rcases Membership.mem_append.mp rest with inner | rest
              · have present := ChordWord.insideUsed_of_mem chord letter inner
                rw [used] at present
                cases present
              · rcases Membership.mem_cons.mp rest with same | outer
                · exact (pivot (congrArg SignedGenerator.index same)).elim
                · exact outer
          have readback := right.edge_eq letter outsideMember
          change OrientedEdge.mk (ChordWord.joinMap _ _ ((outside.edges letter.index).start.natAdd leftSize))
            (ChordWord.joinMap _ _ ((outside.edges letter.index).finish.natAdd leftSize)) = _
          rw [ChordWord.joinMap_right, ChordWord.joinMap_right]
          exact readback
        · rw [if_pos rfl]
          obtain ⟨entry, entryMember, indexEq⟩ := ChordWord.insideUsed_member chord letter.index used
          have readback := left.edge_eq entry entryMember
          change OrientedEdge.mk (ChordWord.joinMap _ _ ((inside.edges letter.index).start.castAdd rightSize))
            (ChordWord.joinMap _ _ ((inside.edges letter.index).finish.castAdd rightSize)) = _
          rw [ChordWord.joinMap_left, ChordWord.joinMap_left]
          rw [indexEq] at readback
          exact readback }

/-- Join universal inside and outside vertex models along the displayed cancelling generator.

The combined model retains the exact disjoint vertex count, coverage and executable factorization into every other
realization. -/
@[expose] def joinVertexModels (inside : Vertices.WordVertexModel chord.inside leftSize) (outside :
  Vertices.WordVertexModel chord.outside rightSize)
    (unique : ∀ index reversed, SignedGenerator.occurrences ⟨index, reversed⟩ chord.word ≤ 1)
    (balanced : ∀ index, Pairing.totalAt (chord.inside.map SignedGenerator.coefficients) index = 0) :
    Vertices.WordVertexModel chord.word (leftSize + rightSize) where
  toWordVertexRealization := ChordWord.joinVertices chord inside.toWordVertexRealization outside.toWordVertexRealization
    unique balanced
  covered := by
    exact ChordWord.join_covered chord inside outside unique balanced
  lift := ChordWord.joinFactor chord inside outside unique balanced

end ChordWord

namespace WordCancellation

variable {count : Nat}

/-- Every terminal cancellation tree supplies its exact vertex model, including a map to every finite endpoint
assignment of the same word. -/
@[expose] def vertexModel : {word : List (SignedWord.SignedGenerator count)} → (tree : ZeroReduction.WordCancellation
  word) →
    (∀ index reversed, SignedGenerator.occurrences ⟨index, reversed⟩ word ≤ 1) →
    Vertices.WordVertexModel word (tree.pairs + 1)
  | _, .nil, _ => WordVertexModel.empty
  | _, .pair selected inside outside, unique => by
      have counts := selected.counts unique
      let inner := Purelib.Topology.Surface.Word.VertexCancellation.WordCancellation.vertexModel inside
        (selected.chord.inside_counts_le counts)
      let outer := Purelib.Topology.Surface.Word.VertexCancellation.WordCancellation.vertexModel outside
        (ChordWord.outside_counts_le selected.chord counts)
      let joined := VertexCancellation.ChordWord.joinVertexModels selected.chord inner outer counts inside.closed
      have sizeEq : (inside.pairs + 1) + (outside.pairs + 1) = (WordCancellation.pair selected inside outside).pairs + 1
        := by
        change _ = (inside.pairs + outside.pairs + 1) + 1
        omega
      exact sizeEq ▸ WordVertexModel.rotate joined
        (WordRotation.symm selected.rotation)

end WordCancellation
end Purelib.Topology.Surface.Word.VertexCancellation

end
