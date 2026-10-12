module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Map
import Purelib.Data.List.Membership
import Purelib.Data.Vector.Basic
import Purelib.Topology.Chain.PathBoundary

import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Cut.IntegralPairing
import Purelib.Topology.Surface.Sewing.PolygonSewing
import Purelib.Topology.Surface.Sewing.VertexSewing
import Purelib.Topology.Surface.Word.Pairing
import Purelib.Topology.Surface.Word.ProjectedEdgePairs
import Purelib.Topology.Surface.Word.Selection
import Purelib.Topology.Surface.Word.SignedWord
import Purelib.Topology.Surface.Word.Surgery
public import Purelib.Topology.Surface.Word.PairedWord
public import Purelib.Topology.Surface.Cut.JumpPaths
import Purelib.Tactic.QuotientFreeOmega
meta import Mathlib.Tactic.Linter.Lint

public section

/-!
# Occurrence-preserving chord paths on the actual cut boundary

A paired generator selects its positive and negative signed occurrences,
retaining their actual cut edges and the cyclic interval between them. Edge
equality is never used to find those occurrences a second time. The interval
projects to a closed surface path, and its paired signed counts are exactly
the corresponding row of the cached integral pairing.
-/

namespace Purelib.Topology.Surface.Cut.Chord

open Purelib
open Purelib.Data.List
open Purelib.Topology.Chain
open Purelib.Topology.Polygon
open Purelib.Topology.Polygon.Stokes
open Purelib.Topology.Surface.Cut
open Purelib.Topology.Surface.Cut.BoundaryWord
open Purelib.Topology.Surface.Cut.IntegralPairing
open Purelib.Topology.Surface.Cut.JumpPaths
open Purelib.Topology.Surface.Cut.JumpPaths.CutPath
open Purelib.Topology.Surface.Sewing.PolygonSewing
open Purelib.Topology.Surface.Sewing.VertexSewing
open Purelib.Topology.Surface.Word
open Purelib.Topology.Surface.Word.PairedWord
open Purelib.Topology.Surface.Word.SignedWord
open Purelib.Topology.Surface.Word.Surgery

open Purelib.Topology.Polygon.Stokes (OrientedEdge)

open Purelib.Topology.Chain.PathBoundary (PathEndpoints)
open Purelib.Topology.Surface.Word.SignedWord (SignedGenerator)
open Purelib.Topology.Surface.Cut.BoundaryWord (CutWordEntry CutBoundaryWord)
open Purelib.Topology.Surface.Word.Selection (WordRotation InterlacedAt ChordAt)
open Purelib.Topology.Surface.Word.ProjectedEdgePairs (ProjectedEdgePair)
open _root_.Purelib.Topology.Surface.Cut.IntegralPairing renaming CutBoundaryWord -> IntegralPairing
open Purelib.Topology.Surface.Sewing.PolygonSewing.PolygonStokes (BoundarySplit)

namespace CutWordEntry

variable {source target count : Nat} {labels : Fin source → Fin target}
  {generators : Data.Vector (Stokes.OrientedEdge source) count}

set_option genInjectivity false in
/-- A literal split around one signed occurrence of the retained cut word.

The selected entry keeps its original cut edge, and the split equation identifies its exact location and signed letter.
-/
structure Occurrence (needle : SignedWord.SignedGenerator count) (entries : List (BoundaryWord.CutWordEntry labels
  generators)) where
  /-- Original entries before the selected occurrence. -/ before : List (BoundaryWord.CutWordEntry labels generators)
  /-- The selected original cut entry. -/ entry : BoundaryWord.CutWordEntry labels generators
  /-- Original entries after the selected occurrence. -/ after : List (BoundaryWord.CutWordEntry labels generators)
  /-- The original list is exactly the retained prefix, entry, and suffix. -/ equation : entries = before ++ entry ::
    after
  /-- The selected entry has the requested signed generator. -/ letter_eq : entry.letter = needle

constructive_injectivity Occurrence

/-- Total selection from positive signed multiplicity, preserving the full entry rather than forgetting its cut edge
when selecting a letter.

The original left-to-right search retains the first matching entry together with its literal prefix and suffix. Positive
signed multiplicity excludes exhaustion without changing the original occurrence list. -/
@[expose] def locate (needle : SignedWord.SignedGenerator count) : (entries : List (BoundaryWord.CutWordEntry labels
  generators)) →
    0 < needle.occurrences (entries.map CutWordEntry.letter) → Occurrence needle entries
  | [], positive => (Nat.not_lt_zero _ positive).elim
  | head :: remaining, positive =>
      if same : head.letter = needle then ⟨[], head, remaining, rfl, same⟩
      else
        let tail := locate needle remaining (by
          rw [List.map_cons, SignedGenerator.occurrences, if_neg same, zero_add] at positive
          exact positive)
        ⟨head :: tail.before, tail.entry, tail.after, congrArg (List.cons head) tail.equation, tail.letter_eq⟩

namespace Occurrence

variable {needle : SignedWord.SignedGenerator count} {entries : List (BoundaryWord.CutWordEntry labels generators)}

/-- Read the retained signed occurrence as a split of the original edge boundary.

Mapping the retained prefix, entry and suffix preserves the original split equation. Every cut-edge occurrence keeps its
original position and orientation. -/
@[expose] def boundarySplit (found : Occurrence needle entries) : PolygonStokes.BoundarySplit (entries.map
  CutWordEntry.edge) :=
  ⟨found.before.map CutWordEntry.edge, found.entry.edge, found.after.map CutWordEntry.edge,
    by simpa only [Map.map_append, List.map_cons] using congrArg (List.map CutWordEntry.edge) found.equation⟩

/-- Rotate the signed word to begin at the exact retained occurrence.

The retained suffix precedes the original prefix after the selected letter. Both word equations come from the same
displayed entry split, preserving signed occurrence order. -/
@[expose] def rotation (found : Occurrence needle entries) :
    Selection.WordRotation (entries.map CutWordEntry.letter)
      (needle :: ((found.after ++ found.before).map CutWordEntry.letter)) :=
  ⟨found.before.map CutWordEntry.letter, (found.entry :: found.after).map CutWordEntry.letter,
    by simpa only [Map.map_append] using congrArg (List.map CutWordEntry.letter) found.equation,
    by rw [List.map_cons, found.letter_eq, List.cons_append, Map.map_append]⟩

/-- The selected original entry belongs to the supplied occurrence list. -/
theorem member (found : Occurrence needle entries) : found.entry ∈ entries := by
  exact (congrArg (fun bank => found.entry ∈ bank) found.equation).mpr
    (Membership.mem_append.mpr (Or.inr List.mem_cons_self))

/-- Every entry in the rotated remainder belongs to the original occurrence list. -/
theorem rest_mem (found : Occurrence needle entries) {entry : BoundaryWord.CutWordEntry labels generators}
    (member : entry ∈ found.after ++ found.before) : entry ∈ entries := by
  rw [found.equation]
  rcases Membership.mem_append.mp member with after | before
  · exact Membership.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ after))
  · exact Membership.mem_append.mpr (Or.inl before)

end Occurrence
end CutWordEntry

section CutBoundaryWord

variable {source target : Nat} {labels : Fin source → Fin target} {edges : List (Stokes.OrientedEdge source)}

set_option genInjectivity false in
/-- The positive and subsequent negative occurrence of one paired generator.

Both selections retain their original cut entries and the cyclic interval between them. -/
structure CutBoundaryWord (word : BoundaryWord.CutBoundaryWord labels edges) (index : Fin word.alphabet.count) where
  /-- Retained positive occurrence in the original alphabet entries. -/ first : CutWordEntry.Occurrence ⟨index, false⟩
    word.alphabet.entries
  /-- Retained negative occurrence in the cyclic remainder after the positive occurrence. -/ last :
    CutWordEntry.Occurrence ⟨index, true⟩ (first.after ++ first.before)

constructive_injectivity CutBoundaryWord

namespace CutBoundaryWord

variable {word : BoundaryWord.CutBoundaryWord labels edges} {index : Fin word.alphabet.count}

/-- Select both signed occurrences of a generator proved to be paired.

The exact occurrence counts make both finite searches total and retain the original cyclic order. -/
@[expose] def build (word : BoundaryWord.CutBoundaryWord labels edges) (index : Fin word.alphabet.count)
    (paired : word.alphabet.oneSided index = false) : CutBoundaryWord word index :=
  let first := CutWordEntry.locate ⟨index, false⟩ word.alphabet.entries (by
    rw [word.alphabet.occurrences_eq, Bool.false_and]; exact Nat.zero_lt_one)
  have negative : 0 < SignedGenerator.occurrences ⟨index, true⟩
      ((first.after ++ first.before).map CutWordEntry.letter) := by
    have count := first.rotation.occurrences (⟨index, true⟩ : SignedWord.SignedGenerator word.alphabet.count)
    rw [SignedGenerator.occurrences, if_neg (by
      intro same; have := congrArg SignedGenerator.reversed same; cases this), zero_add,
      word.alphabet.occurrences_eq, paired] at count
    change SignedGenerator.occurrences ⟨index, true⟩
      ((first.after ++ first.before).map CutWordEntry.letter) = 1 at count
    omega
  ⟨first, CutWordEntry.locate ⟨index, true⟩ _ negative⟩

/-- Read the retained cut occurrences as the corresponding signed-word chord selection. -/
@[expose] def selected (chord : CutBoundaryWord word index) : Selection.ChordAt word.letters index :=
  { chord := ⟨index, chord.last.before.map CutWordEntry.letter, chord.last.after.map CutWordEntry.letter⟩
    index_eq := rfl
    rotation :=
      { first := chord.first.before.map CutWordEntry.letter
        last := (chord.first.entry :: chord.first.after).map CutWordEntry.letter
        source_eq := word.letters_eq.trans chord.first.rotation.source_eq
        target_eq := by
          change (⟨index, false⟩ :: ((chord.last.before.map CutWordEntry.letter) ++
            (⟨index, true⟩ :: chord.last.after.map CutWordEntry.letter))) = _
          have tail := congrArg (List.map CutWordEntry.letter) chord.last.equation
          simp only [Map.map_append, List.map_cons, chord.last.letter_eq] at tail
          rw [← tail, List.map_cons, chord.first.letter_eq, List.cons_append] } }

/-- Recover the opposite projected edge pair from the retained positive and negative entries. -/
@[expose] def pair (chord : CutBoundaryWord word index) : ProjectedEdgePairs.ProjectedEdgePair labels :=
  ⟨chord.first.entry.edge, chord.last.entry.edge, by
    rw [chord.last.entry.projected_eq, chord.first.entry.projected_eq,
      chord.last.letter_eq, chord.first.letter_eq]
    rfl⟩

/-- The original ordered cut interval from the positive entry through the negative entry. -/
@[expose] def interval (chord : CutBoundaryWord word index) : List (BoundaryWord.CutWordEntry labels
  word.alphabet.generators) :=
  chord.first.entry :: (chord.last.before ++ [chord.last.entry])

/-- The retained chord interval has the exact endpoints of its original cut-edge pair.

The supplied closed boundary is split at the two retained occurrences. Its intervening path runs between their original
endpoint vertices in the displayed cyclic order. -/
theorem interval_path (chord : CutBoundaryWord word index) {anchor : Fin source}
    (closed : PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish edges anchor anchor) :
    PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish (chord.interval.map CutWordEntry.edge)
      chord.pair.first.start chord.pair.second.finish := by
  have rest := chord.first.boundarySplit.rest_path (by rw [word.alphabet.edges_eq]; exact closed)
  change PathBoundary.PathEndpoints _ _ (chord.first.after.map CutWordEntry.edge ++ chord.first.before.map
    CutWordEntry.edge)
    chord.first.entry.edge.finish chord.first.entry.edge.start at rest
  rw [← Map.map_append, chord.last.equation, Map.map_append, List.map_cons] at rest
  obtain ⟨middle, inside, outside⟩ := PathEndpoints.split_append (chord.last.before.map CutWordEntry.edge)
    (chord.last.entry.edge :: chord.last.after.map CutWordEntry.edge) rest
  cases outside with
  | cons tail =>
      change PathBoundary.PathEndpoints _ _ (chord.first.entry.edge ::
        ((chord.last.before ++ [chord.last.entry]).map CutWordEntry.edge)) _ _
      rw [Map.map_append, List.map_cons, List.map_nil]
      exact .cons (PathEndpoints.append inside (.cons (.nil _)))

/-- Retain the chord's cut interval together with its exact projected surface path. -/
@[expose] def path (chord : CutBoundaryWord word index) {anchor : Fin source}
    (closed : PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish edges anchor anchor) :
    CutPath.Projected labels chord.pair.first.start chord.pair.second.finish :=
  Projected.build labels _ (chord.interval_path closed)

/-- The retained chord interval projects to a closed surface path. -/
theorem path_closed (chord : CutBoundaryWord word index) {anchor : Fin source}
    (closed : PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish edges anchor anchor) :
    PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish (chord.path closed).surfaceEdges
      (labels chord.pair.first.start) (labels chord.pair.first.start) :=
  (chord.path closed).closed (congrArg OrientedEdge.finish chord.pair.opposite)

/-- Every chord-interval entry belongs to the original retained cut alphabet.

The interval contains the first retained occurrence, the intervening prefix and the last retained occurrence. Their
literal split equations transport membership into the original alphabet. -/
theorem interval_mem (chord : CutBoundaryWord word index) {entry : BoundaryWord.CutWordEntry labels
  word.alphabet.generators}
    (member : entry ∈ chord.interval) : entry ∈ word.alphabet.entries := by
  rcases Membership.mem_cons.mp member with same | rest
  · cases same; exact chord.first.member
  · apply chord.first.rest_mem
    rw [chord.last.equation]
    rcases Membership.mem_append.mp rest with before | last
    · exact Membership.mem_append.mpr (Or.inl before)
    · have same := Membership.mem_singleton.mp last
      cases same
      exact Membership.mem_append.mpr (Or.inr List.mem_cons_self)

/-- Every chord-interval edge is supported on the original cut boundary. -/
theorem interval_supported (chord : CutBoundaryWord word index) :
    CutPath.Supported edges (chord.interval.map CutWordEntry.edge) := by
  intro edge member
  obtain ⟨entry, entryMember, same⟩ := Map.mem_map.mp member
  rw [← same]
  apply Or.inl
  exact (congrArg (fun bank => entry.edge ∈ bank) word.alphabet.edges_eq).mp
    (Map.mem_map_of_mem (chord.interval_mem entryMember))

/-- Every projected chord edge is supported on the projected original boundary. -/
theorem path_supported (chord : CutBoundaryWord word index) {anchor : Fin source}
    (closed : PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish edges anchor anchor) :
    CutPath.Supported (edges.map (OrientedEdge.map labels)) (chord.path closed).surfaceEdges :=
  CutPath.supported_map labels chord.interval_supported

/-- Only the two selected coordinates must be balanced. One-sided boundary coordinates elsewhere in the original cyclic
word need not vanish.

The original paired mask controls each retained column. Balanced selected coordinates identify the corresponding signed
coefficient row while preserving all other one-sided occurrences. -/
theorem paired_row (chord : CutBoundaryWord word index) (pairing : IntegralPairing word)
    (paired : word.alphabet.oneSided index = false) (column : Fin word.alphabet.count) :
    pairing.paired index column =
      Pairing.totalAt ((SignedGenerator.retain (fun position => !word.alphabet.oneSided position)
        chord.selected.chord.inside).map SignedGenerator.coefficients) column := by
  have unique (position : Fin word.alphabet.count) (reversed : Bool) :
      SignedGenerator.occurrences ⟨position, reversed⟩ word.letters ≤ 1 := by
    rw [CutBoundaryWord.occurrences_eq word]; split <;> omega
  rw [SignedGenerator.total_retain]
  cases side : word.alphabet.oneSided column
  · change pairing.paired index column = Pairing.totalAt
      (chord.selected.chord.inside.map SignedGenerator.coefficients) column
    by_cases same : column = index
    · cases same
      rw [pairing.paired_diagonal]
      apply Eq.symm
      apply Word.Surgery.totalAt_zero_of
      intro coefficients member
      obtain ⟨letter, member, equal⟩ := Map.mem_map.mp member
      rw [← equal]
      exact SignedGenerator.coefficient_zero_of_ne letter index
        (chord.selected.chord.tail_avoids (chord.selected.counts unique) letter
          (Membership.mem_append.mpr (Or.inl member)))
    · have total (position : Fin word.alphabet.count) (balanced : word.alphabet.oneSided position = false) :
          Pairing.totalAt (word.letters.map SignedGenerator.coefficients) position = 0 := by
        rw [← word.coefficients_eq, ← word.signature.total_eq, CutBoundaryWord.total_eq_oneSided word, balanced]
        rfl
      have row := chord.selected.chord.pairing_row (chord.selected.counts unique) column same
      change Pairing.pairingAt _ index column = _ at row
      rw [chord.selected.rotation.pairing_at index column (total index paired) (total column side),
        ← word.coefficients_eq, ← word.signature.matrix_eq, ← pairing.paired_twice index column paired side] at row
      omega
  · rw [pairing.paired_eq, paired, side]
    rfl

end CutBoundaryWord
end CutBoundaryWord
end Purelib.Topology.Surface.Cut.Chord

end
