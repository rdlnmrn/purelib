module
import Purelib.Data.Fin
import Purelib.Data.List.Membership
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Map

import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Sewing.SewingProjection
import Purelib.Topology.Surface.Sewing.VertexSewing
import Purelib.Topology.Surface.Word.ProjectedEdgePairs
public import Purelib.Topology.Surface.Cut.Chord
import Purelib.Topology.Surface.Word.SignedWord
import Purelib.Data.Vector.Basic

open Purelib.Data.List

open Purelib.Topology.Polygon

open Purelib.Topology.Surface.Cut

open Purelib.Topology.Surface.Cut.BoundaryWord

open Purelib.Topology.Surface.Cut.Chord

open Purelib.Topology.Surface.Cut.Chord.CutBoundaryWord
open _root_.Purelib.Topology.Surface.Cut.Chord renaming CutBoundaryWord -> Chord

open Purelib.Topology.Surface.Sewing.SewingProjection

open Purelib.Topology.Surface.Sewing.VertexSewing

open Purelib.Topology.Surface.Word

open Purelib.Topology.Surface.Word.ProjectedEdgePairs

public section

/-!
# Every retained cut pair has its original signed-generator chord

Locate the generator directly in the retained pair list. Reordering the
alphabet does not change this index. Unique projected edge incidence then
identifies both actual endpoints of the selected chord with that same pair.
-/

namespace Purelib.Topology.Surface.Chord.PairChordCoverage

open Purelib.Topology.Polygon.Stokes (OrientedEdge)
open Purelib.Topology.Surface.Cut.BoundaryWord (CutAlphabet CutBoundaryWord)
open Purelib.Topology.Surface.Word.ProjectedEdgePairs (ProjectedEdgePair ProjectedEdgePairing)
open _root_.Purelib.Topology.Surface.Cut.Chord renaming CutBoundaryWord -> Chord

variable {source target : Nat} {labels : Fin source → Fin target}

set_option genInjectivity false in
/-- An original cut pair located at its two-sided generator coordinate in the retained alphabet. -/
structure PairGenerator {edges : List (Stokes.OrientedEdge source)}
    (bank : BoundaryWord.CutAlphabet labels edges) (pair : ProjectedEdgePairs.ProjectedEdgePair labels) where
  /-- Retained generator coordinate for the original pair. -/ index : Fin bank.count
  /-- This generator is two-sided rather than physical. -/ paired : bank.oneSided index = false
  /-- The original generator edge is exactly the pair's first cut edge. -/ generator_eq : bank.generators index =
    pair.first

constructive_injectivity PairGenerator

section
open Purelib.Topology.Surface.Chord
/-- Locate a retained pair's first edge in the ordered pair-only generator bank. -/
@[expose] def pairGenerator (pair : ProjectedEdgePairs.ProjectedEdgePair labels) :
    (pairs : List (ProjectedEdgePairs.ProjectedEdgePair labels)) → pair ∈ pairs → PairGenerator
      (CutAlphabet.ofLists [] pairs) pair
  | [], member => (List.not_mem_nil member).elim
  | head :: rest, member =>
      if same : head.first = pair.first then ⟨⟨0, Nat.zero_lt_succ _⟩, rfl, same⟩
      else
        let tail := pairGenerator pair rest ((Membership.mem_cons.mp
          member).resolve_left
          (fun equal => same (congrArg ProjectedEdgePair.first equal).symm))
        ⟨tail.index.succ, tail.paired, tail.generator_eq⟩

/-- Retain a pair's generator witness while prefixing the physical boundary generators. -/
@[expose] def withBoundary (pair : ProjectedEdgePairs.ProjectedEdgePair labels) (pairs : List
  (ProjectedEdgePairs.ProjectedEdgePair labels)) (member : pair ∈ pairs) :
    (boundary : List (Stokes.OrientedEdge source)) → PairGenerator (CutAlphabet.ofLists boundary
      pairs) pair
  | [] => pairGenerator pair pairs member
  | _ :: rest =>
      let tail := withBoundary pair pairs member rest
      ⟨tail.index.succ, tail.paired, tail.generator_eq⟩

end

/-- Every generator in a pair-only alphabet is two-sided. -/
private theorem pair_only (pairs : List (ProjectedEdgePairs.ProjectedEdgePair labels)) (index : Fin (CutAlphabet.ofLists
  [] pairs).count) :
    (CutAlphabet.ofLists [] pairs).oneSided index = false := by
  induction pairs with
  | nil => exact Fin.elim0 index
  | cons pair rest ih =>
      refine Purelib.Data.Fin.cases_induction rfl (fun index => ih index) index

open Purelib.Topology.Surface.Chord in
/-- Each one-sided alphabet generator belongs to the original physical boundary. -/
private theorem physical_generator_mem (boundary : List (Stokes.OrientedEdge source)) (pairs : List
  (ProjectedEdgePairs.ProjectedEdgePair labels))
    (index : Fin (CutAlphabet.ofLists boundary pairs).count)
    (physical : (CutAlphabet.ofLists boundary pairs).oneSided index = true) :
    (CutAlphabet.ofLists boundary pairs).generators index ∈ boundary := by
  induction boundary with
  | nil => have impossible := (pair_only pairs index).symm.trans physical; cases impossible
  | cons edge rest ih =>
      revert physical
      refine Purelib.Data.Fin.cases_induction (fun _ => List.mem_cons_self) (fun index physical => ?_) index
      exact List.mem_cons_of_mem edge (ih index physical)

namespace ProjectedEdgePairing

variable {edges : List (Stokes.OrientedEdge source)}

open Purelib.Topology.Surface.Chord in
/-- A one-sided generator of the retained boundary word is an original physical boundary edge. -/
theorem oneSided_generator_mem (pairing : ProjectedEdgePairs.ProjectedEdgePairing labels edges)
    (index : Fin (ProjectedEdgePairing.boundaryWord pairing).alphabet.count) (physical :
      (ProjectedEdgePairing.boundaryWord pairing).alphabet.oneSided index = true) :
    (ProjectedEdgePairing.boundaryWord pairing).alphabet.generators index ∈ pairing.boundary :=
  physical_generator_mem pairing.boundary pairing.pairs index physical

/-- Both edges of each retained pair belong to the original input edge list. -/
theorem pair_edges_mem (pairing : ProjectedEdgePairs.ProjectedEdgePairing labels edges) {pair :
  ProjectedEdgePairs.ProjectedEdgePair labels} (member : pair ∈ pairing.pairs) :
    pair.first ∈ edges ∧ pair.second ∈ edges := by
  have allOccurrences : ∀ pairs : List (ProjectedEdgePairs.ProjectedEdgePair labels), pair ∈ pairs →
      pair.first ∈ ProjectedEdgePair.occurrences pairs ∧ pair.second ∈ ProjectedEdgePair.occurrences pairs := by
    intro pairs
    induction pairs with
    | nil => exact fun member => (List.not_mem_nil member).elim
    | cons head rest ih =>
        intro member
        rcases Membership.mem_cons.mp member with same | member
        · subst pair
          exact ⟨List.mem_cons_self, List.mem_cons_of_mem _ List.mem_cons_self⟩
        · exact ⟨List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (ih member).1),
            List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (ih member).2)⟩
  have occurrences := allOccurrences pairing.pairs member
  exact ⟨(EdgeReordering.mem_iff pairing.incidence _).mpr (Membership.mem_append.mpr (Or.inr occurrences.1)),
    (EdgeReordering.mem_iff pairing.incidence _).mpr (Membership.mem_append.mpr (Or.inr occurrences.2))⟩

set_option genInjectivity false in
/-- The original pair and the chosen chord share literal cut edges, not merely their projected labels. All selected data
can be cached together. -/
structure PairChord (pairing : ProjectedEdgePairs.ProjectedEdgePairing labels edges) (pair :
  ProjectedEdgePairs.ProjectedEdgePair labels) where
  /-- Original retained alphabet coordinate associated with the pair. -/ index : Fin (ProjectedEdgePairing.boundaryWord
    pairing).alphabet.count
  /-- The selected coordinate is a two-sided generator. -/ paired : (ProjectedEdgePairing.boundaryWord
    pairing).alphabet.oneSided index = false
  /-- Retained signed-generator chord at that exact coordinate. -/ chord : Cut.Chord.CutBoundaryWord
    (ProjectedEdgePairing.boundaryWord pairing) index
  /-- The chord's first cut edge is literally the original pair's first edge. -/ first_eq : chord.pair.first =
    pair.first
  /-- The chord's second cut edge is literally the original pair's second edge. -/ second_eq : chord.pair.second =
    pair.second

constructive_injectivity PairChord

open Purelib.Topology.Surface.Chord in
open Purelib.Topology.Surface.Chord.PairChordCoverage in
/-- Select the chord for an original retained pair and certify both literal cut-edge identities.

Unique projected incidence identifies the second selected edge with the original pair, retaining its exact generator
coordinate. -/
@[expose] def pairChord (pairing : ProjectedEdgePairs.ProjectedEdgePairing labels edges)
    (unique : (edges.map (OrientedEdge.map labels)).Nodup)
    (pair : ProjectedEdgePairs.ProjectedEdgePair labels) (member : pair ∈ pairing.pairs) :
      PairChord pairing pair := by
  let selected := withBoundary pair pairing.pairs member pairing.boundary
  let index : Fin (ProjectedEdgePairing.boundaryWord pairing).alphabet.count := selected.index
  have paired : (ProjectedEdgePairing.boundaryWord pairing).alphabet.oneSided index = false := selected.paired
  let chord := Chord.build (ProjectedEdgePairing.boundaryWord pairing) index paired
  have firstEq : chord.pair.first = pair.first := by
    have provenance := ProjectedEdgePairing.boundaryWord_provenance pairing chord.first.entry chord.first.member
    unfold CutWordEntry.PairProvenance at provenance
    rw [chord.first.letter_eq] at provenance
    exact provenance.trans selected.generator_eq
  have secondMember : chord.pair.second ∈ edges := by
    have lastMember := chord.first.rest_mem chord.last.member
    exact (congrArg (fun bank => chord.last.entry.edge ∈ bank) (ProjectedEdgePairing.boundaryWord
      pairing).alphabet.edges_eq).mp
      (Map.mem_map_of_mem lastMember)
  have secondEq : chord.pair.second = pair.second := by
    apply Map.equal_of_map_unique (OrientedEdge.map labels) unique secondMember (pair_edges_mem
      pairing member).2
    rw [chord.pair.opposite, firstEq]
    exact pair.opposite.symm
  exact ⟨index, paired, chord, firstEq, secondEq⟩

end ProjectedEdgePairing
end Purelib.Topology.Surface.Chord.PairChordCoverage
