module
import Purelib.Data.Fin
import Purelib.Data.List.Membership
import Purelib.Data.Nat.Order
import Purelib.Data.List.Map
import Purelib.Data.Vector.Basic

import Purelib.Data.List.Permutation
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.BoundaryPairs
import Purelib.Topology.Surface.Word.ProjectedEdgePairs
import Purelib.Topology.Surface.Word.SignedWord
public import Purelib.Topology.Surface.Cut.BoundaryWord

section

open scoped Purelib.Data.Nat

open Purelib

open Purelib.Data

open Purelib.Data.List

open Purelib.Topology.Polygon

open Purelib.Topology.Surface.Cut

open Purelib.Topology.Surface.Cut.BoundaryPairs

open Purelib.Topology.Surface.Cut.BoundaryWord

open Purelib.Topology.Surface.Word

open Purelib.Topology.Surface.Word.SignedWord

public section

/-! Exact signed occurrence witnesses for each physical edge and cut pair. -/

namespace Purelib.Topology.Surface.Cut.AlphabetWitnesses

open Purelib.Topology.Polygon.Stokes (OrientedEdge)
open Purelib.Topology.Surface.Cut.BoundaryWord (CutAlphabet CutWordEntry)
open Purelib.Topology.Surface.Cut.BoundaryWord.CutAlphabet (ofLists)
open Purelib.Topology.Surface.Word.ProjectedEdgePairs (ProjectedEdgePairing)
open Purelib.Topology.Surface.Word.SignedWord (SignedGenerator)
open Purelib.Topology.Surface.Word.ProjectedEdgePairs (ProjectedEdgePair)

variable {source target : Nat} {labels : Fin source → Fin target} {edges : List (Stokes.OrientedEdge source)}

namespace CutAlphabet

/-- The retained occurrence list contains the given edge with the given signed generator. -/
@[expose] def Displays (bank : BoundaryWord.CutAlphabet labels edges) (edge : Stokes.OrientedEdge source) (letter :
  SignedWord.SignedGenerator bank.count) : Prop :=
  ∃ entry ∈ bank.entries, entry.edge = edge ∧ entry.letter = letter

open Purelib.Topology.Surface.Cut.AlphabetWitnesses in
/-- Restoring boundary order preserves an exact signed occurrence witness. -/
theorem Displays.reorder {original : List (Stokes.OrientedEdge source)} {bank : BoundaryWord.CutAlphabet labels
  original}
    {edge : Stokes.OrientedEdge source} {letter : SignedWord.SignedGenerator bank.count} (display : CutAlphabet.Displays
      bank edge letter)
    (edges : List (Stokes.OrientedEdge source)) (ordering : List.Perm original edges) :
    CutAlphabet.Displays (bank.reorder edges ordering) edge letter := by
  obtain ⟨entry, member, same⟩ := display
  exact ⟨entry, (bank.reorder_entries_iff edges ordering entry).mpr member, same⟩

/-- Prepending a generator shifts its occurrence indices without changing their cut edges. -/
private theorem shift_display {count : Nat}
    {generators : Data.Vector (Stokes.OrientedEdge source) count}
    {entries : List (BoundaryWord.CutWordEntry labels generators)} {edge : Stokes.OrientedEdge source} {letter :
      SignedWord.SignedGenerator count}
    (head : Stokes.OrientedEdge source)
    (display : ∃ entry ∈ entries, entry.edge = edge ∧ entry.letter = letter) :
    ∃ entry ∈ entries.map (CutWordEntry.shift head), entry.edge = edge ∧ entry.letter = letter.shift := by
  obtain ⟨entry, member, edgeEq, letterEq⟩ := display
  exact ⟨entry.shift head, Map.mem_map_of_mem member, edgeEq, congrArg SignedGenerator.shift letterEq⟩

open Purelib.Topology.Surface.Cut.AlphabetWitnesses
/-- Every retained cut pair supplies positive and negative occurrences of one paired generator. -/
theorem ofLists_pair : ∀ (physical : List (Stokes.OrientedEdge source)) (pairs : List
  (ProjectedEdgePairs.ProjectedEdgePair labels))
    (pair : ProjectedEdgePairs.ProjectedEdgePair labels), pair ∈ pairs → ∃ index,
      (CutAlphabet.ofLists physical pairs).oneSided index = false ∧
      CutAlphabet.Displays (CutAlphabet.ofLists physical pairs) pair.first ⟨index, false⟩ ∧
      CutAlphabet.Displays (CutAlphabet.ofLists physical pairs) pair.second ⟨index, true⟩ := by
  intro physical
  induction physical with
  | nil =>
      intro pairs
      induction pairs with
      | nil => exact fun _ member => (List.not_mem_nil member).elim
      | cons head pairs ih =>
          intro pair member
          rcases Membership.mem_cons.mp member with rfl | inTail
          · refine ⟨⟨0, Nat.zero_lt_succ _⟩, rfl, ?_, ?_⟩
            · exact ⟨⟨pair.first, ⟨⟨0, Nat.zero_lt_succ _⟩, false⟩, rfl⟩, List.mem_cons_self, rfl, rfl⟩
            · exact ⟨⟨pair.second, ⟨⟨0, Nat.zero_lt_succ _⟩, true⟩, pair.opposite⟩, List.mem_cons_of_mem _
                List.mem_cons_self, rfl, rfl⟩
          · obtain ⟨index, side, first, last⟩ := ih pair inTail
            refine ⟨index.succ, side, ?_, ?_⟩
            · obtain ⟨entry, member, same⟩ := CutAlphabet.shift_display head.first first
              exact ⟨entry, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ member), same⟩
            · obtain ⟨entry, member, same⟩ := CutAlphabet.shift_display head.first last
              exact ⟨entry, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ member), same⟩
  | cons head physical ih =>
      intro pairs pair member
      obtain ⟨index, side, first, last⟩ := ih pairs pair member
      refine ⟨index.succ, side, ?_, ?_⟩
      · obtain ⟨entry, member, same⟩ := CutAlphabet.shift_display head first
        exact ⟨entry, List.mem_cons_of_mem _ member, same⟩
      · obtain ⟨entry, member, same⟩ := CutAlphabet.shift_display head last
        exact ⟨entry, List.mem_cons_of_mem _ member, same⟩

/-- Every physical edge supplies the positive occurrence of a one-sided generator. -/
theorem ofLists_physical : ∀ (physical : List (Stokes.OrientedEdge source)) (pairs : List
  (ProjectedEdgePairs.ProjectedEdgePair labels))
    (edge : Stokes.OrientedEdge source), edge ∈ physical → ∃ index,
      (CutAlphabet.ofLists physical pairs).oneSided index = true ∧ CutAlphabet.Displays (CutAlphabet.ofLists physical
        pairs) edge ⟨index, false⟩ := by
  intro physical
  induction physical with
  | nil => exact fun _ _ member => (List.not_mem_nil member).elim
  | cons head physical ih =>
      intro pairs edge member
      rcases Membership.mem_cons.mp member with rfl | inTail
      · exact ⟨⟨0, Nat.zero_lt_succ _⟩, rfl, ⟨edge, ⟨⟨0, Nat.zero_lt_succ _⟩, false⟩, rfl⟩, List.mem_cons_self, rfl,
          rfl⟩
      · obtain ⟨index, side, displayed⟩ := ih pairs edge inTail
        obtain ⟨entry, member, same⟩ := CutAlphabet.shift_display head displayed
        exact ⟨index.succ, side, entry, List.mem_cons_of_mem _ member, same⟩

/-- Each constructed generator has a retained positive occurrence reading its exact source edge. -/
theorem ofLists_generator : ∀ (physical : List (Stokes.OrientedEdge source)) (pairs : List
  (ProjectedEdgePairs.ProjectedEdgePair labels))
    (index : Fin (CutAlphabet.ofLists physical pairs).count),
    CutAlphabet.Displays (CutAlphabet.ofLists physical pairs) ((CutAlphabet.ofLists physical pairs).generators index)
      ⟨index, false⟩ := by
  intro physical
  induction physical with
  | nil =>
      intro pairs
      induction pairs with
      | nil => exact fun index => Fin.elim0 index
      | cons head pairs ih =>
          intro index
          refine Data.Fin.cases_induction (motive := fun index =>
            CutAlphabet.Displays (CutAlphabet.ofLists [] (head :: pairs))
              ((CutAlphabet.ofLists [] (head :: pairs)).generators index) ⟨index, false⟩) ?_ (fun index => ?_) index
          · exact ⟨⟨head.first, ⟨⟨0, Nat.zero_lt_succ _⟩, false⟩, rfl⟩, List.mem_cons_self, rfl, rfl⟩
          · obtain ⟨entry, member, same⟩ := CutAlphabet.shift_display head.first (ih index)
            exact ⟨entry, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ member), same⟩
  | cons head physical ih =>
      intro pairs index
      refine Data.Fin.cases_induction (motive := fun index =>
        CutAlphabet.Displays (CutAlphabet.ofLists (head :: physical) pairs)
          ((CutAlphabet.ofLists (head :: physical) pairs).generators index) ⟨index, false⟩) ?_ (fun index => ?_) index
      · exact ⟨⟨head, ⟨⟨0, Nat.zero_lt_succ _⟩, false⟩, rfl⟩, List.mem_cons_self, rfl, rfl⟩
      · obtain ⟨entry, member, same⟩ := CutAlphabet.shift_display head (ih pairs index)
        exact ⟨entry, List.mem_cons_of_mem _ member, same⟩

end CutAlphabet

end Purelib.Topology.Surface.Cut.AlphabetWitnesses

namespace Purelib.Topology.Surface.Cut.AlphabetWitnesses.ProjectedEdgePairing

open Purelib.Topology.Polygon.Stokes (OrientedEdge)
open Purelib.Topology.Surface.Cut.BoundaryWord (CutAlphabet CutWordEntry)
open Purelib.Topology.Surface.Cut.BoundaryWord.CutAlphabet (ofLists)
open Purelib.Topology.Surface.Word.ProjectedEdgePairs (ProjectedEdgePairing)
open Purelib.Topology.Surface.Word.SignedWord (SignedGenerator)
open Purelib.Topology.Surface.Word.ProjectedEdgePairs (ProjectedEdgePair)

variable {source target : Nat} {labels : Fin source → Fin target} {edges : List (Stokes.OrientedEdge source)}

open Purelib.Topology.Surface.Cut.AlphabetWitnesses
open Purelib.Topology.Surface.Cut.AlphabetWitnesses.CutAlphabet
/-- The cyclic boundary word retains both signed occurrences of every original cut pair. -/
theorem boundaryWord_pair (pairing : ProjectedEdgePairs.ProjectedEdgePairing labels edges)
    (pair : ProjectedEdgePairs.ProjectedEdgePair labels) (member : pair ∈ pairing.pairs) : ∃ index,
    (ProjectedEdgePairing.boundaryWord pairing).alphabet.oneSided index = false ∧
    CutAlphabet.Displays (ProjectedEdgePairing.boundaryWord pairing).alphabet pair.first ⟨index, false⟩ ∧
    CutAlphabet.Displays (ProjectedEdgePairing.boundaryWord pairing).alphabet pair.second ⟨index, true⟩ := by
  obtain ⟨index, side, first, last⟩ := CutAlphabet.ofLists_pair pairing.boundary pairing.pairs pair member
  exact ⟨index, side, Displays.reorder first edges (List.Permutation.symm (EdgeReordering.toPerm pairing.incidence)),
    Displays.reorder last edges (List.Permutation.symm (EdgeReordering.toPerm pairing.incidence))⟩

/-- The cyclic boundary word retains the positive occurrence of each physical edge. -/
theorem boundaryWord_physical (pairing : ProjectedEdgePairs.ProjectedEdgePairing labels edges)
    (edge : Stokes.OrientedEdge source) (member : edge ∈ pairing.boundary) : ∃ index,
    (ProjectedEdgePairing.boundaryWord pairing).alphabet.oneSided index = true ∧ CutAlphabet.Displays
      (ProjectedEdgePairing.boundaryWord pairing).alphabet edge ⟨index, false⟩ := by
  obtain ⟨index, side, displayed⟩ := CutAlphabet.ofLists_physical pairing.boundary pairing.pairs edge member
  exact ⟨index, side, Displays.reorder displayed edges (List.Permutation.symm (EdgeReordering.toPerm
    pairing.incidence))⟩

/-- Every generator of the restored cyclic word has its exact positive occurrence witness. -/
theorem boundaryWord_generator (pairing : ProjectedEdgePairs.ProjectedEdgePairing labels edges) (index : Fin
  (ProjectedEdgePairing.boundaryWord pairing).alphabet.count) :
    CutAlphabet.Displays (ProjectedEdgePairing.boundaryWord pairing).alphabet ((ProjectedEdgePairing.boundaryWord
      pairing).alphabet.generators index) ⟨index, false⟩ :=
  Displays.reorder
    (CutAlphabet.ofLists_generator pairing.boundary pairing.pairs index) edges
    (List.Permutation.symm (EdgeReordering.toPerm pairing.incidence))

end Purelib.Topology.Surface.Cut.AlphabetWitnesses.ProjectedEdgePairing

end
