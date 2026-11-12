module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Map
-- The exposed first-occurrence selection retains this membership certificate.
public import Purelib.Data.List.Membership
import Purelib.Data.Nat.Order
import Purelib.Data.Vector.Basic

import Purelib.Data.List.Permutation
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.VertexSewing
import Purelib.Topology.Surface.Word.Pairing
import Purelib.Topology.Surface.Word.ProjectedEdgePairs
public import Purelib.Topology.Surface.Word.SignedWord
public import Purelib.Topology.Surface.Cut.BoundaryPairs
import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
import Batteries.Logic
meta import Mathlib.Tactic.Linter.Lint

public section

/-!
# Signed words extracted from the actual cyclic cut boundary

Generators are the retained one-sided edges followed by one edge of each cut
pair. Every word occurrence stores the exact original cut edge and proves
its projected orientation relative to its generator. Reordering restores the
original cyclic boundary order before computing the integer area signature.
-/

namespace Purelib.Topology.Surface.Cut.BoundaryWord
open Purelib
open Purelib.Data
open Purelib.Data.List
open Purelib.Topology.Polygon
open Purelib.Topology.Surface.Cut.BoundaryPairs
open Purelib.Topology.Surface.Sewing.VertexSewing
open Purelib.Topology.Surface.Word
open Purelib.Topology.Surface.Word.Pairing
open Purelib.Topology.Surface.Word.ProjectedEdgePairs
open Purelib.Topology.Surface.Word.SignedWord

open Purelib.Topology.Polygon.Stokes (OrientedEdge)
open Purelib.Topology.Surface.Word.SignedWord (SignedGenerator)
open Purelib.Topology.Surface.Word.ProjectedEdgePairs (ProjectedEdgePair ProjectedEdgePairing)

open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)

variable {source target : Nat} {labels : Fin source → Fin target}

set_option genInjectivity false in
/-- One original cut-edge occurrence and its signed generator.

The projection equation retains its exact orientation relative to the supplied generator bank. -/
structure CutWordEntry {count : Nat} (labels : Fin source → Fin target)
    (generators : Data.Vector (OrientedEdge source) count) where
  /-- The original directed cut-edge occurrence. -/ edge : OrientedEdge source
  /-- Its signed index in the retained generator bank. -/ letter : SignedGenerator count
  /-- The original edge projects to the generator in exactly the retained orientation. -/ projected_eq :
    OrientedEdge.map labels edge =
    if letter.reversed then (OrientedEdge.map labels (generators letter.index)).reverse else OrientedEdge.map labels
      (generators letter.index)

constructive_injectivity CutWordEntry

namespace CutWordEntry

variable {count : Nat} {generators : Data.Vector (OrientedEdge source) count}

open Purelib.Topology.Surface.Cut in
/-- Shift an occurrence's generator index after prepending one generator, retaining its source edge. -/
@[expose] def shift (head : OrientedEdge source) (entry : CutWordEntry labels generators) :
  CutWordEntry labels (.cons head generators) :=
  ⟨entry.edge, entry.letter.shift, entry.projected_eq⟩

section
open Purelib.Topology.Surface.Cut
open Purelib.Topology.Surface.Cut.BoundaryWord
/-- Shifting generator indices leaves the list of original cut edges unchanged. -/
theorem shift_edges (head : OrientedEdge source) : (entries : List (CutWordEntry labels generators))
  →
    (entries.map (shift head)).map CutWordEntry.edge =
      entries.map CutWordEntry.edge
  | [] => rfl
  | entry :: entries => congrArg (List.cons entry.edge)
    (CutWordEntry.shift_edges head entries)

/-- Reading letters after shifting agrees with shifting the original signed-letter list. -/
theorem shift_letters (head : OrientedEdge source) : (entries : List (CutWordEntry labels
  generators)) →
    (entries.map (shift head)).map CutWordEntry.letter =
      (entries.map CutWordEntry.letter).map SignedGenerator.shift
  | [] => rfl
  | entry :: entries => congrArg (List.cons entry.letter.shift)
    (CutWordEntry.shift_letters head entries)

end

open Purelib.Topology.Surface.Cut in
/-- Exact cut-occurrence provenance, stronger than equality after projection. A reversed letter reads the second edge of
an actual retained pair; its generator is that same pair's first edge. -/
@[expose] def PairProvenance (pairs : List (ProjectedEdgePair labels)) (entry :
  CutWordEntry labels generators) : Prop :=
  if entry.letter.reversed then
    ∃ pair ∈ pairs, generators entry.letter.index = pair.first ∧ entry.edge = pair.second
  else entry.edge = generators entry.letter.index

open Purelib.Topology.Surface.Cut in
open Purelib.Topology.Surface.Cut.BoundaryWord in
/-- Exact pair provenance persists when the retained pair list is enlarged. -/
theorem PairProvenance.mono {first last : List (ProjectedEdgePair labels)}
    {entry : CutWordEntry labels generators} (provenance : entry.PairProvenance first)
    (included : ∀ pair ∈ first, pair ∈ last) : entry.PairProvenance last := by
  unfold PairProvenance at provenance ⊢
  split at provenance
  · rename_i reversed
    rw [if_pos reversed]
    obtain ⟨pair, member, equal⟩ := provenance
    exact ⟨pair, included pair member, equal⟩
  · rename_i forward
    rw [if_neg forward]
    exact provenance

end CutWordEntry

open Purelib.Topology.Surface.Cut in
set_option genInjectivity false in
/-- An executable generator alphabet and its exact cut-edge occurrences.

The retained generators and orientation flags specify the original occurrence
bank. Its edge readback and signed multiplicity certificates permit a bank
before cyclic reordering without changing the indexed edge list. -/
structure CutAlphabet (labels : Fin source → Fin target) (edges : List (OrientedEdge source)) where
  /-- Number of retained physical and paired generators. -/ count : Nat
  /-- Cached original cut edge for each generator index. -/ generators : Data.Vector (OrientedEdge
    source) count
  /-- Flag identifying generators that occur only with positive physical-boundary orientation. -/ oneSided :
    Data.Vector Bool count
  /-- Original cut-edge occurrences with their signed generator identities. -/ entries : List (CutWordEntry
    labels generators)
  /-- Reading the retained source edges recovers the indexed edge list exactly. -/ edges_eq : entries.map
    CutWordEntry.edge = edges
  /-- Paired generators occur once in each orientation, while physical generators occur only positively. -/
    occurrences_eq : ∀ index reversed,
    SignedGenerator.occurrences ⟨index, reversed⟩ (entries.map
      CutWordEntry.letter) =
      if reversed && oneSided index then 0 else 1

constructive_injectivity CutAlphabet

namespace CutAlphabet

section
open Purelib.Topology.Surface.Cut
open Purelib.Topology.Surface.Cut.BoundaryWord
/-- Build a generator bank with both signed occurrences of each retained cut pair.

Each pair's first edge is its generator, and the second edge uses the negative orientation of that same index. -/
@[expose] def ofPairs : (pairs : List (ProjectedEdgePair labels)) → CutAlphabet labels
  (ProjectedEdgePair.occurrences pairs)
  | [] => ⟨0, .nil, .nil, [], rfl, fun index => Fin.elim0 index⟩
  | pair :: pairs =>
      let tail := CutAlphabet.ofPairs pairs
      { count := tail.count + 1
        generators := .cons pair.first tail.generators
        oneSided := .cons false tail.oneSided
        entries := ⟨pair.first, ⟨0, false⟩, rfl⟩ :: ⟨pair.second, ⟨0, true⟩, pair.opposite⟩ ::
          tail.entries.map (CutWordEntry.shift pair.first)
        edges_eq := by
          rw [List.map_cons, List.map_cons, CutWordEntry.shift_edges, tail.edges_eq]
          rfl
        occurrences_eq := by
          intro index reversed
          rcases index with ⟨value, bound⟩
          cases value with
          | zero =>
            change SignedGenerator.occurrences ⟨0, reversed⟩ _ = _
            rw [List.map_cons, List.map_cons, CutWordEntry.shift_letters, SignedGenerator.occurrences,
              SignedGenerator.occurrences, SignedGenerator.occurrences_shift_zero]
            have opposite : (⟨0, true⟩ : SignedGenerator (tail.count + 1)) ≠ ⟨0, false⟩ :=
              fun equal => Bool.noConfusion (congrArg SignedGenerator.reversed equal)
            cases reversed with
            | false =>
                rewrite [if_pos (Eq.refl (⟨0, false⟩ : SignedGenerator (tail.count + 1))),
                  if_neg opposite]
                rfl
            | true =>
                rewrite [if_neg opposite.symm,
                  if_pos (Eq.refl (⟨0, true⟩ : SignedGenerator (tail.count + 1)))]
                rfl
          | succ value =>
            let index : Fin tail.count := ⟨value, Nat.lt_of_succ_lt_succ bound⟩
            have retained : (⟨value + 1, bound⟩ : Fin (tail.count + 1)) = index.succ := rfl
            rw [retained]
            have different : (⟨0, false⟩ : SignedGenerator (tail.count + 1)) ≠ ⟨index.succ, reversed⟩ := by
              intro same
              exact Nat.noConfusion (congrArg (fun letter => letter.index.val) same).symm
            rw [List.map_cons, List.map_cons, CutWordEntry.shift_letters, SignedGenerator.occurrences,
              if_neg different,
              SignedGenerator.occurrences,
              if_neg (fun same => Nat.noConfusion (congrArg (fun letter => letter.index.val) same).symm)]
            change 0 + (0 + SignedGenerator.occurrences (SignedGenerator.shift ⟨index, reversed⟩)
              ((tail.entries.map CutWordEntry.letter).map
                SignedGenerator.shift)) = _
            rw [SignedGenerator.occurrences_shift, tail.occurrences_eq, Nat.zero_add, Nat.zero_add]
            rfl }

/-- Give each one-sided edge and each cut pair one generator.

Each physical edge contributes only its positive occurrence. Each retained
cut pair contributes both orientations of its single generator, while the
original tail entries and generator bank remain cached. -/
@[expose] def ofLists : (boundary : List (OrientedEdge source)) → (pairs : List
  (ProjectedEdgePair labels)) →
    CutAlphabet labels (boundary ++ ProjectedEdgePair.occurrences pairs)
  | [], pairs => ofPairs pairs
  | edge :: boundary, pairs =>
      let tail := CutAlphabet.ofLists boundary pairs
      { count := tail.count + 1
        generators := .cons edge tail.generators
        oneSided := .cons true tail.oneSided
        entries := ⟨edge, ⟨0, false⟩, rfl⟩ :: tail.entries.map (CutWordEntry.shift edge)
        edges_eq := by rw [List.map_cons, CutWordEntry.shift_edges, tail.edges_eq]; rfl
        occurrences_eq := by
          intro index reversed
          rcases index with ⟨value, bound⟩
          cases value with
          | zero =>
            change SignedGenerator.occurrences ⟨0, reversed⟩ _ = _
            rw [List.map_cons, CutWordEntry.shift_letters, SignedGenerator.occurrences,
              SignedGenerator.occurrences_shift_zero]
            have opposite : (⟨0, false⟩ : SignedGenerator (tail.count + 1)) ≠ ⟨0, true⟩ :=
              fun same => Bool.noConfusion (congrArg SignedGenerator.reversed same)
            cases reversed with
            | false =>
                rw [if_pos (Eq.refl (⟨0, false⟩ : SignedGenerator (tail.count + 1)))]
                rfl
            | true =>
                rw [if_neg opposite]
                rfl
          | succ value =>
            let index : Fin tail.count := ⟨value, Nat.lt_of_succ_lt_succ bound⟩
            have retained : (⟨value + 1, bound⟩ : Fin (tail.count + 1)) = index.succ := rfl
            rw [retained]
            have different : (⟨0, false⟩ : SignedGenerator (tail.count + 1)) ≠ ⟨index.succ, reversed⟩ := by
              intro same
              exact Nat.noConfusion (congrArg (fun letter => letter.index.val) same).symm
            rw [List.map_cons, CutWordEntry.shift_letters, SignedGenerator.occurrences,
              if_neg different]
            change 0 + SignedGenerator.occurrences (SignedGenerator.shift ⟨index, reversed⟩)
              ((tail.entries.map CutWordEntry.letter).map
                SignedGenerator.shift) = _
            rw [SignedGenerator.occurrences_shift, tail.occurrences_eq, Nat.zero_add]
            rfl }

end

section
open Purelib.Topology.Surface.Cut.BoundaryWord
/-- The paired alphabet retains the exact original pair behind every negative occurrence.

Each new negative occurrence is certified by its displayed cut pair. Every
shifted occurrence retains the pair and generator equation already present
in the cached tail alphabet. -/
private theorem ofPairs_provenance : (pairs : List (ProjectedEdgePair labels)) →
    ∀ entry ∈ (ofPairs pairs).entries, entry.PairProvenance pairs
  | [], _, member => (List.not_mem_nil member).elim
  | pair :: pairs, entry, member => by
      rcases Membership.mem_cons.mp member with same | member
      · cases same; rfl
      · rcases Membership.mem_cons.mp member with same | member
        · cases same
          exact ⟨pair, List.mem_cons_self, rfl, rfl⟩
        · obtain ⟨original, originalMember, same⟩ := Map.mem_map.mp member
          cases same
          exact (CutAlphabet.ofPairs_provenance pairs original
            originalMember).mono
            (fun _ present => List.mem_cons_of_mem pair present)

/-- Adding physical generators preserves exact pair provenance of every negative occurrence.

Each added physical edge has positive orientation and retains its own
generator. Shifted negative occurrences keep the original cut-pair witness
and projected orientation equation of the cached tail. -/
theorem ofLists_provenance : (boundary : List (OrientedEdge source)) → (pairs : List
  (ProjectedEdgePair labels)) →
    ∀ entry ∈ (ofLists boundary pairs).entries, entry.PairProvenance pairs
  | [], pairs, entry, member => ofPairs_provenance pairs entry member
  | edge :: boundary, pairs, entry, member => by
      rcases Membership.mem_cons.mp member with same | member
      · cases same; rfl
      · obtain ⟨original, originalMember, same⟩ := Map.mem_map.mp member
        cases same
        exact CutAlphabet.ofLists_provenance boundary pairs original
          originalMember

end

/-- Mapping entries transports their retained list permutation. -/
theorem mapPermutation {α β : Type} (value : α → β) {first second : List α}
    (ordering : List.Perm first second) : List.Perm (first.map value) (second.map value) := by
  induction ordering with
  | nil => exact .nil
  | cons head tail ih => exact .cons (value head) ih
  | swap first second rest => exact .swap (value first) (value second) _
  | trans first second ihFirst ihSecond => exact .trans ihFirst ihSecond

open Purelib.Topology.Surface.Cut in
set_option genInjectivity false in
/-- A selected original occurrence and the residual occurrence bank.

The exact source-edge equation and permutation identify which occurrence was removed, preserving multiplicity. -/
structure Selected {count : Nat}
    (generators : Data.Vector (OrientedEdge source) count)
    (bank : List (CutWordEntry labels generators)) (edge : OrientedEdge source) where
  /-- The selected original occurrence. -/ entry : CutWordEntry labels generators
  /-- The selected occurrence has the requested cut edge. -/ edge_eq : entry.edge = edge
  /-- Residual bank after removing the selected occurrence. -/ remaining : List (CutWordEntry labels
    generators)
  /-- Exact permutation moving the selected occurrence before the residual bank. -/ ordering : List.Perm bank (entry ::
    remaining)

constructive_injectivity Selected

open Purelib.Topology.Surface.Cut in
open Purelib.Topology.Surface.Cut.BoundaryWord in
/-- Select the first occurrence with the requested original edge and retain the residual bank.

A membership witness makes the finite search total; no occurrence is duplicated or discarded silently. -/
@[expose] def select {count : Nat} {generators : Data.Vector (OrientedEdge source) count}
    (edge : OrientedEdge source) : (entries : List (CutWordEntry labels generators)) →
    edge ∈ entries.map CutWordEntry.edge → Selected generators
      entries edge
  | [], member => (List.not_mem_nil member).elim
  | first :: rest, member =>
      if same : first.edge = edge then ⟨first, same, rest, Permutation.refl _⟩
      else
        let tail := CutAlphabet.select edge rest ((Membership.mem_cons.mp
          member).resolve_left (Ne.symm same))
        ⟨tail.entry, tail.edge_eq, first :: tail.remaining,
          (List.Perm.cons first tail.ordering).trans (.swap tail.entry first tail.remaining)⟩

open Purelib.Topology.Surface.Cut in
set_option genInjectivity false in
/-- Original occurrence entries reordered to an exact requested edge list.

The edge readback and retained permutation preserve the complete original bank and its multiplicities. -/
structure OrderedEntries {count : Nat}
    (generators : Data.Vector (OrientedEdge source) count)
    (bank : List (CutWordEntry labels generators)) (edges : List (OrientedEdge source)) where
  /-- Retained entries in the requested edge order. -/ entries : List (CutWordEntry labels generators)
  /-- Their source-edge readback is the exact requested edge list. -/ edges_eq : entries.map
    CutWordEntry.edge = edges
  /-- The reordered entries contain exactly the original bank with multiplicity. -/ ordering : List.Perm entries bank

constructive_injectivity OrderedEntries

section
open Purelib.Topology.Surface.Cut
open Purelib.Topology.Surface.Cut.BoundaryWord
/-- Restore the requested edge order by selecting and removing one occurrence at a time.

The supplied permutation proves each search succeeds and that no original
entry remains unused. Each step retains the selected occurrence and its
original remainder, cancelling only the displayed common edge in the
permutation certificate. -/
@[expose] def order {count : Nat} {generators : Data.Vector (OrientedEdge source) count}
    (bank : List (CutWordEntry labels generators)) : (edges : List (OrientedEdge source)) →
    List.Perm (bank.map CutWordEntry.edge) edges → OrderedEntries
      generators bank edges
  | [], covered =>
      ⟨[], rfl, by
        have lengthZero : bank.length = 0 :=
          (Map.length_map CutWordEntry.edge bank).symm.trans
            (Permutation.length_eq covered)
        have empty : bank = [] := by
          cases bank with
          | nil => rfl
          | cons head tail => exact Nat.noConfusion lengthZero
        rw [empty]⟩
  | edge :: rest, covered =>
      let first := select edge bank ((Permutation.mem_iff covered edge).mpr List.mem_cons_self)
      have remaining : List.Perm (first.remaining.map CutWordEntry.edge) rest
        := by
        have all := (Permutation.symm (mapPermutation
          CutWordEntry.edge first.ordering)).trans covered
        rw [List.map_cons, first.edge_eq] at all
        exact Permutation.cons_inv all
      let tail := CutAlphabet.order first.remaining rest remaining
      ⟨first.entry :: tail.entries, congrArg₂ List.cons first.edge_eq tail.edges_eq,
        (List.Perm.cons first.entry tail.ordering).trans (Permutation.symm first.ordering)⟩

/-- Restore the requested edge order of an original occurrence bank.

The supplied edge permutation makes each original first-occurrence
selection total. Removing that selected entry preserves multiplicity even
when two cut edges are equal, and retains the original generator bank. -/
@[expose] def reorder {sourceEdges : List (OrientedEdge source)} (bank : CutAlphabet labels
  sourceEdges)
    (edges : List (OrientedEdge source)) (covered : List.Perm sourceEdges edges) : CutAlphabet
      labels edges :=
  let ordered := order bank.entries edges (by rw [bank.edges_eq]; exact covered)
  ⟨bank.count, bank.generators, bank.oneSided, ordered.entries, ordered.edges_eq, fun index reversed =>
    (SignedGenerator.occurrences_perm ⟨index, reversed⟩ (mapPermutation
      CutWordEntry.letter ordered.ordering)).trans
      (bank.occurrences_eq index reversed)⟩

/-- Reordering preserves every literal occurrence, including its signed generator and the original cut edge. -/
theorem reorder_entries_iff {sourceEdges : List (OrientedEdge source)} (bank : CutAlphabet labels
  sourceEdges)
    (edges : List (OrientedEdge source)) (covered : List.Perm sourceEdges edges)
    (entry : CutWordEntry labels bank.generators) :
    entry ∈ (bank.reorder edges covered).entries ↔ entry ∈ bank.entries :=
  Permutation.mem_iff
    (order bank.entries edges (by rw [bank.edges_eq]; exact covered)).ordering entry

/-- Restoring cyclic boundary order preserves every retained entry's exact pair provenance. -/
theorem reorder_provenance {sourceEdges : List (OrientedEdge source)} (bank : CutAlphabet labels
  sourceEdges)
    (edges : List (OrientedEdge source)) (covered : List.Perm sourceEdges edges)
    (pairs : List (ProjectedEdgePair labels)) (provenance : ∀ entry ∈ bank.entries,
      entry.PairProvenance pairs) :
    ∀ entry ∈ (bank.reorder edges covered).entries, entry.PairProvenance pairs := by
  intro entry member
  apply provenance entry
  exact (Permutation.mem_iff
    (order bank.entries edges (by rw [bank.edges_eq]; exact covered)).ordering entry).mp member

end

open Purelib.Topology.Surface.Cut in
/-- Every retained generator projects to a displayed boundary occurrence.

Its positive signed multiplicity supplies an original entry with that
generator index and orientation. The entry's source-edge readback and
projection certificate identify the retained projected boundary member. -/
theorem generator_projected_mem (alphabet : CutAlphabet labels edges) (index : Fin alphabet.count) :
    OrientedEdge.map labels (alphabet.generators index) ∈ edges.map (OrientedEdge.map labels) := by
  have count_eq : SignedGenerator.occurrences ⟨index, false⟩
      (alphabet.entries.map CutWordEntry.letter) = 1 := by
    rw [alphabet.occurrences_eq]
    rfl
  obtain ⟨entry, entry_mem, letter_eq⟩ :=
    Map.mem_map.mp (SignedGenerator.mem_of_occurrences_eq_one count_eq)
  have edge_mem : entry.edge ∈ edges := by
    have listed : entry.edge ∈ alphabet.entries.map CutWordEntry.edge :=
      Map.mem_map.mpr ⟨entry, entry_mem, rfl⟩
    rwa [alphabet.edges_eq] at listed
  have projected : OrientedEdge.map labels entry.edge = OrientedEdge.map labels (alphabet.generators index) := by
    rw [entry.projected_eq, letter_eq]
    rfl
  rw [← projected]
  exact Map.mem_map.mpr ⟨entry.edge, edge_mem, rfl⟩

end CutAlphabet

open Purelib.Topology.Surface.Cut in
set_option genInjectivity false in
/-- An actual cyclic cut word with its cached integer alternating area matrix.

The retained alphabet determines the exact cached signed letters and their
coefficient word. Its signature belongs to those same coefficients; no
symplectic normal form is asserted. -/
structure CutBoundaryWord (labels : Fin source → Fin target) (edges : List (OrientedEdge source)) where
  /-- Original generator and occurrence bank in cyclic edge order. -/ alphabet : CutAlphabet labels edges
  /-- Cached signed generator word of the retained occurrences. -/ letters : List (SignedGenerator
    alphabet.count)
  /-- The signed word reads the exact letters of the retained entries. -/ letters_eq : letters = alphabet.entries.map
    CutWordEntry.letter
  /-- Cached integral coefficient vector for each signed occurrence. -/ coefficients : List (Coefficients
    alphabet.count)
  /-- The coefficient word is the direct readback of the cached signed letters. -/ coefficients_eq : coefficients =
    letters.map SignedGenerator.coefficients
  /-- Retained total vector and alternating area matrix of the exact coefficient word. -/ signature : Signature
    coefficients

constructive_injectivity CutBoundaryWord

namespace ProjectedEdgePairing

variable {edges : List (OrientedEdge source)}

open Purelib.Topology.Surface.Cut in
open Purelib.Topology.Surface.Cut.BoundaryWord in
/-- Complete automatic extraction from the already checked occurrence pairing. The original cyclic edge order is
restored before forming a matrix. -/
@[expose] def boundaryWord (pairing : ProjectedEdgePairing labels edges) :
  CutBoundaryWord labels edges :=
  let source := CutAlphabet.ofLists pairing.boundary pairing.pairs
  let alphabet := source.reorder edges (Permutation.symm (EdgeReordering.toPerm pairing.incidence))
  let letters := alphabet.entries.map CutWordEntry.letter
  let coefficients := letters.map SignedGenerator.coefficients
  { alphabet := alphabet
    letters := letters
    letters_eq := rfl
    coefficients := coefficients
    coefficients_eq := rfl
    signature := Signature.build coefficients }

open Purelib.Topology.Surface.Cut.BoundaryWord in
/-- Restoring cyclic order retains literal pair provenance. This applies to any checked pairing cache, without equality
to the canonical pairing scan. -/
theorem boundaryWord_provenance (pairing : ProjectedEdgePairing labels edges) :
    ∀ entry ∈ (boundaryWord pairing).alphabet.entries, entry.PairProvenance pairing.pairs :=
  (CutAlphabet.ofLists pairing.boundary pairing.pairs).reorder_provenance edges
    (Permutation.symm (EdgeReordering.toPerm pairing.incidence)) pairing.pairs
    (CutAlphabet.ofLists_provenance pairing.boundary pairing.pairs)

end ProjectedEdgePairing

end Purelib.Topology.Surface.Cut.BoundaryWord
