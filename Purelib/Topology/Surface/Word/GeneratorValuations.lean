module
import Purelib.Data.List.Membership
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Gaussian.Basic
import Purelib.Data.List.Map
import Purelib.Topology.Surface.Word.SignedWord

import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.BoundaryPairs
public import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Cut.Chord
import Purelib.Topology.Surface.Sewing.VertexSewing
import Purelib.Topology.Surface.Word.ProjectedEdgePairs
import Purelib.Topology.Surface.Chord.PairChordCoverage
import Purelib.Data.Vector.Basic
import Purelib.Tactic.Ring

open Purelib.Algebra

open Purelib.Data

open Purelib.Data.List

open Purelib.Topology.Polygon

open Purelib.Topology.Polygon.Stokes

open Purelib.Topology.Surface.Cut

open Purelib.Topology.Surface.Cut.BoundaryPairs

open Purelib.Topology.Surface.Cut.BoundaryWord

open Purelib.Topology.Surface.Cut.Chord

open Purelib.Topology.Surface.Cut.Chord.CutBoundaryWord
open _root_.Purelib.Topology.Surface.Cut.Chord renaming CutBoundaryWord -> Chord

open Purelib.Topology.Surface.Sewing.VertexSewing

open Purelib.Topology.Surface.Word

open Purelib.Topology.Surface.Word.SignedWord

public section

/-!+# Exact edge realization of arbitrary cut-generator values

Unique projected boundary incidence distinguishes positive generators, even
up to reversal. A finite signed indicator sum therefore extends any chosen
generator values to an antisymmetric surface-edge valuation. Physical edges
are located in the retained alphabet with their one-sided certificate.
-/

namespace Purelib.Topology.Surface.Word.GeneratorValuations

open Purelib.Topology.Surface.Cut.BoundaryWord (CutAlphabet CutWordEntry)
open Purelib.Topology.Surface.Word.ProjectedEdgePairs (ProjectedEdgePair ProjectedEdgePairing)

open Purelib.Topology.Surface.Chord.PairChordCoverage

open Purelib.Topology.Polygon.Stokes (OrientedEdge)
open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib.LinearAlgebra

variable {source target : Nat} {labels : Fin source → Fin target}

set_option genInjectivity false in
/-- A physical boundary edge located in its original cut alphabet.

The retained index carries both its one-sided certificate and exact generator equality. -/
private structure PhysicalGenerator {edges : List (Stokes.OrientedEdge source)}
    (bank : BoundaryWord.CutAlphabet labels edges) (edge : Stokes.OrientedEdge source) where
  /-- Original alphabet index of the physical edge. -/ index : Fin bank.count
  /-- The retained generator is certified one-sided. -/ physical : bank.oneSided index = true
  /-- The alphabet generator is the actual original physical edge. -/ generator_eq : bank.generators index = edge

constructive_injectivity PhysicalGenerator

/-- Find an original physical boundary occurrence in the alphabet built from boundary edges and pairs. -/
private def physicalGenerator (edge : Stokes.OrientedEdge source) (pairs : List (ProjectedEdgePairs.ProjectedEdgePair
  labels)) :
    (boundary : List (Stokes.OrientedEdge source)) → edge ∈ boundary → PhysicalGenerator
      (CutAlphabet.ofLists boundary pairs) edge
  | [], member => (List.not_mem_nil member).elim
  | head :: rest, member =>
      if same : head = edge then ⟨⟨0, Nat.zero_lt_succ _⟩, rfl, same⟩
      else
        let tail := physicalGenerator edge pairs rest
          ((Membership.mem_cons.mp member).resolve_left (Ne.symm same))
        ⟨tail.index.succ, tail.physical, tail.generator_eq⟩

namespace ProjectedEdgePairing

variable {edges : List (Stokes.OrientedEdge source)}

/-- Locate the unique positive letter for a retained cut generator. -/
private def positiveOccurrence (pairing : ProjectedEdgePairs.ProjectedEdgePairing labels edges) (index : Fin
  (ProjectedEdgePairing.boundaryWord pairing).alphabet.count) :
    Purelib.Topology.Surface.Cut.Chord.CutWordEntry.Occurrence ⟨index, false⟩ (ProjectedEdgePairing.boundaryWord
      pairing).alphabet.entries :=
  CutWordEntry.locate ⟨index, false⟩ _ (by
    rw [(ProjectedEdgePairing.boundaryWord pairing).alphabet.occurrences_eq, Bool.false_and]
    exact Nat.zero_lt_one)

/-- The selected positive occurrence has the original generator edge. -/
private theorem positive_edge (pairing : ProjectedEdgePairs.ProjectedEdgePairing labels edges) (index : Fin
  (ProjectedEdgePairing.boundaryWord pairing).alphabet.count) :
    (positiveOccurrence pairing index).entry.edge = (ProjectedEdgePairing.boundaryWord
      pairing).alphabet.generators index := by
  have provenance := ProjectedEdgePairing.boundaryWord_provenance pairing _ (positiveOccurrence
    pairing index).member
  unfold CutWordEntry.PairProvenance at provenance
  rw [(positiveOccurrence pairing index).letter_eq] at provenance
  exact provenance

/-- Projected boundary uniqueness transfers to the retained cut-word entries. -/
private theorem projected_entries_unique (pairing : ProjectedEdgePairs.ProjectedEdgePairing labels edges)
    (unique : (edges.map (OrientedEdge.map labels)).Nodup) :
    ((ProjectedEdgePairing.boundaryWord pairing).alphabet.entries.map (fun entry => (OrientedEdge.map labels
      entry.edge))).Nodup := by
  have mapped : (ProjectedEdgePairing.boundaryWord pairing).alphabet.entries.map (fun entry => (OrientedEdge.map labels
    entry.edge)) =
      edges.map (OrientedEdge.map labels) := by
    exact (Map.map_map (OrientedEdge.map labels) CutWordEntry.edge _).symm.trans
      (congrArg (List.map (OrientedEdge.map labels)) (ProjectedEdgePairing.boundaryWord pairing).alphabet.edges_eq)
  exact mapped.symm ▸ unique

/-- Distinct cut generators have distinct projected edges under unique projected incidence. -/
theorem generator_projected_injective (pairing : ProjectedEdgePairs.ProjectedEdgePairing labels edges)
    (unique : (edges.map (OrientedEdge.map labels)).Nodup) (first last : Fin (ProjectedEdgePairing.boundaryWord
      pairing).alphabet.count)
    (same : (OrientedEdge.map labels ((ProjectedEdgePairing.boundaryWord pairing).alphabet.generators first)) =
      (OrientedEdge.map labels ((ProjectedEdgePairing.boundaryWord pairing).alphabet.generators last))) : first = last
        := by
  have equal := Map.equal_of_map_unique (fun entry => (OrientedEdge.map labels entry.edge))
    ((projected_entries_unique pairing unique))
    (positiveOccurrence pairing first).member (positiveOccurrence pairing
      last).member (by
      rw [positive_edge, positive_edge]; exact same)
  have letters := congrArg CutWordEntry.letter equal
  rw [(positiveOccurrence pairing first).letter_eq, (positiveOccurrence
    pairing last).letter_eq] at letters
  exact congrArg SignedGenerator.index letters

/-- Positive generators cannot project to each other's reverse under unique projected incidence. -/
theorem generator_projected_ne_reverse (pairing : ProjectedEdgePairs.ProjectedEdgePairing labels edges)
    (unique : (edges.map (OrientedEdge.map labels)).Nodup) (first last : Fin (ProjectedEdgePairing.boundaryWord
      pairing).alphabet.count) :
    (OrientedEdge.map labels ((ProjectedEdgePairing.boundaryWord pairing).alphabet.generators first)) ≠
      ((OrientedEdge.map labels ((ProjectedEdgePairing.boundaryWord pairing).alphabet.generators last))).reverse := by
  intro same
  cases side : (ProjectedEdgePairing.boundaryWord pairing).alphabet.oneSided last
  · let chord := Chord.build (ProjectedEdgePairing.boundaryWord pairing) last side
    have equal := Map.equal_of_map_unique (fun entry => (OrientedEdge.map labels entry.edge))
      ((projected_entries_unique pairing unique))
      (positiveOccurrence pairing first).member (chord.first.rest_mem chord.last.member) (by
        rw [positive_edge, chord.last.entry.projected_eq, chord.last.letter_eq]
        exact same)
    have letters := congrArg CutWordEntry.letter equal
    rw [(positiveOccurrence pairing first).letter_eq, chord.last.letter_eq] at letters
    have impossible := congrArg SignedGenerator.reversed letters
    cases impossible
  · have missing := ((ProjectedEdgePairing.boundary_iff pairing unique _).mp
      (Map.mem_map_of_mem (ProjectedEdgePairing.oneSided_generator_mem pairing last side))).2
    have member : (OrientedEdge.map labels ((ProjectedEdgePairing.boundaryWord pairing).alphabet.generators first)) ∈
      edges.map (OrientedEdge.map labels) := by
      have cutMember := (congrArg (fun bank => (positiveOccurrence pairing first).entry.edge ∈
        bank)
        (ProjectedEdgePairing.boundaryWord pairing).alphabet.edges_eq).mp
        (Map.mem_map_of_mem (positiveOccurrence pairing first).member)
      rw [← positive_edge pairing first]
      exact Map.mem_map_of_mem cutMember
    exact missing (same ▸ member)

/-- The signed indicator difference is antisymmetric on every edge, including edges outside the retained boundary. -/
@[expose] def generatorValue (pairing : ProjectedEdgePairs.ProjectedEdgePairing labels edges)
    (values : Fin (ProjectedEdgePairing.boundaryWord pairing).alphabet.count → Gaussian.Basic.Canonical) (edge :
      Stokes.OrientedEdge target) : Gaussian.Basic.Canonical :=
  FiniteSum.Fin.sumFin fun index =>
    (if edge = (OrientedEdge.map labels ((ProjectedEdgePairing.boundaryWord pairing).alphabet.generators index)) then
      values index else 0) -
    (if edge.reverse = (OrientedEdge.map labels ((ProjectedEdgePairing.boundaryWord pairing).alphabet.generators index))
      then values index else 0)

/-- The finite signed-indicator valuation negates under edge reversal. -/
theorem generatorValue_reverse (pairing : ProjectedEdgePairs.ProjectedEdgePairing labels edges)
    (values : Fin (ProjectedEdgePairing.boundaryWord pairing).alphabet.count → Gaussian.Basic.Canonical) (edge :
      Stokes.OrientedEdge target) :
    generatorValue pairing values edge.reverse = -generatorValue pairing
      values edge := by
  rw [generatorValue, generatorValue, ← FiniteSum.Fin.sumFin_neg]
  apply FiniteSum.Fin.sumFin_congr
  intro index
  rw [OrientedEdge.reverse_reverse]
  ring1

/-- The constructed edge valuation recovers each prescribed generator value exactly. -/
theorem generatorValue_generator (pairing : ProjectedEdgePairs.ProjectedEdgePairing labels edges)
    (unique : (edges.map (OrientedEdge.map labels)).Nodup)
    (values : Fin (ProjectedEdgePairing.boundaryWord pairing).alphabet.count → Gaussian.Basic.Canonical) (selected : Fin
      (ProjectedEdgePairing.boundaryWord pairing).alphabet.count) :
    generatorValue pairing values ((OrientedEdge.map labels ((ProjectedEdgePairing.boundaryWord
      pairing).alphabet.generators selected))) = values selected := by
  calc
    _ = FiniteSum.Fin.sumFin (fun index => if index = selected then values index else 0) := by
      apply FiniteSum.Fin.sumFin_congr
      intro index
      have reverseMissing : ((OrientedEdge.map labels ((ProjectedEdgePairing.boundaryWord pairing).alphabet.generators
        selected))).reverse ≠
          (OrientedEdge.map labels ((ProjectedEdgePairing.boundaryWord pairing).alphabet.generators index)) :=
        Ne.symm ((generator_projected_ne_reverse pairing unique index selected))
      rw [if_neg reverseMissing, Gaussian.Basic.sub_zero]
      by_cases same : index = selected
      · subst index
        rw [if_pos rfl, if_pos rfl]
      · rw [if_neg (fun equal => same (generator_projected_injective pairing unique selected index
          equal).symm), if_neg same]
    _ = _ := FiniteSum.Fin.sumFin_ite_eq selected _

/-- Zero values on one-sided generators make the constructed valuation vanish on physical boundary edges. -/
theorem generatorValue_physical (pairing : ProjectedEdgePairs.ProjectedEdgePairing labels edges)
    (unique : (edges.map (OrientedEdge.map labels)).Nodup)
    (values : Fin (ProjectedEdgePairing.boundaryWord pairing).alphabet.count → Gaussian.Basic.Canonical)
    (zero : ∀ index, (ProjectedEdgePairing.boundaryWord pairing).alphabet.oneSided index = true → values index = 0)
    (edge : Stokes.OrientedEdge source) (member : edge ∈ pairing.boundary) : generatorValue pairing
      values ((OrientedEdge.map labels edge)) = 0 := by
  let selected := physicalGenerator edge pairing.pairs pairing.boundary member
  have equal : (ProjectedEdgePairing.boundaryWord pairing).alphabet.generators selected.index = edge :=
    selected.generator_eq
  rw [← equal, generatorValue_generator pairing unique]
  exact zero selected.index selected.physical

end ProjectedEdgePairing
end Purelib.Topology.Surface.Word.GeneratorValuations
