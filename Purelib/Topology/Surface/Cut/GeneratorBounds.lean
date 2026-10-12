module
import Purelib.Data.List.Map

public import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.BoundaryWord
public import Purelib.Topology.Surface.Cut.WordArea
import Purelib.Topology.Surface.Cut.WordErrors
import Purelib.Topology.Surface.Word.ProjectedEdgePairs
import Purelib.Topology.Surface.Cut.Chord
import Purelib.Topology.Surface.Cut.WordAreaBounds
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Field
import Mathlib.Data.Int.Cast.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Data.Nat.Cast.Defs
import Purelib.Data.Vector.Basic
import Mathlib.Data.Nat.Init

open Purelib.Data.List

open Purelib.Riemann.Readings

open Purelib.Riemann.Readings.PrimitiveAreaBounds

open Purelib.Topology.Polygon

open Purelib.Topology.Surface.Cut

open Purelib.Topology.Surface.Cut.BoundaryWord

open Purelib.Topology.Surface.Cut.WordArea

open Purelib.Topology.Surface.Cut.WordAreaBounds.PrimitivePoint

open Purelib.Topology.Surface.Cut.WordErrors.CutBoundaryWord

open Purelib.Topology.Surface.Word

@[expose] public section

/-!
# Magnitudes of the actual retained boundary generators

Positive signed multiplicity locates an original occurrence. Its exact
pairing provenance identifies the generator before applying endpoint bounds;
equality only after projection would not suffice for cut primitives.
-/

namespace Purelib.Topology.Surface.Cut.GeneratorBounds

open Purelib.Topology.Surface.Cut.Chord
open Purelib.Topology.Surface.Cut.WordAreaBounds
open Purelib.Topology.Surface.Word.ProjectedEdgePairs (ProjectedEdgePairing)
open Purelib.Topology.Surface.Cut.BoundaryWord (CutBoundaryWord)
open Purelib.Topology.Surface.Cut.WordArea.CutBoundaryWord (AreaSample)
open Purelib.Riemann.Readings.PrimitiveAreaBounds (AreaCoordinate)

open Purelib.Topology.Polygon.Stokes (OrientedEdge PrimitivePoint)

variable {source target : Nat} {labels : Fin source → Fin target} {edges : List (Stokes.OrientedEdge source)}

/-- Each retained generator is an actual original cut-edge occurrence, before projection. -/
theorem ProjectedEdgePairing.generator_mem (pairing : ProjectedEdgePairs.ProjectedEdgePairing labels edges)
    (index : Fin (ProjectedEdgePairing.boundaryWord pairing).alphabet.count) : (ProjectedEdgePairing.boundaryWord
      pairing).alphabet.generators index ∈ edges := by
  let occurrence := CutWordEntry.locate ⟨index, false⟩ (ProjectedEdgePairing.boundaryWord pairing).alphabet.entries (by
    rw [(ProjectedEdgePairing.boundaryWord pairing).alphabet.occurrences_eq, Bool.false_and]
    exact Nat.zero_lt_one)
  have equal := ProjectedEdgePairing.boundaryWord_provenance pairing occurrence.entry occurrence.member
  unfold CutWordEntry.PairProvenance at equal
  rw [occurrence.letter_eq] at equal
  have member := (congrArg (fun bank => occurrence.entry.edge ∈ bank) (ProjectedEdgePairing.boundaryWord
    pairing).alphabet.edges_eq).mp
    (Map.mem_map_of_mem occurrence.member)
  exact equal ▸ member

namespace CutBoundaryWord.AreaSample

variable {word : BoundaryWord.CutBoundaryWord labels edges} {primitive : Fin source → Stokes.PrimitivePoint} {origin :
  Stokes.PrimitivePoint}

/-- Conjugate primitive endpoint pairs give conjugate retained generator increments. -/
theorem values_conjugate (sample : CutBoundaryWord.AreaSample word primitive origin) (related : ∀ vertex,
  (PrimitivePoint.Conjugate (primitive vertex)))
    (index : Fin word.alphabet.count) : (PrimitivePoint.Conjugate (sample.values index)) := by
  rw [AreaSample.values_apply sample]
  exact PrimitivePoint.sub_conjugate (related _) (related _)

open Purelib.Topology.Surface.Cut.GeneratorBounds in
/-- Original endpoint magnitude bounds give a fourfold bound on each retained generator increment. -/
theorem values_bounded (sample : CutBoundaryWord.AreaSample word primitive origin) (pairing :
  ProjectedEdgePairs.ProjectedEdgePairing labels edges)
    (word_eq : word = (ProjectedEdgePairing.boundaryWord pairing)) {magnitude : PrimitiveAreaBounds.AreaCoordinate}
    (bounded : ∀ edge ∈ edges, (PrimitivePoint.Bounded (primitive edge.start)) magnitude ∧ (PrimitivePoint.Bounded
      (primitive edge.finish)) magnitude)
    (index : Fin word.alphabet.count) : (PrimitivePoint.Bounded (sample.values index)) (4 * magnitude) := by
  cases word_eq
  rw [AreaSample.values_apply sample]
  have endpoints := bounded _ (ProjectedEdgePairing.generator_mem pairing index)
  exact (Bounded.sub endpoints.2) endpoints.1

end CutBoundaryWord.AreaSample
end Purelib.Topology.Surface.Cut.GeneratorBounds
