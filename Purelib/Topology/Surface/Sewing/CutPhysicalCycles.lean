module
import Purelib.Data.List.Membership
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.List.Map
import Purelib.Topology.Chain.PathBoundary

import Purelib.Topology.Polygon.Stokes
public import Purelib.Topology.Surface.Chord.PairChordCoverage
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Sewing.SimpleBoundaryCycles
import Purelib.Topology.Surface.Sewing.VertexSewing
public import Purelib.Topology.Surface.Word.GeneratorValuations
import Purelib.Topology.Surface.Word.ProjectedEdgePairs
public import Purelib.Topology.Surface.Sewing.PhysicalCycleCoordinates
import Purelib.Topology.Surface.Chord.PhysicalBoundary
import Purelib.Data.Vector.Basic
import Mathlib.Algebra.Ring.Int.Defs

open Purelib

open Purelib.Algebra

open Purelib.Data.List

open Purelib.Topology.Chain

open Purelib.Topology.Polygon

open Purelib.Topology.Polygon.Stokes

open Purelib.Topology.Surface.Chord.PairChordCoverage

open Purelib.Topology.Surface.Cut.BoundaryWord

open Purelib.Topology.Surface.Sewing.PhysicalCycleCoordinates

open Purelib.Topology.Surface.Sewing.SimpleBoundaryCycles

open Purelib.Topology.Surface.Sewing.VertexSewing

open Purelib.Topology.Surface.Word

open Purelib.Topology.Surface.Word.GeneratorValuations

/-!
# Whole physical cycles for the retained cut-generator coefficients

The one-sided alphabet slots are exactly the original physical boundary
edges. Their projected incidence is unique. These finite facts turn a closed
physical row into the cached loop multiples, without a caller decomposition
or a new root/path preparation.
-/

public section

namespace Purelib.Topology.Surface.Sewing.CutPhysicalCycles

open Purelib.Topology.Surface.Word.ProjectedEdgePairs (ProjectedEdgePair ProjectedEdgePairing)
open Purelib.Topology.Surface.Cut.BoundaryWord (CutAlphabet)
open Purelib.Topology.Surface.Sewing.SimpleBoundaryCycles.PolygonStokes (BoundaryCycleDecomposition)

open Purelib.Topology.Polygon.Stokes (OrientedEdge)

variable {source target : Nat} {labels : Fin source → Fin target}

/-- Every original physical boundary edge has a one-sided coordinate in the retained cut alphabet. -/
theorem physical_index (pairs : List (ProjectedEdgePairs.ProjectedEdgePair labels))
    {edge : Stokes.OrientedEdge source} : ∀ boundary : List (Stokes.OrientedEdge source), edge ∈ boundary →
    ∃ index : Fin (CutAlphabet.ofLists boundary pairs).count,
      (CutAlphabet.ofLists boundary pairs).oneSided index = true ∧
      (CutAlphabet.ofLists boundary pairs).generators index = edge
  | [], member => (List.not_mem_nil member).elim
  | head :: tail, member => by
      rcases Data.List.Membership.mem_cons.mp member with rfl | inTail
      · exact ⟨⟨0, Nat.zero_lt_succ _⟩, rfl, rfl⟩
      · obtain ⟨index, side, equal⟩ := Purelib.Topology.Surface.Sewing.CutPhysicalCycles.physical_index pairs tail
          inTail
        exact ⟨index.succ, side, equal⟩

namespace ProjectedEdgePairing

variable {edges : List (Stokes.OrientedEdge source)} {occurrences : List (Stokes.OrientedEdge target)}

/-- Compute a complete loop decomposition of a closed physical row. All nonzero entries are retained, including the
exterior components. -/
@[expose] def physicalCycles (pairing : ProjectedEdgePairs.ProjectedEdgePairing labels edges)
    (unique : (edges.map (OrientedEdge.map labels)).Nodup)
    (boundary : PolygonStokes.BoundaryCycleDecomposition occurrences)
    (matching : ∀ edge, edge ∈ pairing.boundary.map (OrientedEdge.map labels) ↔ edge ∈ boundary.cycles.flatten)
    (row : Fin (ProjectedEdgePairing.boundaryWord pairing).alphabet.count → Int)
    (physical : ∀ index, (ProjectedEdgePairing.boundaryWord pairing).alphabet.oneSided index = false → row index = 0)
    (closed : ∀ vertex, FiniteSum.Fin.sumFin (fun index => row index *
      PathBoundary.edgeBoundaryAt OrientedEdge.start OrientedEdge.finish
        (OrientedEdge.map labels ((ProjectedEdgePairing.boundaryWord pairing).alphabet.generators index)) vertex) = 0) :
    PhysicalCycleCoordinates.Data boundary (fun index => OrientedEdge.map labels ((ProjectedEdgePairing.boundaryWord
      pairing).alphabet.generators index)) row := by
  apply PhysicalCycleCoordinates.build boundary _ row (fun first last same =>
    ProjectedEdgePairing.generator_projected_injective pairing unique first last same)
  · intro index nonzero
    cases side : (ProjectedEdgePairing.boundaryWord pairing).alphabet.oneSided index
    · exact (nonzero (physical index side)).elim
    · exact (matching _).mp (Map.mem_map_of_mem (ProjectedEdgePairing.oneSided_generator_mem pairing index side))
  · intro edge member
    obtain ⟨original, inBoundary, projected⟩ := Map.mem_map.mp ((matching edge).mpr member)
    obtain ⟨index, _, equal⟩ := CutPhysicalCycles.physical_index pairing.pairs pairing.boundary inBoundary
    exact ⟨index, (congrArg (OrientedEdge.map labels) equal).trans projected⟩
  · exact closed

end ProjectedEdgePairing
end Purelib.Topology.Surface.Sewing.CutPhysicalCycles
