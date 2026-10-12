module

import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Cut.Patch
public import Purelib.Topology.Surface.Sewing.SewnPrimitivePaths
public import Purelib.Topology.Surface.Sewing.ChordCycleBank
import Purelib.Data.Vector.Basic
import Purelib.Topology.Surface.Sewing.CutCycleChains
import Purelib.Topology.Surface.Sewing.VertexSewing
import Purelib.Topology.Surface.Cut.JumpPaths

/-!
# Positive source banks for the retained chord cycles

Every chord interval follows the positive cut boundary, even when its signed
generator letters are negative. Empty physical-boundary slots are included.
Ownership is computed before primitive accuracy and can be cached thereafter.
-/

public section

namespace Purelib.Topology.Surface.Chord.SourceBanks

open Purelib.Topology
open Purelib.Topology.Surface
open Purelib.Topology.Surface.Chord
open Purelib.Topology.Surface.Sewing
open Purelib.Topology.Surface.Sewing.SewnPrimitivePaths

open Purelib.Topology.Polygon.Stokes (OrientedEdge OrientedTriangle)

open Purelib.Topology.Surface.Sewing.SewnPrimitivePaths.SewnPrimitiveFaces
open Purelib.Topology.Surface.Cut.Patch (CutPatch)
open Purelib.Topology.Surface.Cut.BoundaryWord (CutBoundaryWord)
open _root_.Purelib.Topology.Surface.Sewing (ChordCycleBank)

variable {vertexCount faceCount : Nat} {faces : Fin faceCount → Polygon.Stokes.OrientedTriangle vertexCount}
  {indices : List (Fin faceCount)} {boundary : List (Polygon.Stokes.OrientedEdge vertexCount)}
  {patch : Cut.Patch.CutPatch faces indices boundary} {word : Cut.BoundaryWord.CutBoundaryWord patch.vertexLabels
    patch.boundary}

/-- Every retained chord-cycle edge occurs positively in the original cut boundary. -/
theorem cycle_positive (routes : Sewing.ChordCycleBank word) (index : Fin word.alphabet.count) :
    ∀ edge ∈ (routes.cycles index).path.cutEdges, edge ∈ patch.boundary := by
  rw [routes.cycles_eq]
  cases routes.coordinates index with
  | boundary => exact fun _ member => (List.not_mem_nil member).elim
  | paired index paired chord route =>
      change ∀ edge ∈ route.path.cutEdges, edge ∈ patch.boundary
      rw [route.path_eq]
      exact Chord.interval_positive chord

/-- Geometry-only ownership can be cached once and shared across primitive requests.

Each chord cycle retains its original positive boundary occurrences, including empty physical slots, and the source bank
records their ordered owners. -/
@[expose] def sourceBank (patch : Cut.Patch.CutPatch faces indices boundary) {word : Cut.BoundaryWord.CutBoundaryWord
  patch.vertexLabels patch.boundary}
    (routes : Sewing.ChordCycleBank word) (index : Fin word.alphabet.count) : SewnPrimitiveFaces.PathSources
      patch (routes.cycles index).path.cutEdges :=
  PathSources.build patch _ (fun edge member => Or.inl (cycle_positive routes index edge member))

/-- The constructed source bank retains positive orientation for every chord-cycle occurrence. -/
theorem sourceBank_positive (routes : Sewing.ChordCycleBank word) (index : Fin word.alphabet.count) :
    (sourceBank patch routes index).Positive :=
  PathSources.build_positive _ _ _ (cycle_positive routes index)

end Purelib.Topology.Surface.Chord.SourceBanks

end
