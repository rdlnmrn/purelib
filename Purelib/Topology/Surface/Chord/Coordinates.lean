module
import Purelib.Data.List.Map
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Gaussian.Basic
import Purelib.Topology.Chain.PathBoundary

import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Cut.Chord
import Purelib.Topology.Surface.Cut.IntegralPairing
import Purelib.Topology.Surface.Cut.JumpPaths
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Topology.Surface.Sewing.VertexSewing
import Purelib.Topology.Surface.Word.Pairing
import Purelib.Topology.Surface.Word.SignedWord
public import Purelib.Topology.Surface.Boundary.BoundaryCoordinates
public import Purelib.Topology.Surface.Cut.ChordJumps
import Purelib.Data.Vector.Basic
import Purelib.Topology.Surface.Word.ProjectedEdgePairs

public section

/-!
# Actual chord cycles in the same integer coordinates as the A/B tours

The existing retained chord interval directly supplies its signed word.
Its integer row is the paired matrix row plus the full physical-boundary
row, and its boundary vanishes at every projected surface vertex. Thus the
rows to be used in spanning are coordinates of actual closed paths.
-/

namespace Purelib.Topology.Surface.Chord.Coordinates

open Purelib.Algebra
open Purelib.Data
open Purelib.Topology.Chain
open Purelib.Topology.Polygon
open Purelib.Topology.Polygon.Stokes
open Purelib.Topology.Surface.Boundary
open Purelib.Topology.Surface.Boundary.BoundaryCoordinates
open Purelib.Topology.Surface.Cut
open Purelib.Topology.Surface.Cut.Chord
open Purelib.Topology.Surface.Cut.Chord.CutBoundaryWord
open _root_.Purelib.Topology.Surface.Cut.Chord renaming CutBoundaryWord -> Chord
open Purelib.Topology.Surface.Cut.IntegralPairing
open Purelib.Topology.Surface.Cut.JumpPaths.CutPath
open Purelib.Topology.Surface.Sewing
open Purelib.Topology.Surface.Sewing.VertexSewing
open Purelib.Topology.Surface.Word
open Purelib.Topology.Surface.Word.SignedWord

open Purelib.Topology.Polygon.Stokes (OrientedEdge)
open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib.Topology.Surface.Boundary.BoundaryCoordinates (WordCoordinates)
open Purelib.Topology.Surface.Sewing.SewingRetraction (wordValue)
open Purelib.Topology.Surface.Cut.BoundaryWord (CutBoundaryWord)
open _root_.Purelib.Topology.Surface.Cut.Chord renaming CutBoundaryWord -> Chord
open _root_.Purelib.Topology.Surface.Cut.IntegralPairing renaming CutBoundaryWord -> IntegralPairing
open Purelib.Topology.Surface.Word.SignedWord (SignedGenerator)

variable {source target : Nat} {labels : Fin source → Fin target} {edges : List (Stokes.OrientedEdge source)}
  {word : BoundaryWord.CutBoundaryWord labels edges} {index : Fin word.alphabet.count}

/-- Cache the signed generator coordinates of the retained chord interval.

The construction reuses original cut-word entries and their order, with no new occurrence search. -/
@[expose] def coordinates (chord : Cut.Chord.CutBoundaryWord word index) :
    BoundaryCoordinates.WordCoordinates word.alphabet (chord.interval.map (fun entry => OrientedEdge.map labels
      entry.edge)) :=
  WordCoordinates.ofEntries word.alphabet chord.interval

open Purelib.Topology.Surface.Chord in
/-- Chord coordinates equal the paired matrix row plus the full physical-boundary row. -/
theorem coordinates_eq_row (chord : Cut.Chord.CutBoundaryWord word index) (pairing :
  Cut.IntegralPairing.CutBoundaryWord word)
    (paired : word.alphabet.oneSided index = false) (column : Fin word.alphabet.count) :
    (coordinates chord).totals column = pairing.paired index column +
      Pairing.totalAt ((ChordJumps.physicalLetters chord).map SignedGenerator.coefficients) column := by
  rw [coordinates, WordCoordinates.totals_eq, WordCoordinates.ofEntries_letters, List.Map.map_map]
  exact ChordJumps.total_eq_row_add_physical chord pairing paired column

/-- A retained chord interval projects to an exact closed path when the original cut word is closed. -/
theorem coordinates_closed (chord : Cut.Chord.CutBoundaryWord word index) {anchor : Fin source}
    (closed : PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish edges anchor anchor) :
    PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish
      (chord.interval.map (fun entry => OrientedEdge.map labels entry.edge)) (labels chord.pair.first.start) (labels
        chord.pair.first.start) := by
  have endpoints := chord.path_closed closed
  dsimp only [Chord.path, Projected.build] at endpoints
  rewrite [List.Map.map_map] at endpoints
  dsimp only [Function.comp_def] at endpoints
  exact endpoints

open Purelib.Topology.Surface.Chord
/-- The retained chord coordinate row has zero boundary at every projected vertex. -/
theorem coordinates_boundary_zero (chord : Cut.Chord.CutBoundaryWord word index) {anchor : Fin source}
    (closed : PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish edges anchor anchor)
    (vertex : Fin target) : (coordinates chord).boundaryAt vertex = 0 :=
  (coordinates chord).boundary_zero (coordinates_closed chord closed) vertex

/-- Original directed-edge evaluation, including the physical contribution. No vanishing face or physical-period premise
is needed. -/
theorem coordinates_value (chord : Cut.Chord.CutBoundaryWord word index) (pairing : Cut.IntegralPairing.CutBoundaryWord
  word)
    (paired : word.alphabet.oneSided index = false) (value : Stokes.OrientedEdge target → Gaussian.Basic.Canonical)
    (anti : ∀ edge, value edge.reverse = -value edge) :
    SewingRetraction.wordValue value (chord.interval.map (fun entry => OrientedEdge.map labels entry.edge)) =
      WordCoordinates.combine (fun column => pairing.paired index column +
        Pairing.totalAt ((ChordJumps.physicalLetters chord).map SignedGenerator.coefficients) column)
        (fun column => value (OrientedEdge.map labels (word.alphabet.generators column))) := by
  refine ((coordinates chord).value_eq value anti).trans ?_
  apply FiniteSum.Fin.sumFin_congr
  intro column
  rw [coordinates_eq_row chord pairing paired]

end Purelib.Topology.Surface.Chord.Coordinates

end
