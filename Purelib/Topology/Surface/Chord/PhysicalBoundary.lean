module
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Vector.Basic
import Purelib.Topology.Chain.PathBoundary

import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Chord.Coordinates
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Cut.IntegralPairing
import Purelib.Topology.Surface.Cut.Spanning
import Purelib.Topology.Surface.Sewing.ChordCycleBank
import Purelib.Topology.Surface.Sewing.VertexSewing
public import Purelib.Topology.Surface.Chord.Spanning
import Mathlib.Algebra.Ring.Int.Defs
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra

open Purelib.Topology.Chain

open Purelib.Topology.Polygon

open Purelib.Topology.Polygon.Stokes

open Purelib.Topology.Surface.Chord

open Purelib.Topology.Surface.Chord.Spanning.CutBoundaryWord

open Purelib.Topology.Surface.Chord.Spanning.CutBoundaryWord.IntegralPairing

open Purelib.Topology.Surface.Cut

open Purelib.Topology.Surface.Cut.IntegralPairing

open Purelib.Topology.Surface.Cut.Spanning.CutBoundaryWord

open Purelib.Topology.Surface.Sewing

open Purelib.Topology.Surface.Sewing.VertexSewing

/-!
# Closed physical remainders after spanning by actual chord cycles

The paired matrix rows alone omit physical pieces of the chord paths.
Subtracting the cached physical pieces gives the remainder associated with
the actual closed cycles. Its integer boundary vanishes at every original
surface vertex; this is an exact chain statement, independent of periods.
-/

@[expose] public section

namespace Purelib.Topology.Surface.Chord.PhysicalBoundary

open Purelib.Topology.Surface.Cut.BoundaryWord (CutBoundaryWord)
open _root_.Purelib.Topology.Surface.Sewing (ChordCycleBank)
open _root_.Purelib.Topology.Surface.Sewing.ChordCycleBank (ChordCoordinate)
open _root_.Purelib.Topology.Surface.Cut.IntegralPairing renaming CutBoundaryWord -> IntegralPairing
open Purelib.Topology.Surface.Cut.Spanning.CutBoundaryWord.IntegralPairing (SpanningCoordinates)
open Purelib.Topology.Surface.Chord.Spanning.CutBoundaryWord.IntegralPairing.SpanningCoordinates (OnChords)

open Purelib.Topology.Polygon.Stokes (OrientedEdge)

open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_zero sumFin_add
  sumFin_swap sumFin_mul_left sumFin_mul_right)
open Purelib.Data.Vector.Basic (vectorOfFn_apply)
open Purelib.Topology.Chain.PathBoundary (PathEndpoints edgeBoundaryAt)

variable {source target : Nat} {labels : Fin source → Fin target}
  {edges : List (Stokes.OrientedEdge source)} {word : BoundaryWord.CutBoundaryWord labels edges}

namespace ChordCoordinate

/-- The complete retained chord row, including its physical part, has zero boundary at every original surface vertex. -/
theorem boundary_zero (coordinate : ChordCycleBank.ChordCoordinate word) (integral : Cut.IntegralPairing.CutBoundaryWord
  word)
    {anchor : Fin source}
    (closed : PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish edges anchor anchor)
    (vertex : Fin target) :
    FiniteSum.Fin.sumFin (fun column => (integral.paired coordinate.index column + (ChordCoordinate.physicalRow
      coordinate) column) *
      PathBoundary.edgeBoundaryAt OrientedEdge.start OrientedEdge.finish (OrientedEdge.map labels
        (word.alphabet.generators column)) vertex) = 0 := by
  cases coordinate with
  | boundary index side =>
      apply (FiniteSum.Fin.sumFin_congr ?_).trans FiniteSum.Fin.sumFin_zero
      intro column
      change (integral.paired index column + (Data.Vector.Basic.vectorOfFn fun _ => (0 : Int)) column) * _ = 0
      rw [integral.paired_eq, side, Bool.true_or, if_pos rfl, Data.Vector.Basic.vectorOfFn_apply, zero_add, zero_mul]
  | paired index side chord route =>
      refine (FiniteSum.Fin.sumFin_congr ?_).trans (Coordinates.coordinates_boundary_zero chord closed vertex)
      intro column
      change (integral.paired index column + route.physicalCoefficients column) * _ = (Coordinates.coordinates
        chord).totals column * _
      rw [route.physicalCoefficients_eq, Coordinates.coordinates_eq_row chord integral side]

end ChordCoordinate

namespace ChordCycleBank

open Purelib.Topology.Surface.Chord.PhysicalBoundary in
/-- Every row in the retained chord-cycle bank has zero integer boundary on the original surface. -/
theorem boundary_zero (bank : Sewing.ChordCycleBank word) (integral : Cut.IntegralPairing.CutBoundaryWord word)
    {anchor : Fin source}
    (closed : PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish edges anchor anchor)
    (index : Fin word.alphabet.count) (vertex : Fin target) :
    FiniteSum.Fin.sumFin (fun column => (integral.paired index column + (ChordCoordinate.physicalRow (bank.coordinates
      index)) column) *
      PathBoundary.edgeBoundaryAt OrientedEdge.start OrientedEdge.finish (OrientedEdge.map labels
        (word.alphabet.generators column)) vertex) = 0 := by
  have result := ChordCoordinate.boundary_zero (bank.coordinates index) integral closed vertex
  rw [bank.indices_eq] at result
  exact result

end ChordCycleBank

namespace IntegralPairing.SpanningCoordinates.OnChords

variable {integral : Cut.IntegralPairing.CutBoundaryWord word}
  {row : Data.Vector Int word.alphabet.count}
  {span : IntegralPairing.SpanningCoordinates integral row} {bank : Sewing.ChordCycleBank word}

/-- Entrywise equality with the full rows of the actual chord cycles. -/
theorem equation (coordinates : SpanningCoordinates.OnChords span bank) (column : Fin word.alphabet.count) :
    row column = FiniteSum.Fin.sumFin (fun index => span.coefficients index *
      (integral.paired index column + (ChordCoordinate.physicalRow (bank.coordinates index)) column)) +
        coordinates.physical column := by
  have split := (FiniteSum.Fin.sumFin_congr (fun index => mul_add (span.coefficients index)
    (integral.paired index column) ((ChordCoordinate.physicalRow (bank.coordinates index)) column))).trans
      (FiniteSum.Fin.sumFin_add _ _)
  rw [split, coordinates.physical_eq, span.equation]
  ring1

open Purelib.Topology.Surface.Chord.PhysicalBoundary in
open Purelib.Topology.Surface.Chord.PhysicalBoundary.IntegralPairing.SpanningCoordinates in
/-- Closedness of the original integer row passes to the corrected physical remainder because each subtracted row
represents an actual closed chord. -/
theorem physical_boundary_zero (coordinates : SpanningCoordinates.OnChords span bank) {anchor : Fin source}
    (closed : PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish edges anchor anchor)
    (rowClosed : ∀ vertex : Fin target, FiniteSum.Fin.sumFin (fun column => row column *
      PathBoundary.edgeBoundaryAt OrientedEdge.start OrientedEdge.finish (OrientedEdge.map labels
        (word.alphabet.generators column)) vertex) = 0)
    (vertex : Fin target) :
    FiniteSum.Fin.sumFin (fun column => coordinates.physical column *
      PathBoundary.edgeBoundaryAt OrientedEdge.start OrientedEdge.finish (OrientedEdge.map labels
        (word.alphabet.generators column)) vertex) = 0 := by
  let boundary := fun column => PathBoundary.edgeBoundaryAt OrientedEdge.start OrientedEdge.finish
    (OrientedEdge.map labels (word.alphabet.generators column)) vertex
  have evaluated : FiniteSum.Fin.sumFin (fun column => row column * boundary column) =
      FiniteSum.Fin.sumFin (fun index => span.coefficients index * FiniteSum.Fin.sumFin (fun column =>
        (integral.paired index column + (ChordCoordinate.physicalRow (bank.coordinates index)) column) * boundary
          column)) +
      FiniteSum.Fin.sumFin (fun column => coordinates.physical column * boundary column) := by
    calc
      _ = FiniteSum.Fin.sumFin (fun column => FiniteSum.Fin.sumFin (fun index => span.coefficients index *
          (integral.paired index column + (ChordCoordinate.physicalRow (bank.coordinates index)) column) * boundary
            column) +
          coordinates.physical column * boundary column) := by
        apply FiniteSum.Fin.sumFin_congr
        intro column
        rw [equation coordinates, add_mul, FiniteSum.Fin.sumFin_mul_right]
      _ = _ := by
        rw [FiniteSum.Fin.sumFin_add, FiniteSum.Fin.sumFin_swap]
        apply congrArg (· + FiniteSum.Fin.sumFin (fun column => coordinates.physical column * boundary column))
        apply FiniteSum.Fin.sumFin_congr
        intro index
        exact (FiniteSum.Fin.sumFin_congr (fun column => _root_.mul_assoc _ _ _)).trans (FiniteSum.Fin.sumFin_mul_left _
          _)
  have chordsZero : FiniteSum.Fin.sumFin (fun index => span.coefficients index * FiniteSum.Fin.sumFin (fun column =>
      (integral.paired index column + (ChordCoordinate.physicalRow (bank.coordinates index)) column) * boundary column))
        = 0 := by
    apply (FiniteSum.Fin.sumFin_congr ?_).trans FiniteSum.Fin.sumFin_zero
    intro index
    rw [ChordCycleBank.boundary_zero bank integral closed index vertex, mul_zero]
  rw [rowClosed vertex, chordsZero, zero_add] at evaluated
  exact evaluated.symm

end IntegralPairing.SpanningCoordinates.OnChords
end Purelib.Topology.Surface.Chord.PhysicalBoundary
