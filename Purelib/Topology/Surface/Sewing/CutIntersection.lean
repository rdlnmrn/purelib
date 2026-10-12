module
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Vector.Basic

import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Cut.Chord
import Purelib.Topology.Surface.Cut.IntegralPairing
public import Purelib.Topology.Surface.Cut.Spanning
public import Purelib.Topology.Surface.Sewing.ChordCycleBank
import Purelib.Topology.Surface.Word.PairedWord
import Purelib.Topology.Surface.Word.Pairing
import Purelib.Topology.Surface.Word.SignedWord
import Purelib.Topology.Surface.Chord.Spanning
import Purelib.Topology.Surface.Cut.ChordJumps
import Mathlib.Algebra.Ring.Int.Defs
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra

open Purelib.Topology.Polygon

open Purelib.Topology.Surface.Cut

open Purelib.Topology.Surface.Cut.BoundaryWord

open Purelib.Topology.Surface.Cut.Chord

open Purelib.Topology.Surface.Cut.IntegralPairing

open Purelib.Topology.Surface.Cut.Spanning.CutBoundaryWord

open Purelib.Topology.Surface.Sewing

open Purelib.Topology.Surface.Word

open Purelib.Topology.Surface.Word.PairedWord

open Purelib.Topology.Surface.Word.SignedWord

/-!
# Signed cut-chord crossings and the induced pairing of actual closed rows

Count the other generator's two signed occurrences between a chord's
retained endpoints. This is the actual cyclic cut word, not a supplied
standard intersection table. Integer spanning coefficients transport the
crossing form to closed rows. The transported form is independent of those
coefficients, skew, and zero on purely physical rows.
-/

@[expose] public section

namespace Purelib.Topology.Surface.Sewing.CutIntersection.CutBoundaryWord

open Purelib.Topology.Surface.Cut.BoundaryWord (CutBoundaryWord CutWordEntry)
open _root_.Purelib.Topology.Surface.Cut.Chord renaming CutBoundaryWord -> Chord
open _root_.Purelib.Topology.Surface.Sewing (ChordCycleBank)
open _root_.Purelib.Topology.Surface.Sewing.ChordCycleBank (ChordCoordinate)
open _root_.Purelib.Topology.Surface.Cut.IntegralPairing renaming CutBoundaryWord -> IntegralPairing
open Purelib.Topology.Surface.Cut.Spanning.CutBoundaryWord.IntegralPairing (SpanningCoordinates)
open Purelib.Topology.Surface.Word.SignedWord (SignedGenerator)

open Purelib.Topology.Polygon.Stokes (OrientedEdge)

open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_zero sumFin_swap sumFin_neg sumFin_mul_right)

section

variable {source target : Nat} {labels : Fin source → Fin target} {edges : List (Stokes.OrientedEdge source)}
  {word : BoundaryWord.CutBoundaryWord labels edges}

namespace Chord

/-- Oriented endpoint interlacing on the retained cyclic cut boundary. The actual entries strictly between the selected
endpoints are counted. -/
def crossing {index : Fin word.alphabet.count} (chord : Chord word index) (column : Fin
  word.alphabet.count) : Int :=
  (SignedGenerator.occurrences ⟨column, false⟩ (chord.last.before.map CutWordEntry.letter) : Int) -
    (SignedGenerator.occurrences ⟨column, true⟩ (chord.last.before.map CutWordEntry.letter) : Int)

/-- Signed interlacing of two paired generator occurrences equals the original paired-matrix entry. -/
theorem crossing_eq_paired {index : Fin word.alphabet.count} (chord : Chord word index)
    (integral : IntegralPairing word) (paired : word.alphabet.oneSided index = false)
    (column : Fin word.alphabet.count) (columnPaired : word.alphabet.oneSided column = false) :
    (crossing chord column) = integral.paired index column := by
  have equation := chord.paired_row integral paired column
  rw [SignedGenerator.total_retain, columnPaired] at equation
  change integral.paired index column = Pairing.totalAt
    ((chord.last.before.map CutWordEntry.letter).map SignedGenerator.coefficients) column at equation
  rw [SignedGenerator.total_eq_counts] at equation
  exact equation.symm

end Chord

namespace ChordCoordinate

set_option backward.match.sparseCases false in
/-- Count retained chord interlacing for two paired coordinates, assigning zero to physical slots. -/
def crossing : ChordCycleBank.ChordCoordinate word → ChordCycleBank.ChordCoordinate word → Int
  | .paired _ _ chord _, .paired column .. => (CutIntersection.CutBoundaryWord.Chord.crossing chord column)
  | _, _ => 0

/-- Coordinate crossing reads the paired-matrix entry at the two original retained indices. -/
theorem crossing_eq_paired (first last : ChordCycleBank.ChordCoordinate word) (integral :
  IntegralPairing word) :
    (crossing first last) = integral.paired first.index last.index := by
  cases first with
  | boundary index side =>
      change 0 = integral.paired index last.index
      rw [integral.paired_eq, side, Bool.true_or]
      rfl
  | paired index side chord route =>
      cases last with
      | boundary column columnSide =>
          change 0 = integral.paired index column
          rw [integral.paired_eq, columnSide, Bool.or_true]
          rfl
      | paired column columnSide other otherRoute =>
          exact (CutIntersection.CutBoundaryWord.Chord.crossing_eq_paired chord) integral side column columnSide

end ChordCoordinate

/-- Crossings in the retained chord bank recover the original paired matrix in alphabet order. -/
theorem ChordCycleBank.crossing_eq_paired (bank : ChordCycleBank word) (integral :
  IntegralPairing word)
    (first last : Fin word.alphabet.count) :
    (CutBoundaryWord.ChordCoordinate.crossing (bank.coordinates first) (bank.coordinates last)) = integral.paired first
      last := by
  rw [(CutBoundaryWord.ChordCoordinate.crossing_eq_paired (bank.coordinates first)) (bank.coordinates last) integral,
    bank.indices_eq, bank.indices_eq]

namespace IntegralPairing.SpanningCoordinates

variable {integral : IntegralPairing word}
  {firstRow lastRow : Data.Vector Int word.alphabet.count}

/-- Compute from the already cached paired matrix and integer coefficients. The crossing theorem below identifies it
with the actual chord occurrences. -/
def intersection (first : IntegralPairing.SpanningCoordinates integral firstRow) (last :
  IntegralPairing.SpanningCoordinates integral lastRow) : Int :=
  FiniteSum.Fin.sumFin fun row => FiniteSum.Fin.sumFin fun column => first.coefficients row * integral.paired row column
    * last.coefficients column

/-- The cached matrix contraction equals the integer-weighted crossings of actual retained chords. -/
theorem intersection_eq_crossings (first : IntegralPairing.SpanningCoordinates integral firstRow) (last :
  IntegralPairing.SpanningCoordinates integral lastRow)
    (bank : ChordCycleBank word) :
    (intersection first) last = FiniteSum.Fin.sumFin (fun row => FiniteSum.Fin.sumFin (fun column =>
      first.coefficients row * (CutBoundaryWord.ChordCoordinate.crossing (bank.coordinates row) (bank.coordinates
        column)) * last.coefficients column)) := by
  apply FiniteSum.Fin.sumFin_congr
  intro row
  apply FiniteSum.Fin.sumFin_congr
  intro column
  rw [(CutBoundaryWord.ChordCycleBank.crossing_eq_paired bank) integral]

/-- Exchanging the original two spanned rows negates their intersection reading. -/
theorem intersection_skew (first : IntegralPairing.SpanningCoordinates integral firstRow) (last :
  IntegralPairing.SpanningCoordinates integral lastRow) :
    (intersection first) last = -(intersection last) first := by
  calc
    _ = FiniteSum.Fin.sumFin (fun column => FiniteSum.Fin.sumFin (fun row =>
        first.coefficients row * integral.paired row column * last.coefficients column)) := FiniteSum.Fin.sumFin_swap _
    _ = FiniteSum.Fin.sumFin (fun column => FiniteSum.Fin.sumFin (fun row =>
        -(last.coefficients column * integral.paired column row * first.coefficients row))) := by
      apply FiniteSum.Fin.sumFin_congr
      intro column
      apply FiniteSum.Fin.sumFin_congr
      intro row
      rw [integral.paired_skew row column]
      ring1
    _ = _ := (FiniteSum.Fin.sumFin_congr (fun _ => FiniteSum.Fin.sumFin_neg _)).trans (FiniteSum.Fin.sumFin_neg _)

/-- Every original spanned row has zero intersection with itself. -/
theorem intersection_diagonal (first : IntegralPairing.SpanningCoordinates integral firstRow) :
  (intersection first) first = 0 := by
  have skew := (intersection_skew first) first
  omega

/-- Read the first intersection argument directly from its original row after removing the physical remainder. -/
theorem intersection_left_readback (first : IntegralPairing.SpanningCoordinates integral firstRow) (last :
  IntegralPairing.SpanningCoordinates integral lastRow) :
    (intersection first) last = FiniteSum.Fin.sumFin (fun column => (firstRow column -
      first.physical column) * last.coefficients column) := by
  calc
    _ = FiniteSum.Fin.sumFin (fun column => FiniteSum.Fin.sumFin (fun row =>
        first.coefficients row * integral.paired row column * last.coefficients column)) := FiniteSum.Fin.sumFin_swap _
    _ = FiniteSum.Fin.sumFin (fun column => (FiniteSum.Fin.sumFin (fun row => first.coefficients row * integral.paired
      row column)) * last.coefficients column) :=
      FiniteSum.Fin.sumFin_congr (fun _ => FiniteSum.Fin.sumFin_mul_right _ _)
    _ = _ := by
      apply FiniteSum.Fin.sumFin_congr
      intro column
      have row := first.equation column
      have coefficient : FiniteSum.Fin.sumFin (fun index => first.coefficients index * integral.paired index column) =
          firstRow column - first.physical column := by omega
      rw [coefficient]

/-- Alternative retained spanning coefficients for the same first row give the same intersection. -/
theorem intersection_left_independent (first other : IntegralPairing.SpanningCoordinates integral firstRow)
    (last : IntegralPairing.SpanningCoordinates integral lastRow) : (intersection first) last =
      (intersection other) last := by
  rw [(intersection_left_readback first) last, (intersection_left_readback
    other) last]
  apply FiniteSum.Fin.sumFin_congr
  intro column
  rw [first.physical_eq, other.physical_eq]

/-- The intersection depends only on the two original rows, not their retained spanning coefficients. -/
theorem intersection_independent (first otherFirst : IntegralPairing.SpanningCoordinates integral firstRow)
    (last otherLast : IntegralPairing.SpanningCoordinates integral lastRow) : (intersection first)
      last = (intersection otherFirst) otherLast := by
  rw [(intersection_left_independent first) otherFirst last, (intersection_skew
    otherFirst) last,
    (intersection_left_independent last) otherLast otherFirst, ←
      (intersection_skew otherFirst) otherLast]

/-- Physical rows lie in the radical of this cut pairing. They remain present in the period and area identities, where
they need not vanish. -/
theorem intersection_physical (first : IntegralPairing.SpanningCoordinates integral firstRow) (last :
  IntegralPairing.SpanningCoordinates integral lastRow)
    (physical : ∀ column, word.alphabet.oneSided column = false → firstRow column = 0) :
      (intersection first) last = 0 := by
  rw [(intersection_left_readback first) last]
  apply (FiniteSum.Fin.sumFin_congr ?_).trans FiniteSum.Fin.sumFin_zero
  intro column
  rw [first.physical_eq]
  cases side : word.alphabet.oneSided column
  · rw [physical column side]
    change (0 : Int) * last.coefficients column = 0
    exact zero_mul _
  · change (firstRow column - firstRow column) * last.coefficients column = 0
    rw [sub_self, zero_mul]

end IntegralPairing.SpanningCoordinates
end
end Purelib.Topology.Surface.Sewing.CutIntersection.CutBoundaryWord
