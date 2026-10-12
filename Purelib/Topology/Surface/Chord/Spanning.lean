module
public import Purelib.Algebra.Group.Negation
import Purelib.Data.List.Map
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.Ring.IntCast
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Vector.Basic

import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Boundary.BoundaryCoordinates
import Purelib.Topology.Surface.Chord.Coordinates
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Cut.ChordJumps
import Purelib.Topology.Surface.Cut.IntegralPairing
import Purelib.Topology.Surface.Sewing.CutCycleChains
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Topology.Surface.Sewing.VertexSewing
import Purelib.Topology.Surface.Word.PairedWord
public import Purelib.Topology.Surface.Cut.Spanning
public import Purelib.Topology.Surface.Sewing.ChordCycleBank
import Purelib.Topology.Surface.Cut.Chord
import Purelib.Topology.Surface.Cut.JumpPaths
import Mathlib.Algebra.Ring.Int.Defs
import Purelib.Tactic.Ring

section
open Purelib.Algebra
-- Preserve the retained subtraction dictionary while selecting its owned zero certificate.
attribute [local instance 2000] Group.Negation.subNegZeroMonoid

open Purelib

open Purelib.Algebra

open Purelib.Data

open Purelib.Topology.Polygon

open Purelib.Topology.Surface.Boundary.BoundaryCoordinates

open Purelib.Topology.Surface.Chord

open Purelib.Topology.Surface.Cut

open Purelib.Topology.Surface.Cut.IntegralPairing

open Purelib.Topology.Surface.Cut.Spanning.CutBoundaryWord

open Purelib.Topology.Surface.Sewing

open Purelib.Topology.Surface.Sewing.ChordCycleBank
open _root_.Purelib.Topology.Surface.Sewing renaming ChordCycleBank -> ChordCycleBank

open Purelib.Topology.Surface.Sewing.VertexSewing

open Purelib.Topology.Surface.Word.PairedWord

/-!
# Spanning by the retained actual chord cycles

Reuse each cached chord route and its physical coefficients. Converting
paired-matrix rows to actual chord cycles changes the physical remainder
by an explicit integer sum. The resulting identity holds for every
antisymmetric surface-edge valuation, without analytic vanishing premises.
-/

public section

namespace Purelib.Topology.Surface.Chord.Spanning

open Purelib.Topology.Surface.Boundary.BoundaryCoordinates (WordCoordinates)
open _root_.Purelib.Topology.Surface.Sewing (ChordCycleBank)
open Purelib.Topology.Surface.Sewing.CutCycleChains (CutCycleChain)
open Purelib.Topology.Surface.Sewing.ChordCycleBank (ChordCoordinate)
open Purelib.Topology.Surface.Cut.BoundaryWord (CutBoundaryWord)
open _root_.Purelib.Topology.Surface.Cut.IntegralPairing renaming CutBoundaryWord -> IntegralPairing
open Purelib.Topology.Surface.Cut.Spanning.CutBoundaryWord.IntegralPairing (SpanningCoordinates)
open Purelib.Topology.Surface.Word.SignedWord (SignedGenerator)

open Purelib.Topology.Polygon.Stokes (OrientedEdge)
open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_zero
  sumFin_add sumFin_sub sumFin_swap sumFin_mul_left sumFin_mul_right)

open Purelib.Topology.Surface.Sewing.SewingRetraction (wordValue)

/-- Evaluating a difference of integer coefficient rows subtracts their Gaussian readings. -/
private theorem combine_sub {count : Nat} (first last : Fin count → Int) (values : Fin count → Gaussian.Basic.Canonical)
  :
    WordCoordinates.combine (fun index => first index - last index) values =
      WordCoordinates.combine first values - WordCoordinates.combine last values :=
  (FiniteSum.Fin.sumFin_congr (fun index => by rw [Algebra.Ring.IntCast.sub, sub_mul])).trans (FiniteSum.Fin.sumFin_sub
    _ _)

/-- Evaluating an integer linear combination of rows agrees with the nested Gaussian combinations. -/
private theorem combine_rows {count : Nat} (weights : Fin count → Int) (rows : Fin count → Fin count → Int)
    (values : Fin count → Gaussian.Basic.Canonical) :
    WordCoordinates.combine (fun column => sumFin (fun index => weights index * rows index column)) values =
      WordCoordinates.combine weights (fun index => WordCoordinates.combine (rows index) values) := by
  calc
    _ = sumFin (fun column => sumFin (fun index =>
        (weights index : Gaussian.Basic.Canonical) * (rows index column : Gaussian.Basic.Canonical) * values column)) :=
          by
      apply FiniteSum.Fin.sumFin_congr
      intro column
      rw [FiniteSum.Fin.cast_sum, ← FiniteSum.Fin.sumFin_mul_right]
      apply FiniteSum.Fin.sumFin_congr
      intro index
      rw [Ring.IntCast.intCast_mul]
    _ = _ := by
      rw [FiniteSum.Fin.sumFin_swap]
      apply FiniteSum.Fin.sumFin_congr
      intro index
      exact (FiniteSum.Fin.sumFin_congr (fun column => _root_.mul_assoc _ _ _)).trans (FiniteSum.Fin.sumFin_mul_left _
        _)

/-- An integer row evaluates pointwise addition of Gaussian values additively. -/
private theorem combine_values_add {count : Nat} (weights : Fin count → Int) (first last : Fin count →
  Gaussian.Basic.Canonical) :
    WordCoordinates.combine weights (fun index => first index + last index) =
      WordCoordinates.combine weights first + WordCoordinates.combine weights last :=
  (FiniteSum.Fin.sumFin_congr (fun _ => mul_add _ _ _)).trans (FiniteSum.Fin.sumFin_add _ _)

namespace CutCycleChain

variable {source target : Nat} {labels : Fin source → Fin target} {ambient : List (Stokes.OrientedEdge target)}

/-- Evaluation of the actual retained surface words, with their integer multiplicities. This does not identify edge
readings with analytic periods. -/
@[expose] def edgeValue (chain : CutCycleChains.CutCycleChain labels ambient) (value : Stokes.OrientedEdge target →
  Gaussian.Basic.Canonical) : Gaussian.Basic.Canonical :=
  WordCoordinates.combine chain.weights (fun index => SewingRetraction.wordValue value (chain.cycles
    index).path.surfaceEdges)

end CutCycleChain

namespace CutBoundaryWord

variable {source target : Nat} {labels : Fin source → Fin target} {edges : List (Stokes.OrientedEdge source)}
  {word : BoundaryWord.CutBoundaryWord labels edges}

namespace ChordCoordinate

/-- The paired route already caches this row; no signed-word scan is rerun. -/
@[expose] def physicalRow : ChordCycleBank.ChordCoordinate word → Data.Vector Int word.alphabet.count
  | .boundary .. => vectorOfFn fun _ => 0
  | .paired _ _ _ route => route.physicalCoefficients

/-- A chord's retained physical row vanishes on every paired alphabet column. -/
theorem physicalRow_paired_zero (coordinate : ChordCycleBank.ChordCoordinate word) (column : Fin word.alphabet.count)
    (side : word.alphabet.oneSided column = false) : (physicalRow coordinate) column = 0 := by
  cases coordinate with
  | boundary => exact Data.Vector.Basic.vectorOfFn_apply _ _
  | paired index paired chord route =>
      change route.physicalCoefficients column = 0
      rw [route.physicalCoefficients_eq, ChordJumps.physicalLetters, SignedGenerator.total_retain, side]
      rfl

/-- Read an original chord cycle as its paired row plus its retained physical correction.

The edge valuation must reverse sign under orientation reversal; boundary slots contribute zero to both terms. -/
theorem cycle_value (coordinate : ChordCycleBank.ChordCoordinate word) (anchor : Fin source) (integral :
  IntegralPairing word)
    (value : Stokes.OrientedEdge target → Gaussian.Basic.Canonical) (anti : ∀ edge, value edge.reverse = -value edge) :
    SewingRetraction.wordValue value (coordinate.cycle anchor).path.surfaceEdges =
      WordCoordinates.combine (integral.paired coordinate.index)
        (fun column => value (OrientedEdge.map labels (word.alphabet.generators column))) +
      WordCoordinates.combine (physicalRow coordinate)
        (fun column => value (OrientedEdge.map labels (word.alphabet.generators column))) := by
  cases coordinate with
  | boundary index side =>
      have pairedZero : WordCoordinates.combine (integral.paired index)
          (fun column => value (OrientedEdge.map labels (word.alphabet.generators column))) = 0 := by
        apply (FiniteSum.Fin.sumFin_congr ?_).trans FiniteSum.Fin.sumFin_zero
        intro column
        rw [integral.paired_eq, side, Bool.true_or, if_pos rfl, Algebra.Ring.IntCast.cast_zero, zero_mul]
      have physicalZero : WordCoordinates.combine (vectorOfFn fun _ : Fin word.alphabet.count => (0 : Int))
          (fun column => value (OrientedEdge.map labels (word.alphabet.generators column))) = 0 := by
        apply (FiniteSum.Fin.sumFin_congr ?_).trans FiniteSum.Fin.sumFin_zero
        intro column
        rw [Data.Vector.Basic.vectorOfFn_apply, Algebra.Ring.IntCast.cast_zero, zero_mul]
      change 0 = _
      dsimp only [ChordCoordinate.index, physicalRow]
      rw [pairedZero, physicalZero, zero_add]
  | paired index side chord route =>
      have projected : route.path.surfaceEdges = chord.interval.map (fun entry => OrientedEdge.map labels entry.edge) :=
        by
        rw [route.path.projection_eq, route.path_eq, Data.List.Map.map_map]
        rfl
      change SewingRetraction.wordValue value route.path.surfaceEdges = _
      rw [projected, Coordinates.coordinates_value chord integral side value anti]
      calc
        _ = sumFin (fun column =>
            (integral.paired index column : Gaussian.Basic.Canonical) * value (OrientedEdge.map labels
              (word.alphabet.generators column)) +
            (route.physicalCoefficients column : Gaussian.Basic.Canonical) * value (OrientedEdge.map labels
              (word.alphabet.generators column))) := by
          apply FiniteSum.Fin.sumFin_congr
          intro column
          rw [route.physicalCoefficients_eq, Algebra.Ring.IntCast.add, add_mul]
        _ = _ := FiniteSum.Fin.sumFin_add _ _

end ChordCoordinate

namespace ChordCycleBank

/-- The original indexed chord bank reads back the paired row and physical correction of each cached cycle. -/
theorem cycle_value (bank : Sewing.ChordCycleBank word) (integral : IntegralPairing word)
    (value : Stokes.OrientedEdge target → Gaussian.Basic.Canonical) (anti : ∀ edge, value edge.reverse = -value edge)
    (index : Fin word.alphabet.count) :
    SewingRetraction.wordValue value (bank.cycles index).path.surfaceEdges =
      WordCoordinates.combine (integral.paired index) (fun column => value (OrientedEdge.map labels
        (word.alphabet.generators column))) +
      WordCoordinates.combine (CutBoundaryWord.ChordCoordinate.physicalRow (bank.coordinates index)) (fun column =>
        value (OrientedEdge.map labels (word.alphabet.generators column))) := by
  rw [bank.cycles_eq, CutBoundaryWord.ChordCoordinate.cycle_value (bank.coordinates index) bank.anchor integral value
    anti, bank.indices_eq]

end ChordCycleBank

namespace IntegralPairing.SpanningCoordinates

variable {integral : IntegralPairing word} {row : Data.Vector Int word.alphabet.count}

set_option genInjectivity false in
/-- The same integer combination, now of concrete cycles, and the corrected physical row. The bank is shared with the
prepared chord-period programs. -/
structure OnChords (span : IntegralPairing.SpanningCoordinates integral row) (bank : Sewing.ChordCycleBank word)
  where
  /-- Cached integer coefficients of the corrected physical boundary reading. -/ physical : Data.Vector Int
    word.alphabet.count
  /-- Each cached coefficient subtracts the weighted chord corrections from the original physical coefficient. -/
    physical_eq : ∀ column, physical column = span.physical column -
    sumFin (fun index => span.coefficients index * (CutBoundaryWord.ChordCoordinate.physicalRow (bank.coordinates
      index)) column)

constructive_injectivity OnChords

/-- Transfer spanning coordinates to the original chord cycles.

The cached physical row subtracts the weighted physical corrections of those cycles from the original spanning row. -/
@[expose] def onChords (span : IntegralPairing.SpanningCoordinates integral row) (bank : Sewing.ChordCycleBank
  word) : OnChords span bank :=
  ⟨vectorOfFn fun column => span.physical column -
      sumFin (fun index => span.coefficients index * (CutBoundaryWord.ChordCoordinate.physicalRow (bank.coordinates
        index)) column), Data.Vector.Basic.vectorOfFn_apply _⟩

namespace OnChords

variable {span : IntegralPairing.SpanningCoordinates integral row} {bank : Sewing.ChordCycleBank word}

/-- The retained original chord cycles with their existing spanning coefficients. -/
@[expose] def chain (_ : OnChords span bank) : CutCycleChains.CutCycleChain labels (edges.map
  (OrientedEdge.map labels)) :=
  ⟨word.alphabet.count, bank.cycles, span.coefficients⟩

/-- The corrected physical row remains zero on every paired generator. -/
theorem physical_paired_zero (coordinates : OnChords span bank) (column : Fin word.alphabet.count)
    (side : word.alphabet.oneSided column = false) : coordinates.physical column = 0 := by
  rw [coordinates.physical_eq, span.physical_eq, side]
  have zero : sumFin (fun index => span.coefficients index * (CutBoundaryWord.ChordCoordinate.physicalRow
    (bank.coordinates index)) column) = 0 := by
    exact (FiniteSum.Fin.sumFin_congr (fun index => by rw [CutBoundaryWord.ChordCoordinate.physicalRow_paired_zero
      (bank.coordinates index) column side, mul_zero])).trans FiniteSum.Fin.sumFin_zero
  rw [zero]
  rfl

/-- Evaluate the corrected physical row as the original physical reading minus the weighted chord corrections. -/
theorem physical_value (coordinates : OnChords span bank) (values : Fin word.alphabet.count →
  Gaussian.Basic.Canonical) :
    WordCoordinates.combine coordinates.physical values = WordCoordinates.combine span.physical values -
      WordCoordinates.combine span.coefficients (fun index => WordCoordinates.combine
        (CutBoundaryWord.ChordCoordinate.physicalRow (bank.coordinates index)) values) := by
  calc
    _ = WordCoordinates.combine (fun column => span.physical column -
        sumFin (fun index => span.coefficients index * (CutBoundaryWord.ChordCoordinate.physicalRow (bank.coordinates
          index)) column)) values := by
      apply FiniteSum.Fin.sumFin_congr
      intro column
      rw [coordinates.physical_eq]
    _ = _ := by rw [combine_sub, combine_rows]

/-- Split an antisymmetric edge reading into its original chord chain and corrected physical row.

The equality retains both terms and requires no vanishing assumption on physical boundary readings. -/
theorem value_eq (coordinates : OnChords span bank) (value : Stokes.OrientedEdge target →
  Gaussian.Basic.Canonical)
    (anti : ∀ edge, value edge.reverse = -value edge) :
    WordCoordinates.combine row (fun column => value (OrientedEdge.map labels (word.alphabet.generators column))) =
      Spanning.CutCycleChain.edgeValue (OnChords.chain coordinates) value +
        WordCoordinates.combine coordinates.physical (fun column => value (OrientedEdge.map labels
          (word.alphabet.generators column))) := by
  have chainValue : Spanning.CutCycleChain.edgeValue (OnChords.chain coordinates) value =
      WordCoordinates.combine span.coefficients (fun index => WordCoordinates.combine (integral.paired index)
        (fun column => value (OrientedEdge.map labels (word.alphabet.generators column)))) +
      WordCoordinates.combine span.coefficients (fun index => WordCoordinates.combine
        (CutBoundaryWord.ChordCoordinate.physicalRow (bank.coordinates index))
        (fun column => value (OrientedEdge.map labels (word.alphabet.generators column)))) := by
    calc
      _ = WordCoordinates.combine span.coefficients (fun index =>
          WordCoordinates.combine (integral.paired index) (fun column => value (OrientedEdge.map labels
            (word.alphabet.generators column))) +
          WordCoordinates.combine (CutBoundaryWord.ChordCoordinate.physicalRow (bank.coordinates index)) (fun column =>
            value (OrientedEdge.map labels (word.alphabet.generators column)))) := by
        change WordCoordinates.combine span.coefficients
          (fun index => SewingRetraction.wordValue value (bank.cycles index).path.surfaceEdges) = _
        apply FiniteSum.Fin.sumFin_congr
        intro index
        dsimp only
        rw [CutBoundaryWord.ChordCycleBank.cycle_value bank integral value anti]
      _ = _ := combine_values_add _ _ _
  rw [span.value_eq, chainValue, coordinates.physical_value]
  ring1

end OnChords
end IntegralPairing.SpanningCoordinates
end CutBoundaryWord
end Purelib.Topology.Surface.Chord.Spanning

end
