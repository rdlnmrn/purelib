module
import Purelib.Data.List.Append
import Purelib.Data.List.Map
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Cut.Chord
import Purelib.Topology.Surface.Cut.ChordJumps
import Purelib.Topology.Surface.Cut.IntegralPairing
public import Purelib.Topology.Surface.Cut.WordErrors
public import Purelib.Topology.Surface.Sewing.ChordCycleBank
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Field
import Purelib.Topology.Surface.Cut.JumpPaths
import Mathlib.Data.Int.Cast.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Topology.Surface.Sewing.VertexSewing
import Mathlib.Data.Nat.Cast.Defs
import Purelib.Data.Vector.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Topology.Surface.Sewing.CutCycleChains
import Purelib.Tactic.QuotientFreeOmega

open Purelib.Data.Gaussian.Basic

open Purelib.Data.Rat

open Purelib.Data.Rat.Fraction

open Purelib.Riemann.Readings

open Purelib.Riemann.Readings.PrimitiveAreaBounds

open Purelib.Topology.Polygon

open Purelib.Topology.Polygon.Stokes

open Purelib.Topology.Surface.Cut

open Purelib.Topology.Surface.Cut.Chord

open Purelib.Topology.Surface.Cut.Chord.CutBoundaryWord
open _root_.Purelib.Topology.Surface.Cut.Chord renaming CutBoundaryWord -> Chord

open Purelib.Topology.Surface.Cut.IntegralPairing

open Purelib.Topology.Surface.Sewing

public section

/-!
# Uniform error bounds for every retained chord

Each occurrence-sensitive chord interval is no longer than the complete
boundary word. Its cached error and the complete chord-bank error vector
therefore use one word-count bound, including empty one-sided cycle slots.
The physical-boundary part of every chord decomposition remains untouched.
-/

namespace Purelib.Topology.Surface.Cut.ChordErrors

open Purelib.Topology.Surface.Cut.BoundaryWord (CutBoundaryWord)
open _root_.Purelib.Topology.Surface.Cut.IntegralPairing renaming CutBoundaryWord -> IntegralPairing
open _root_.Purelib.Topology.Surface.Cut.Chord renaming CutBoundaryWord -> Chord

open Purelib.Topology.Surface.Cut.WordErrors
open Purelib.Topology.Surface.Sewing.ChordCycleBank
open _root_.Purelib.Topology.Surface.Sewing renaming ChordCycleBank -> ChordCycleBank
open Purelib.Riemann.Readings.PrimitiveAreaBounds (AreaCoordinate)

open Purelib.Topology.Polygon.Stokes (OrientedEdge PrimitivePoint)

variable {source target : Nat} {labels : Fin source → Fin target} {edges : List (Stokes.OrientedEdge source)}
  {word : BoundaryWord.CutBoundaryWord labels edges} {pairing : IntegralPairing.CutBoundaryWord word}
  {primitive : Fin source → Stokes.PrimitivePoint} {values : Fin word.alphabet.count → Stokes.PrimitivePoint}

/-- The retained occurrence-sensitive chord interval is no longer than the original boundary word. -/
theorem Chord.interval_length_le {index : Fin word.alphabet.count} (chord : Chord.CutBoundaryWord word index) :
    chord.interval.length ≤ edges.length := by
  have first := congrArg List.length chord.first.equation
  have last := congrArg List.length chord.last.equation
  have whole := congrArg List.length word.alphabet.edges_eq
  simp only [Data.List.Append.length_append, List.length_cons, Data.List.Map.length_map] at first last whole
  simp only [Chord.interval, List.length_cons, Data.List.Append.length_append, List.length_nil]
  omega

section
open Purelib.Topology.Surface.Cut.ChordErrors
/-- Every cached chord route uses at most the complete boundary count. The empty one-sided slots satisfy the same bound
without a special budget. -/
theorem ChordCycleBank.cycle_length_le (bank : Sewing.ChordCycleBank word) (index : Fin word.alphabet.count) :
    (bank.cycles index).path.cutEdges.length ≤ edges.length := by
  rw [bank.cycles_eq]
  cases bank.coordinates index with
  | boundary => exact Nat.zero_le _
  | paired index side chord route =>
      change route.path.cutEdges.length ≤ edges.length
      rw [route.path_eq, Data.List.Map.length_map]
      exact Chord.interval_length_le chord

/-- Uniform occurrence errors bound a chord's cached error by the square of the full word count. -/
theorem Chord.Sample.error_bounded {index : Fin word.alphabet.count} {chord : Chord.CutBoundaryWord word index}
    (sample : ChordJumps.Sample chord pairing primitive values) {bound : PrimitiveAreaBounds.AreaCoordinate}
    (nonnegative : 0 ≤ bound) (bounded : CutWordArea.ErrorsBounded primitive values word.alphabet.entries bound) :
    (PrimitivePoint.Bounded sample.error) ((edges.length : PrimitiveAreaBounds.AreaCoordinate) * ((edges.length :
      PrimitiveAreaBounds.AreaCoordinate) * bound)) := by
  rw [sample.error_eq, sample.steps_eq]
  exact CutWordArea.steps_errorTotal_bounded_of_length
    (fun entry member => bounded entry (chord.interval_mem member)) nonnegative _ edges.length (Chord.interval_length_le
      chord)

end

open Purelib.Topology.Surface.Cut.ChordErrors.Chord in
/-- The same full-word error bound covers paired chord samples and empty physical-coordinate slots. -/
theorem ChordCoordinateSample.error_bounded (sample : ChordCycleBank.ChordCoordinateSample pairing primitive values)
  {bound : PrimitiveAreaBounds.AreaCoordinate}
    (nonnegative : 0 ≤ bound) (bounded : CutWordArea.ErrorsBounded primitive values word.alphabet.entries bound) :
    (PrimitivePoint.Bounded sample.error) ((edges.length : PrimitiveAreaBounds.AreaCoordinate) * ((edges.length :
      PrimitiveAreaBounds.AreaCoordinate) * bound)) := by
  cases sample with
  | boundary =>
      have countNonnegative := Cast.Order.natCast_le_direct (Nat.zero_le edges.length)
      have total := Fraction.Order.Arithmetic.mul_nonneg_direct countNonnegative
        (Fraction.Order.Arithmetic.mul_nonneg_direct countNonnegative nonnegative)
      constructor <;> simpa only [ChordCoordinateSample.error, PrimitivePoint.zero,
        Canonical.normSq_zero] using total
  | paired index side chord route sample => exact Sample.error_bounded sample nonnegative bounded

open Purelib.Topology.Surface.Cut.ChordErrors in
/-- Every cached chord-bank error satisfies the uniform full-word-count bound. -/
theorem ChordCycleBank.Sample.errors_bounded {bank : Sewing.ChordCycleBank word}
    (sample : bank.Sample pairing primitive values) {bound : PrimitiveAreaBounds.AreaCoordinate}
    (nonnegative : 0 ≤ bound) (bounded : CutWordArea.ErrorsBounded primitive values word.alphabet.entries bound)
    (index : Fin word.alphabet.count) :
    (PrimitivePoint.Bounded (sample.errors index)) ((edges.length : PrimitiveAreaBounds.AreaCoordinate) * ((edges.length
      : PrimitiveAreaBounds.AreaCoordinate) * bound)) := by
  rw [sample.errors_eq]
  exact ChordCoordinateSample.error_bounded (sample.coordinates index) nonnegative bounded

end Purelib.Topology.Surface.Cut.ChordErrors
