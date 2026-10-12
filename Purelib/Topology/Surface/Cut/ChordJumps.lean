module
import Purelib.Data.List.Map
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Vector.Basic
import Purelib.Topology.Chain.PathBoundary

import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Cut.IntegralPairing
import Purelib.Topology.Surface.Cut.JumpPaths
import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Purelib.Topology.Surface.Sewing.VertexSewing
import Purelib.Topology.Surface.Word.PairedWord
import Purelib.Topology.Surface.Word.Pairing
import Purelib.Topology.Surface.Word.SignedWord
import Purelib.Topology.Surface.Word.Surgery
public import Purelib.Topology.Surface.Cut.Chord
public import Purelib.Topology.Surface.Cut.WordArea
import Purelib.Topology.Surface.Word.ProjectedEdgePairs
import Purelib.Topology.Surface.Word.Selection
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring

/-!
# Actual chord jumps, paired rows, and their retained corrections

The closed projected chord path has a generally nonzero cut-primitive jump.
Its exact decomposition uses the cached paired matrix row, the one-sided
letters in the actual chord interval, and the sum of that interval's local
increment errors. Neither correction is assumed to vanish.
-/

public section

namespace Purelib.Topology.Surface.Cut.ChordJumps

open Purelib.Data.List

open Purelib
open Purelib.Algebra
open Purelib.Topology.Chain
open Purelib.Topology.Polygon
open Purelib.Topology.Polygon.Stokes
open Purelib.Topology.Surface.Cut
open Purelib.Topology.Surface.Cut.BoundaryWord
open Purelib.Topology.Surface.Cut.Chord
open Purelib.Topology.Surface.Cut.Chord.CutBoundaryWord
open _root_.Purelib.Topology.Surface.Cut.Chord renaming CutBoundaryWord -> Chord
open Purelib.Topology.Surface.Cut.IntegralPairing
open Purelib.Topology.Surface.Cut.JumpPaths
open Purelib.Topology.Surface.Cut.WordArea
open Purelib.Topology.Surface.Sewing.VertexSewing
open Purelib.Topology.Surface.Word
open Purelib.Topology.Surface.Word.PairedWord
open Purelib.Topology.Surface.Word.SignedWord
open Purelib.Topology.Surface.Word.Surgery

open Purelib.Topology.Polygon.Stokes (OrientedEdge PrimitivePoint)

open Purelib.Topology.Chain.PathBoundary (PathEndpoints)
open Purelib.Topology.Surface.Cut.BoundaryWord (CutBoundaryWord CutWordEntry)
open _root_.Purelib.Topology.Surface.Cut.Chord renaming CutBoundaryWord -> Chord
open _root_.Purelib.Topology.Surface.Cut.IntegralPairing renaming CutBoundaryWord -> IntegralPairing
open Purelib.Topology.Surface.Word.SignedWord (SignedGenerator)
open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)
open Purelib.Algebra.FiniteSum.Fin (sumFin_congr)

variable {source target : Nat} {labels : Fin source → Fin target} {edges : List (Stokes.OrientedEdge source)}
  {word : BoundaryWord.CutBoundaryWord labels edges} {index : Fin word.alphabet.count}

/-- Retain the one-sided physical letters in the selected chord's signed interior word. -/
@[expose] def physicalLetters (chord : Chord.CutBoundaryWord word index) : List (SignedWord.SignedGenerator
  word.alphabet.count) :=
  SignedGenerator.retain word.alphabet.oneSided chord.selected.chord.inside

/-- The chord's complete interval and signed interior have the same coefficient total. -/
theorem interval_total (chord : Chord.CutBoundaryWord word index) (column : Fin word.alphabet.count) :
    Pairing.totalAt (CutWordArea.word chord.interval) column =
      Pairing.totalAt (chord.selected.chord.inside.map SignedGenerator.coefficients) column := by
  have flattened : CutWordArea.word chord.interval =
      (chord.interval.map CutWordEntry.letter).map SignedGenerator.coefficients := by rw [Map.map_map]; rfl
  rw [flattened]
  simp only [Chord.interval, List.map_cons, Map.map_append, List.map_nil,
    chord.first.letter_eq, chord.last.letter_eq, Pairing.totalAt, Word.Surgery.totalAt_append]
  change (SignedGenerator.coefficients ⟨index, false⟩ column +
    (Pairing.totalAt (chord.selected.chord.inside.map SignedGenerator.coefficients) column +
      (SignedGenerator.coefficients ⟨index, true⟩ column + 0))) = _
  by_cases same : column = index
  · cases same
    rw [SignedGenerator.coefficient_self, SignedGenerator.coefficient_self]
    change 1 + (_ + (-1 + 0)) = _
    omega
  · rw [SignedGenerator.coefficient_zero_of_ne _ column (Ne.symm same),
      SignedGenerator.coefficient_zero_of_ne _ column (Ne.symm same)]
    omega

/-- A chord interval's total is its paired matrix row plus its retained physical-letter contribution. -/
theorem total_eq_row_add_physical (chord : Chord.CutBoundaryWord word index) (pairing : IntegralPairing
  word)
    (paired : word.alphabet.oneSided index = false) (column : Fin word.alphabet.count) :
    Pairing.totalAt (CutWordArea.word chord.interval) column = pairing.paired index column +
      Pairing.totalAt ((physicalLetters chord).map SignedGenerator.coefficients) column := by
  rw [interval_total chord, chord.paired_row pairing paired, physicalLetters,
    SignedGenerator.total_retain, SignedGenerator.total_retain]
  cases word.alphabet.oneSided column <;>
    simp only [Bool.not_false, Bool.not_true, -eq_self, -iff_self]
    <;> rw [if_pos (Eq.refl true)]
    <;> rw [if_neg (show false ≠ true by intro impossible; cases impossible)]
    <;> omega

set_option genInjectivity false in
/-- Fixed occurrence-preserving path and physical counts, independent of all primitive readings. Refinement requests
reuse this geometry. -/
structure Route (chord : Chord.CutBoundaryWord word index) where
  /-- Cached cut path and its projected surface path with exact endpoints. -/ path : CutPath.Projected labels
    chord.pair.first.start chord.pair.second.finish
  /-- The cached cut edges are exactly the retained chord interval edges. -/ path_eq : path.cutEdges =
    chord.interval.map CutWordEntry.edge
  /-- Cached integral row of the chord's one-sided physical letters. -/ physicalCoefficients : Pairing.Coefficients
    word.alphabet.count
  /-- Each physical coefficient is the corresponding total of the retained physical letters. -/ physicalCoefficients_eq
    : ∀ column, physicalCoefficients column =
    Pairing.totalAt ((physicalLetters chord).map SignedGenerator.coefficients) column

constructive_injectivity Route

namespace Route

/-- Cache the exact chord path and physical coefficient row independently of primitive readings. -/
@[expose] def build (chord : Chord.CutBoundaryWord word index) {anchor : Fin source}
    (closed : PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish edges anchor anchor) : Route
      chord :=
  let path := chord.path closed
  let physicalWord := (physicalLetters chord).map SignedGenerator.coefficients
  ⟨path, rfl, Data.Vector.Basic.vectorOfFn fun column => Pairing.totalAt physicalWord column,
    Data.Vector.Basic.vectorOfFn_apply _⟩

/-- The cached chord route is supported on the projected original cut boundary. -/
theorem supported {chord : Chord.CutBoundaryWord word index} (route : Route chord) :
    CutPath.Supported (edges.map (OrientedEdge.map labels)) route.path.surfaceEdges := by
  rw [route.path.projection_eq, route.path_eq]
  exact CutPath.supported_map labels chord.interval_supported

end Route

set_option genInjectivity false in
/-- The path, local comparison steps, physical counts, and all evaluated contributions are cached. Generated data can
fill the same semantic fields; no equality with an expensive canonical constructor is required. -/
structure Sample (chord : Chord.CutBoundaryWord word index) (pairing : IntegralPairing word)
    (primitive : Fin source → Stokes.PrimitivePoint) (values : Fin word.alphabet.count → Stokes.PrimitivePoint) where
  /-- Retained exact cut path and projected surface path. -/ path : CutPath.Projected labels chord.pair.first.start
    chord.pair.second.finish
  /-- The sampled cut edges are the original chord interval edges. -/ path_eq : path.cutEdges = chord.interval.map
    CutWordEntry.edge
  /-- Cached local primitive comparison steps along the original chord interval. -/ steps : List (CutWordArea.Step
    (labels := labels) (generators := word.alphabet.generators) primitive values)
  /-- The retained steps use the exact primitive values, generator values, and initial endpoint. -/ steps_eq : steps =
    CutWordArea.steps primitive values (primitive chord.pair.first.start) chord.interval
  /-- Retained physical-letter coefficient row of the original chord. -/ physicalCoefficients : Pairing.Coefficients
    word.alphabet.count
  /-- Its entries are the exact totals of the selected physical letters. -/ physicalCoefficients_eq : ∀ column,
    physicalCoefficients column =
    Pairing.totalAt ((physicalLetters chord).map SignedGenerator.coefficients) column
  /-- Cached primitive value of the paired matrix row. -/ rowValue : Stokes.PrimitivePoint
  /-- The row value evaluates the original paired matrix row on the supplied generator values. -/ rowValue_eq : rowValue
    = Pairing.linear (fun column => pairing.paired index column) values
  /-- Cached primitive contribution of the retained physical coefficient row. -/ physicalValue : Stokes.PrimitivePoint
  /-- The physical value is the linear evaluation of the retained physical coefficients. -/ physicalValue_eq :
    physicalValue = Pairing.linear physicalCoefficients values
  /-- Cached total local increment error along the chord interval. -/ error : Stokes.PrimitivePoint
  /-- The error is the exact sum of the retained comparison-step errors. -/ error_eq : error = CutWordArea.errorTotal
    steps
  /-- Cached primitive difference between the chord's original final and initial endpoints. -/ jump :
    Stokes.PrimitivePoint
  /-- The retained jump is the exact final primitive value minus the initial value. -/ jump_eq : jump =
    (PrimitivePoint.sub (primitive chord.pair.second.finish)) (primitive chord.pair.first.start)

constructive_injectivity Sample

namespace Sample

variable {chord : Chord.CutBoundaryWord word index} {pairing : IntegralPairing word}
  {primitive : Fin source → Stokes.PrimitivePoint} {values : Fin word.alphabet.count → Stokes.PrimitivePoint}

/-- Reuse a retained geometric chord route to cache its primitive comparison data.

The original path and physical coefficients are preserved while local steps, paired-row value, error, and endpoint jump
are evaluated once. -/
@[expose] def ofRoute (route : Route chord) (pairing : IntegralPairing word)
    (primitive : Fin source → Stokes.PrimitivePoint) (values : Fin word.alphabet.count → Stokes.PrimitivePoint) :
      Sample chord pairing primitive values :=
  let interval := chord.interval
  let steps := CutWordArea.steps primitive values (primitive chord.pair.first.start) interval
  { path := route.path, path_eq := route.path_eq, steps := steps, steps_eq := rfl
    physicalCoefficients := route.physicalCoefficients, physicalCoefficients_eq := route.physicalCoefficients_eq
    rowValue := Pairing.linear (fun column => pairing.paired index column) values, rowValue_eq := rfl
    physicalValue := Pairing.linear route.physicalCoefficients values, physicalValue_eq := rfl
    error := CutWordArea.errorTotal steps, error_eq := rfl
    jump := (PrimitivePoint.sub (primitive chord.pair.second.finish)) (primitive chord.pair.first.start), jump_eq := rfl
      }

/-- The cached cut-path increment is the retained endpoint jump. -/
theorem path_jump (sample : Sample chord pairing primitive values) :
    CutPath.increment primitive sample.path.cutEdges = sample.jump :=
  (CutPath.increment_eq primitive sample.path.endpoints).trans sample.jump_eq.symm

/-- The sample's exact projected surface path is closed at the projected first source. -/
theorem closed (sample : Sample chord pairing primitive values) :
    PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish sample.path.surfaceEdges
      (labels chord.pair.first.start) (labels chord.pair.first.start) :=
  sample.path.closed (congrArg OrientedEdge.finish chord.pair.opposite)

/-- The projected sampled chord path has zero vertex boundary pointwise. -/
theorem boundary_zero (sample : Sample chord pairing primitive values) (vertex : Fin target) :
    PathBoundary.wordBoundaryAt OrientedEdge.start OrientedEdge.finish sample.path.surfaceEdges vertex = 0 :=
  sample.path.boundary_zero (congrArg OrientedEdge.finish chord.pair.opposite) vertex

/-- The sampled surface path remains supported on the projected cut boundary. -/
theorem supported (sample : Sample chord pairing primitive values) :
    CutPath.Supported (edges.map (OrientedEdge.map labels)) sample.path.surfaceEdges := by
  rw [sample.path.projection_eq, sample.path_eq]
  exact CutPath.supported_map labels chord.interval_supported

/-- A paired chord jump equals its paired-row value, physical contribution, and retained local error. -/
theorem jump_decomposition (sample : Sample chord pairing primitive values)
    (paired : word.alphabet.oneSided index = false) :
    sample.jump = (sample.rowValue.add sample.physicalValue).add sample.error := by
  have path := sample.path.endpoints
  rw [sample.path_eq] at path
  have errors := CutWordArea.errorTotal_eq primitive values chord.interval path (primitive chord.pair.first.start)
  have total : Pairing.linear (Pairing.totalAt (CutWordArea.word chord.interval)) values =
      (Pairing.linear (fun column => pairing.paired index column) values).add
        (Pairing.linear sample.physicalCoefficients values) := by
    have evaluated : Pairing.linear (Pairing.totalAt (CutWordArea.word chord.interval)) values =
        Pairing.linear (fun column => pairing.paired index column + sample.physicalCoefficients column) values := by
      unfold Pairing.linear
      congr 1 <;> apply FiniteSum.Fin.sumFin_congr <;> intro column <;> dsimp only <;>
        rw [sample.physicalCoefficients_eq, total_eq_row_add_physical chord pairing paired]
    exact evaluated.trans (Pairing.linear_add _ _ values)
  rw [sample.rowValue_eq, sample.physicalValue_eq, sample.error_eq, sample.steps_eq, errors, total, sample.jump_eq]
  simp only [PrimitivePoint.add, PrimitivePoint.sub]
  congr 1 <;> ring1

end Sample
end Purelib.Topology.Surface.Cut.ChordJumps

end
