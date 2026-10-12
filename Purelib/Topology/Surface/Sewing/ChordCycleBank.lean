module
import Purelib.Algebra.Ring.IntCast
import Purelib.Data.Gaussian.Basic
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Vector.Basic
import Purelib.Topology.Chain.PathBoundary

import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Cut.Chord
import Purelib.Topology.Surface.Cut.IntegralPairing
import Purelib.Topology.Surface.Cut.JumpPaths
import Purelib.Topology.Surface.Sewing.VertexSewing
import Purelib.Topology.Surface.Word.Pairing
public import Purelib.Topology.Surface.Cut.ChordJumps
public import Purelib.Topology.Surface.Sewing.CutCycleChains
import Purelib.Topology.Surface.Word.ProjectedEdgePairs
meta import Mathlib.Tactic.Linter.Lint

/-!
# Fixed chord geometry and separately requested primitive samples

The occurrence selections, paths and physical counts are materialized before
any primitive is sampled. All later sample banks refer to this same geometry,
so period preparation is independent of the requested primitive accuracy.
One-sided coordinates remain explicitly empty paired-cycle slots.
-/

public section

namespace Purelib.Topology.Surface.Sewing

-- The existing nominal ChordCycleBank and its indexed sample keep their original
-- names. Duplicate-namespace lint exceptions below apply only to those declarations.

open Purelib
open Purelib.Algebra.Ring
open Purelib.Data
open Purelib.Algebra
open Purelib.Topology.Chain
open Purelib.Topology.Polygon
open Purelib.Topology.Polygon.Stokes
open Purelib.Topology.Surface.Cut
open Purelib.Topology.Surface.Cut.Chord
open Purelib.Topology.Surface.Cut.Chord.CutBoundaryWord
open _root_.Purelib.Topology.Surface.Cut.Chord renaming CutBoundaryWord -> Chord
open Purelib.Topology.Surface.Cut.ChordJumps
open Purelib.Topology.Surface.Cut.IntegralPairing
open Purelib.Topology.Surface.Cut.JumpPaths
open Purelib.Topology.Surface.Sewing
open Purelib.Topology.Surface.Sewing.CutCycleChains
open Purelib.Topology.Surface.Sewing.VertexSewing
open Purelib.Topology.Surface.Word

open Purelib.Topology.Polygon.Stokes (OrientedEdge PrimitivePoint)

open Purelib.Topology.Chain.PathBoundary (PathEndpoints)
open Purelib.Topology.Surface.Cut.BoundaryWord (CutBoundaryWord)
open _root_.Purelib.Topology.Surface.Cut.Chord renaming CutBoundaryWord -> Chord
open _root_.Purelib.Topology.Surface.Cut.IntegralPairing renaming CutBoundaryWord -> IntegralPairing
open Purelib.Topology.Surface.Cut.ChordJumps (Route Sample)
open Purelib.Topology.Surface.Sewing.CutCycleChains (ClosedCutCycle)
open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)
open Purelib.Algebra.FiniteSum.Fin (sumFin_congr sumFin_zero)

variable {source target : Nat} {labels : Fin source → Fin target} {edges : List (Stokes.OrientedEdge source)}
  {word : BoundaryWord.CutBoundaryWord labels edges} {pairing : Cut.IntegralPairing.CutBoundaryWord word}
  {primitive : Fin source → Stokes.PrimitivePoint} {values : Fin word.alphabet.count → Stokes.PrimitivePoint}

namespace ChordCycleBank

set_option genInjectivity false in
/-- An original alphabet coordinate with either a physical slot or its retained paired chord geometry.

The physical constructor retains the original generator index. The paired constructor also retains the chord and its
occurrence-preserving route. -/
inductive ChordCoordinate (word : BoundaryWord.CutBoundaryWord labels edges) where
  /-- Retain an original one-sided generator as an empty paired-cycle coordinate. -/ | boundary (index : Fin
    word.alphabet.count) (oneSided : word.alphabet.oneSided index = true)
  /-- Retain an original two-sided generator with its selected chord and cached route. -/ | paired (index : Fin
    word.alphabet.count) (twoSided : word.alphabet.oneSided index = false)
      (chord : Cut.Chord.CutBoundaryWord word index) (route : ChordJumps.Route chord)

constructive_injectivity ChordCoordinate

end ChordCycleBank

namespace ChordCycleBank.ChordCoordinate

/-- Read the original generator index from a physical or paired coordinate. -/
@[expose] def index : ChordCoordinate word → Fin word.alphabet.count
  | .boundary index _ => index
  | .paired index .. => index

/-- Retain the original generator slot, constructing a chord route exactly for two-sided generators. -/
@[expose] def build (word : BoundaryWord.CutBoundaryWord labels edges) {anchor : Fin source}
    (closed : PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish edges anchor anchor) (index : Fin
      word.alphabet.count) :
    ChordCoordinate word :=
  if side : word.alphabet.oneSided index = false then
    let chord := Chord.build word index side
    .paired index side chord (Route.build chord closed)
  else .boundary index (by cases equal : word.alphabet.oneSided index; exact (side equal).elim; rfl)

/-- Building a chord coordinate preserves its requested original generator index. -/
theorem build_index (word : BoundaryWord.CutBoundaryWord labels edges) {anchor : Fin source}
    (closed : PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish edges anchor anchor) (position : Fin
      word.alphabet.count) :
    (build word closed position).index = position := by
  unfold build
  split <;> rfl

/-- Read the retained projected closed chord path, using an empty anchored cycle for a physical slot. -/
@[expose] def cycle (anchor : Fin source) : ChordCoordinate word →
    CutCycleChains.ClosedCutCycle labels (edges.map (OrientedEdge.map labels))
  | .boundary .. => ClosedCutCycle.empty labels _ anchor
  | .paired _ _ chord route =>
      ⟨chord.pair.first.start, chord.pair.second.finish, route.path,
        congrArg OrientedEdge.finish chord.pair.opposite, route.supported⟩

end ChordCycleBank.ChordCoordinate

set_option genInjectivity false in
/-- Cached chord geometry and projected cycles for every original generator coordinate.

The retained index equations preserve the alphabet order, and physical coordinates remain explicit empty-cycle slots. -/
structure ChordCycleBank (word : BoundaryWord.CutBoundaryWord labels edges) where
  /-- Original cut anchor used by the empty physical-coordinate cycles. -/ anchor : Fin source
  /-- Cached coordinate geometry in original alphabet order. -/ coordinates : Data.Vector
    (ChordCycleBank.ChordCoordinate word) word.alphabet.count
  /-- Every retained coordinate reads its own original alphabet index. -/ indices_eq : ∀ index, (coordinates
    index).index = index
  /-- Cached actual projected closed paths for the coordinate bank. -/ cycles : Data.Vector
    (CutCycleChains.ClosedCutCycle labels (edges.map (OrientedEdge.map labels))) word.alphabet.count
  /-- Every cycle is exactly the path determined by its retained coordinate and anchor. -/ cycles_eq : ∀ index, cycles
    index = (coordinates index).cycle anchor

constructive_injectivity ChordCycleBank

namespace ChordCycleBank

/-- Cache all original chord coordinates and their closed projected cycles from the supplied closed boundary. -/
@[expose] def build (word : BoundaryWord.CutBoundaryWord labels edges) {anchor : Fin source}
    (closed : PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish edges anchor anchor) :
      ChordCycleBank word :=
  let coordinates := Data.Vector.Basic.vectorOfFn (ChordCycleBank.ChordCoordinate.build word closed)
  { anchor := anchor
    coordinates := coordinates
    indices_eq := fun index => by rw [Data.Vector.Basic.vectorOfFn_apply, ChordCycleBank.ChordCoordinate.build_index]
    cycles := Data.Vector.Basic.vectorOfFn fun index => (coordinates index).cycle anchor
    cycles_eq := Data.Vector.Basic.vectorOfFn_apply _ }

end ChordCycleBank

namespace ChordCycleBank

set_option genInjectivity false in
/-- A homogeneous cache entry keeps the selected coordinate with its full dependent local sample.

Physical slots keep their generator identity; paired slots keep the exact chord route and its cached primitive sample.
-/
inductive ChordCoordinateSample (pairing : Cut.IntegralPairing.CutBoundaryWord word) (primitive : Fin source →
  Stokes.PrimitivePoint)
    (values : Fin word.alphabet.count → Stokes.PrimitivePoint) where
  /-- Retain a physical coordinate with zero paired-cycle readings. -/ | boundary (index : Fin word.alphabet.count)
    (oneSided : word.alphabet.oneSided index = true)
  /-- Retain a paired coordinate, original chord route and its dependent primitive sample. -/ | paired (index : Fin
    word.alphabet.count) (twoSided : word.alphabet.oneSided index = false)
      (chord : Cut.Chord.CutBoundaryWord word index) (route : ChordJumps.Route chord) (sample : ChordJumps.Sample chord
        pairing primitive values)

constructive_injectivity ChordCoordinateSample

end ChordCycleBank

namespace ChordCycleBank.ChordCoordinateSample

/-- Read the exact retained geometric coordinate underlying a primitive sample. -/
@[expose] def coordinate : ChordCoordinateSample pairing primitive values →
  ChordCoordinate word
  | .boundary index side => .boundary index side
  | .paired index side chord route _ => .paired index side chord route

/-- Sample one original chord coordinate using its cached route and the supplied primitive values. -/
@[expose] def build (pairing : Cut.IntegralPairing.CutBoundaryWord word) (primitive : Fin source →
  Stokes.PrimitivePoint)
    (values : Fin word.alphabet.count → Stokes.PrimitivePoint) : ChordCoordinate word →
      ChordCoordinateSample pairing primitive values
  | .boundary index side => .boundary index side
  | .paired index side chord route => .paired index side chord route (Sample.ofRoute route pairing primitive values)

/-- Sampling preserves the exact original geometric chord coordinate. -/
theorem build_coordinate (pairing : Cut.IntegralPairing.CutBoundaryWord word) (primitive : Fin source →
  Stokes.PrimitivePoint)
    (values : Fin word.alphabet.count → Stokes.PrimitivePoint) (route : ChordCoordinate word) :
    (build pairing primitive values route).coordinate = route := by
  cases route <;> rfl

/-- Read the sampled chord jump, with zero for a physical slot. -/
@[expose] def jump : ChordCoordinateSample pairing primitive values → Stokes.PrimitivePoint
  | .boundary .. => PrimitivePoint.zero
  | .paired _ _ _ _ sample => sample.jump

/-- Read the sampled physical-path contribution, with zero for a physical slot. -/
@[expose] def physical : ChordCoordinateSample pairing primitive values → Stokes.PrimitivePoint
  | .boundary .. => PrimitivePoint.zero
  | .paired _ _ _ _ sample => sample.physicalValue

/-- Read the sampled local increment error, with zero for a physical slot. -/
@[expose] def error : ChordCoordinateSample pairing primitive values → Stokes.PrimitivePoint
  | .boundary .. => PrimitivePoint.zero
  | .paired _ _ _ _ sample => sample.error

/-- The retained original cycle increment equals the cached coordinate jump. -/
theorem cycle_jump (sample : ChordCoordinateSample pairing primitive values) (anchor : Fin source) :
    (sample.coordinate.cycle anchor).increment primitive = sample.jump := by
  cases sample with
  | boundary => rfl
  | paired index side chord route sample =>
      exact (CutPath.increment_eq primitive route.path.endpoints).trans sample.jump_eq.symm

/-- Each cached jump equals its paired-row reading plus physical and error contributions.

Physical slots contribute zero jump, while paired slots reuse their retained route's matrix row and local decomposition
certificate. -/
theorem row_eq (sample : ChordCoordinateSample pairing primitive values) :
    sample.jump = ((Pairing.linear (fun column => pairing.paired sample.coordinate.index column) values).add
      sample.physical).add sample.error := by
  cases sample with
  | boundary index side =>
      have zero : Pairing.linear (fun column => pairing.paired index column) values = PrimitivePoint.zero := by
        unfold Pairing.linear
        change PrimitivePoint.mk _ _ = PrimitivePoint.mk 0 0
        congr 1 <;> apply (FiniteSum.Fin.sumFin_congr ?_).trans FiniteSum.Fin.sumFin_zero <;> intro column <;> dsimp
          only <;>
          rw [pairing.paired_eq, side, Bool.true_or, if_pos (Eq.refl true), IntCast.cast_zero, Gaussian.Basic.zero_mul]
      change PrimitivePoint.zero = ((Pairing.linear (fun column => pairing.paired index column) values).add
        PrimitivePoint.zero).add PrimitivePoint.zero
      rw [zero]
      change PrimitivePoint.mk 0 0 = PrimitivePoint.mk (0 + 0 + 0) (0 + 0 + 0)
      rfl
  | paired index side chord route sample =>
      have result := sample.jump_decomposition side
      rw [sample.rowValue_eq] at result
      exact result

end ChordCycleBank.ChordCoordinateSample

namespace ChordCycleBank

set_option genInjectivity false in
/-- Cached primitive readings indexed by one fixed original chord-geometry bank.

Separate jump, physical and error vectors read the same dependent coordinate samples and preserve their original
geometric ownership. -/
structure Sample (bank : ChordCycleBank word) (pairing : Cut.IntegralPairing.CutBoundaryWord word) (primitive
  : Fin source → Stokes.PrimitivePoint)
    (values : Fin word.alphabet.count → Stokes.PrimitivePoint) where
  /-- Cached dependent primitive samples for the original geometric coordinates. -/ coordinates :
    Data.Vector (ChordCoordinateSample pairing primitive values) word.alphabet.count
  /-- Each sample retains the exact coordinate from the original bank. -/ coordinates_eq : ∀ index, (coordinates
    index).coordinate = bank.coordinates index
  /-- Cached primitive jump of each retained coordinate sample. -/ jumps : Data.Vector
    Stokes.PrimitivePoint word.alphabet.count
  /-- The jump vector reads those exact cached samples. -/ jumps_eq : ∀ index, jumps index = (coordinates index).jump
  /-- Cached physical-path contribution of each retained coordinate sample. -/ physical : Data.Vector
    Stokes.PrimitivePoint word.alphabet.count
  /-- The physical vector reads those exact cached samples. -/ physical_eq : ∀ index, physical index = (coordinates
    index).physical
  /-- Cached local increment error of each retained coordinate sample. -/ errors : Data.Vector
    Stokes.PrimitivePoint word.alphabet.count
  /-- The error vector reads those exact cached samples. -/ errors_eq : ∀ index, errors index = (coordinates
    index).error

constructive_injectivity Sample

/-- Request new primitive readings without selecting occurrences, constructing paths, or evaluating physical
multiplicities again. -/
@[expose] def sample (bank : ChordCycleBank word) (pairing : Cut.IntegralPairing.CutBoundaryWord word)
  (primitive : Fin source → Stokes.PrimitivePoint)
    (values : Fin word.alphabet.count → Stokes.PrimitivePoint) : Sample bank pairing primitive values :=
  let coordinates := Data.Vector.Basic.vectorOfFn fun index => ChordCycleBank.ChordCoordinateSample.build pairing
    primitive values (bank.coordinates index)
  { coordinates := coordinates
    coordinates_eq := fun index => by rw [Data.Vector.Basic.vectorOfFn_apply,
      ChordCycleBank.ChordCoordinateSample.build_coordinate]
    jumps := Data.Vector.Basic.vectorOfFn fun index => (coordinates index).jump
    jumps_eq := Data.Vector.Basic.vectorOfFn_apply _
    physical := Data.Vector.Basic.vectorOfFn fun index => (coordinates index).physical
    physical_eq := Data.Vector.Basic.vectorOfFn_apply _
    errors := Data.Vector.Basic.vectorOfFn fun index => (coordinates index).error
    errors_eq := Data.Vector.Basic.vectorOfFn_apply _ }

namespace Sample

variable {bank : ChordCycleBank word}

/-- Each original bank cycle reads the corresponding cached sample jump. -/
theorem cycle_jump (sample : Sample bank pairing primitive values) (index : Fin word.alphabet.count) :
    (bank.cycles index).increment primitive = sample.jumps index := by
  rw [bank.cycles_eq, ← sample.coordinates_eq, sample.jumps_eq]
  exact (sample.coordinates index).cycle_jump bank.anchor

/-- Every retained jump decomposes into its original paired-matrix row, physical reading and local error. -/
theorem row_eq (sample : Sample bank pairing primitive values) (index : Fin word.alphabet.count) :
    sample.jumps index = ((Pairing.linear (fun column => pairing.paired index column) values).add
      (sample.physical index)).add (sample.errors index) := by
  have result := (sample.coordinates index).row_eq
  rw [sample.coordinates_eq, bank.indices_eq] at result
  rw [sample.jumps_eq, sample.physical_eq, sample.errors_eq]
  exact result

end Sample
end ChordCycleBank
end Purelib.Topology.Surface.Sewing

end
