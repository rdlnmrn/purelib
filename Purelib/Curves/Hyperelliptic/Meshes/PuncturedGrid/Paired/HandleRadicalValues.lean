module
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.Ring.IntCast
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Vector.Basic
import Purelib.LinearAlgebra.Alternating.Handle.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleCoordinates
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Boundary.BoundaryCoordinates
import Purelib.Topology.Surface.Chord.Spanning
import Purelib.Topology.Surface.Sewing.VertexSewing
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleWords
import Init.Prelude
import Mathlib.Algebra.Ring.Int.Defs
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryWord
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Cut.IntegralPairing
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.ChordCycleBank
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Surface.Word.NormalForm
import Purelib.Topology.Surface.Word.PairedWord
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleCoordinates

open Purelib.LinearAlgebra.Alternating

open Purelib.Topology.Polygon

open Purelib.Topology.Surface.Boundary.BoundaryCoordinates

open Purelib.Topology.Surface.Chord.Spanning.CutBoundaryWord

open Purelib.Topology.Surface.Sewing.VertexSewing

@[expose] public section

/-! Unused normal-form cycle rows retain their actual physical-boundary values. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleWords.CutBank.HandleChains

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Topology.Polygon.Stokes (OrientedEdge)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Topology.Surface.Boundary.BoundaryCoordinates (WordCoordinates)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank (Ordered)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered (Paired)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms (Prepared)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates (CutBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleCoordinates.CutBank (HandleVector)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleWords.CutBank (HandleChains)
open _root_.Purelib.Data (Vector)
open _root_.Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_zero sumFin_add sumFin_neg sumFin_swap sumFin_mul_left
  sumFin_mul_right)
open Purelib.LinearAlgebra.Alternating.Handle.Basic (handleIndices)
local notation "vget" => Data.Vector.get

/-- Casting the finite original integer sum to Gaussian rationals preserves its indexed summands. -/
private theorem cast_sum {count : Nat} (values : Fin count → Int) :
    ((sumFin values : Int) : Data.Gaussian.Basic.Canonical) = sumFin (fun index => (values index :
      Data.Gaussian.Basic.Canonical)) := by
  induction count with
  | zero => exact Ring.IntCast.cast_zero
  | succ count ih => rw [FiniteSum.Fin.sumFin_succ,
      FiniteSum.Fin.sumFin_succ, Ring.IntCast.add, ih]

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {bank :
    BasedBranchBank lifted}
    {sheet : Fin 2}
  {ordered :
    Ordered bank
    sheet} {paired : Paired ordered}
    {prepared : Prepared paired}

variable {cut : CutBank prepared} (chains :
  HandleChains cut)

/-- Physical coefficients of one retained normal-form combination of actual chord cycles. -/
def physicalCycleRow (index : Fin lifted.cutBoundaryWord.alphabet.count) : CutBank.HandleVector cut :=
  Data.Vector.Basic.vectorOfFn fun column => sumFin fun position =>
    vget (vget chains.weights index) position * (ChordCoordinate.physicalRow (chains.chords.chords.coordinates
      position)) column

/-- Each physical cycle coordinate is the original retained weighted sum of chord physical coordinates. -/
theorem physicalCycleRow_apply (index column : Fin lifted.cutBoundaryWord.alphabet.count) :
    vget (chains.physicalCycleRow index) column = sumFin (fun position =>
      vget (vget chains.weights index) position * (ChordCoordinate.physicalRow (chains.chords.chords.coordinates
        position)) column) :=
  Data.Vector.Basic.vectorOfFn_apply _ _

/-- The actual physical cycle row vanishes on every paired column. -/
theorem physicalCycleRow_paired_zero (index column : Fin lifted.cutBoundaryWord.alphabet.count)
    (side : lifted.cutBoundaryWord.alphabet.oneSided column = false) : vget (chains.physicalCycleRow index) column = 0
      := by
  rw [chains.physicalCycleRow_apply]
  exact (FiniteSum.Fin.sumFin_congr (fun position => by
    rw [ChordCoordinate.physicalRow_paired_zero (chains.chords.chords.coordinates position) column side,
      mul_zero])).trans FiniteSum.Fin.sumFin_zero

/-- The unused transformed row annihilates every paired column, with its cached weights. -/
theorem unused_paired_row (index : Fin lifted.cutBoundaryWord.alphabet.count)
    (unused : index ∉ Handle.Basic.handleIndices cut.normal.pivots) (column : Fin lifted.cutBoundaryWord.alphabet.count)
      :
    sumFin (fun position => vget (vget chains.weights index) position * cut.integral.paired position column) = 0 := by
  calc
    _ = sumFin (fun position => -(cut.integral.paired column position *
        cut.normal.normal.reduction.cycleRows index position)) := by
      apply FiniteSum.Fin.sumFin_congr
      intro position
      rw [chains.weights_eq, cut.integral.paired_skew position column]
      ring1
    _ = -(sumFin (fun position => cut.integral.paired column position *
        cut.normal.normal.reduction.cycleRows index position)) := FiniteSum.Fin.sumFin_neg _
    _ = 0 := (congrArg Neg.neg (cut.normal.normal.unused_kernel index unused column)).trans neg_zero

/-- Combining the original integer rows and then evaluating equals evaluation with their retained weighted coordinate
sum. -/
private theorem combine_rows {count : Nat} (weights : Fin count → Int)
    (rows : Fin count → Fin count → Int) (values : Fin count → Data.Gaussian.Basic.Canonical) :
    WordCoordinates.combine weights (fun index => WordCoordinates.combine (rows index) values) =
      WordCoordinates.combine (fun column => sumFin (fun index => weights index * rows index column)) values := by
  symm
  calc
    _ = sumFin (fun column => sumFin (fun index =>
        (weights index : Data.Gaussian.Basic.Canonical) * (rows index column : Data.Gaussian.Basic.Canonical) * values
          column)) := by
      apply FiniteSum.Fin.sumFin_congr
      intro column
      rw [cast_sum, ←
        FiniteSum.Fin.sumFin_mul_right]
      apply FiniteSum.Fin.sumFin_congr
      intro index
      rw [Ring.IntCast.intCast_mul]
    _ = _ := by
      rw [FiniteSum.Fin.sumFin_swap]
      apply FiniteSum.Fin.sumFin_congr
      intro index
      exact (FiniteSum.Fin.sumFin_congr (fun column => _root_.mul_assoc _ _ _)).trans (FiniteSum.Fin.sumFin_mul_left _
        _)

/-- The paired and physical pieces come from the same retained chord bank. -/
theorem cycleValues_split (index : Fin lifted.cutBoundaryWord.alphabet.count)
    (value : Stokes.OrientedEdge lifted.vertices.count → Data.Gaussian.Basic.Canonical) (anti : ∀ edge, value
      edge.reverse = -value edge) :
    chains.cycleValues value index =
      WordCoordinates.combine (fun column => sumFin (fun position =>
        vget (vget chains.weights index) position * cut.integral.paired position column))
        (fun column => value (OrientedEdge.map lifted.cutPolygon.patch.cut.vertexLabels
          (lifted.cutBoundaryWord.alphabet.generators column))) +
      WordCoordinates.combine (vget (chains.physicalCycleRow index))
        (fun column => value (OrientedEdge.map lifted.cutPolygon.patch.cut.vertexLabels
          (lifted.cutBoundaryWord.alphabet.generators column))) := by
  unfold Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleWords.CutBank.HandleChains.cycleValues
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleWords.CutBank.HandleChains.chordValues
  dsimp only [WordCoordinates.combine]
  calc
    _ = sumFin (fun position =>
        ((vget (vget chains.weights index) position : Int) : Data.Gaussian.Basic.Canonical) * WordCoordinates.combine
          (cut.integral.paired position)
          (fun column => value (OrientedEdge.map lifted.cutPolygon.patch.cut.vertexLabels
            (lifted.cutBoundaryWord.alphabet.generators column))) +
        ((vget (vget chains.weights index) position : Int) : Data.Gaussian.Basic.Canonical) * WordCoordinates.combine
          (ChordCoordinate.physicalRow (chains.chords.chords.coordinates position))
          (fun column => value (OrientedEdge.map lifted.cutPolygon.patch.cut.vertexLabels
            (lifted.cutBoundaryWord.alphabet.generators column)))) := by
      apply FiniteSum.Fin.sumFin_congr
      intro position
      rw [ChordCycleBank.cycle_value
        chains.chords.chords cut.integral value anti position, mul_add]
    _ = _ := by
      rw [FiniteSum.Fin.sumFin_add]
      let values := fun column => value (OrientedEdge.map lifted.cutPolygon.patch.cut.vertexLabels
        (lifted.cutBoundaryWord.alphabet.generators column))
      have paired := combine_rows
        (vget (vget chains.weights index)) (fun position => vget (vget cut.integral.paired position)) values
      have physical := combine_rows
        (vget (vget chains.weights index))
        (fun position => vget (ChordCoordinate.physicalRow (chains.chords.chords.coordinates position))) values
      exact congrArg₂ (· + ·) paired (physical.trans (FiniteSum.Fin.sumFin_congr (fun column =>
        congrArg (fun weight : Int => (weight : Data.Gaussian.Basic.Canonical) * values column)
          (chains.physicalCycleRow_apply index column).symm)))

/-- No unused cycle is discarded: its value is the explicitly retained physical row. -/
theorem unused_cycleValues (index : Fin lifted.cutBoundaryWord.alphabet.count)
    (unused : index ∉ Handle.Basic.handleIndices cut.normal.pivots)
    (value : Stokes.OrientedEdge lifted.vertices.count → Data.Gaussian.Basic.Canonical) (anti : ∀ edge, value
      edge.reverse = -value edge) :
    chains.cycleValues value index = WordCoordinates.combine (vget (chains.physicalCycleRow index))
      (fun column => value (OrientedEdge.map lifted.cutPolygon.patch.cut.vertexLabels
        (lifted.cutBoundaryWord.alphabet.generators column))) := by
  rw [chains.cycleValues_split index value anti]
  have zero : WordCoordinates.combine (fun column => sumFin (fun position =>
      vget (vget chains.weights index) position * cut.integral.paired position column))
      (fun column => value (OrientedEdge.map lifted.cutPolygon.patch.cut.vertexLabels
        (lifted.cutBoundaryWord.alphabet.generators column))) = 0 :=
    (FiniteSum.Fin.sumFin_congr (fun column => by
      dsimp only
      rw [chains.unused_paired_row index unused column, Ring.IntCast.cast_zero, zero_mul])).trans
        FiniteSum.Fin.sumFin_zero
  rewrite [zero]
  exact Data.Gaussian.Basic.zero_add _

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleWords.CutBank.HandleChains
