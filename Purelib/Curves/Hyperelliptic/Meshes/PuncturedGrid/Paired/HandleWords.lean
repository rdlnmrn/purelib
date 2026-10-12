module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.Ring.IntCast
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Vector.Basic
import Purelib.LinearAlgebra.Matrix.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Boundary.BoundaryCoordinates
import Purelib.Topology.Surface.Chord.Spanning
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Topology.Surface.Sewing.VertexSewing
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleCoordinates
import Init.Data.Int.Basic
import Init.Prelude
import Mathlib.Algebra.Ring.Int.Defs
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryWord
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Dependent
import Purelib.LinearAlgebra.Alternating.NormalForm.Basic
import Purelib.LinearAlgebra.Alternating.Reduction.CycleRows
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Cut.JumpPaths
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Cut.Spanning
import Purelib.Topology.Surface.Sewing.ChordCycleBank
import Purelib.Topology.Surface.Sewing.CutCycleChains
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Surface.Word.NormalForm
import Purelib.Topology.Surface.Word.PairedWord
import Purelib.Topology.Surface.Word.Surgery
public import Purelib.LinearAlgebra.Alternating.Reduction.Reconstruction

open Purelib

open Purelib.Algebra

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleCoordinates

open Purelib.Topology.Polygon

open Purelib.Topology.Surface.Boundary.BoundaryCoordinates

open Purelib.Topology.Surface.Chord.Spanning

open Purelib.Topology.Surface.Sewing

open Purelib.Topology.Surface.Sewing.VertexSewing

@[expose] public section

/-!
# Exact ordered words in the computed normal-form cycle rows

The shared chord bank and cycle-row matrix are retained once. Every A/B word
is reconstructed from its cached handle coordinates, together with its actual
physical boundary and face corrections. Unused normal coordinates remain in
the sum; no radical contribution is silently dropped.
-/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleWords

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Topology.Polygon.Stokes (OrientedEdge)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Topology.Surface.Sewing.SewingRetraction (wordValue faceValue)
open Purelib.Topology.Surface.Boundary.BoundaryCoordinates (WordCoordinates)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank (Ordered)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered (Paired)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms (Prepared)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates (CutBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleCoordinates.CutBank (HandleVector HandleRow)
local notation "vget" => Data.Vector.get
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_swap sumFin_mul_left sumFin_mul_right)

/-- Casting a complete finite integer sum to Gaussian rationals preserves all indexed summands. -/
private theorem cast_sum {count : Nat} (values : Fin count → Int) :
    ((sumFin values : Int) : Data.Gaussian.Basic.Canonical) = sumFin (fun index => (values index :
      Data.Gaussian.Basic.Canonical)) := by
  induction count with
  | zero => exact Ring.IntCast.cast_zero
  | succ count ih => rw [FiniteSum.Fin.sumFin_succ,
      FiniteSum.Fin.sumFin_succ, Ring.IntCast.add, ih]

/-- Valuating a finite integer combination of rows equals the same combination of their original Gaussian valuations. -/
private theorem combine_rows {count : Nat} (weights : Fin count → Int)
    (rows : Fin count → Fin count → Int) (values : Fin count → Data.Gaussian.Basic.Canonical) :
    WordCoordinates.combine (fun column => sumFin (fun index => weights index * rows index column)) values =
      WordCoordinates.combine weights (fun index => WordCoordinates.combine (rows index) values) := by
  calc
    _ = sumFin (fun column => sumFin (fun index =>
        (weights index : Data.Gaussian.Basic.Canonical) * (rows index column : Data.Gaussian.Basic.Canonical) * values
          column)) := by
      apply FiniteSum.Fin.sumFin_congr
      intro column
      rw [Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleWords.cast_sum, ← FiniteSum.Fin.sumFin_mul_right]
      apply FiniteSum.Fin.sumFin_congr
      intro index
      rw [Ring.IntCast.intCast_mul]
    _ = _ := by
      rw [FiniteSum.Fin.sumFin_swap]
      apply FiniteSum.Fin.sumFin_congr
      intro index
      exact (FiniteSum.Fin.sumFin_congr (fun column => mul_assoc _ _ _)).trans (FiniteSum.Fin.sumFin_mul_left _ _)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Purelib.Riemann.Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Purelib.Riemann.Meshes.LiftedPuncturedGrid base} {bank :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted}
    {sheet : Fin 2}
  {ordered :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered bank
    sheet} {paired : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered.Paired ordered}
    {prepared : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired}

namespace CutBank

/-- The full integer cycle-row matrix on the original retained cut alphabet. -/
def CycleWeights (_cut : PeriodCoordinates.CutBank prepared) :=
  LinearAlgebra.Matrix Int lifted.cutBoundaryWord.alphabet.count

/-- Every retained matrix entry equals the corresponding original normal-form cycle-row entry. -/
def CycleWeightsEq (cut : PeriodCoordinates.CutBank prepared) (weights :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleWords.CutBank.CycleWeights cut) : Prop :=
  ∀ row column, vget (vget weights row) column = cut.normal.normal.reduction.cycleRows row column

set_option genInjectivity false in
/-- The shared original chord bank and exact cached normal-form cycle-row matrix. -/
structure HandleChains (cut : PeriodCoordinates.CutBank prepared) where
  /-- The retained chord realization of the original complete cut bank. -/ chords : cut.OnChords
  /-- The cached full cycle-row matrix on that exact original cut alphabet. -/ weights :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleWords.CutBank.CycleWeights cut
  /-- The matrix cache retains every original computed normal-form cycle-row entry. -/ weights_eq :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleWords.CutBank.CycleWeightsEq cut weights

constructive_injectivity HandleChains

namespace HandleChains

variable {cut : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates.CutBank prepared} {index :
  Fin genus}

/-- Retain the original cut's chord bank and reuse its complete computed cycle-row matrix. -/
def build (cut : PeriodCoordinates.CutBank prepared) :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleWords.CutBank.HandleChains cut :=
  ⟨cut.onChords, cut.normal.normal.reduction.cycleRows, fun _ _ => rfl⟩

/-- The values of the actual closed chord routes on this retained surface. -/
def chordValues (chains : Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleWords.CutBank.HandleChains cut) (value
  : Stokes.OrientedEdge lifted.vertices.count → Data.Gaussian.Basic.Canonical)
    (column : Fin lifted.cutBoundaryWord.alphabet.count) : Gaussian :=
  SewingRetraction.wordValue value (chains.chords.chords.cycles column).path.surfaceEdges

/-- Evaluate cached normal-form cycle rows, rather than recomputing their integer change of basis in each A/B
evaluation. -/
def cycleValues (chains : Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleWords.CutBank.HandleChains cut) (value
  : Stokes.OrientedEdge lifted.vertices.count → Data.Gaussian.Basic.Canonical)
    (row : Fin lifted.cutBoundaryWord.alphabet.count) : Gaussian :=
  WordCoordinates.combine (vget (vget chains.weights row)) (chains.chordValues value)

/-- The original A span coefficients are exactly the retained handle coordinates combined with the cached cycle rows. -/
theorem a_coefficients (chains : Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleWords.CutBank.HandleChains cut)
  (row : CutBank.HandleRow cut index)
    (column : Fin lifted.cutBoundaryWord.alphabet.count) :
    (cut.rows.get index).a.span.coefficients column =
      sumFin (fun position => vget row.a position * vget (vget chains.weights position) column) := by
  calc
    _ = cut.normal.normal.reduction.dualBackward row.a column :=
      (congrArg (fun values : CutBank.HandleVector cut => vget values column) row.a_readback).symm
    _ = sumFin (fun position => vget row.a position * cut.normal.normal.reduction.cycleRows position column) :=
      cut.normal.normal.reduction.dualBackward_eq_cycleRows _ column
    _ = _ := FiniteSum.Fin.sumFin_congr (fun position => congrArg (fun weight : Int => vget row.a position * weight)
      (chains.weights_eq position column).symm)

/-- The original B span coefficients are exactly the retained handle coordinates combined with those same cached cycle
rows. -/
theorem b_coefficients (chains : Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleWords.CutBank.HandleChains cut)
  (row : CutBank.HandleRow cut index)
    (column : Fin lifted.cutBoundaryWord.alphabet.count) :
    (cut.rows.get index).b.span.coefficients column =
      sumFin (fun position => vget row.b position * vget (vget chains.weights position) column) := by
  calc
    _ = cut.normal.normal.reduction.dualBackward row.b column :=
      (congrArg (fun values : CutBank.HandleVector cut => vget values column) row.b_readback).symm
    _ = sumFin (fun position => vget row.b position * cut.normal.normal.reduction.cycleRows position column) :=
      cut.normal.normal.reduction.dualBackward_eq_cycleRows _ column
    _ = _ := FiniteSum.Fin.sumFin_congr (fun position => congrArg (fun weight : Int => vget row.b position * weight)
      (chains.weights_eq position column).symm)

/-- The actual A chord-chain value equals the retained full handle-coordinate combination of cached cycle values. -/
theorem a_chain_value (chains : Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleWords.CutBank.HandleChains cut)
  (row : CutBank.HandleRow cut index)
    (value : Stokes.OrientedEdge lifted.vertices.count → Data.Gaussian.Basic.Canonical) :
    CutCycleChain.edgeValue (chains.chords.rows.get index).aPhysical.chain value =
      WordCoordinates.combine (vget row.a) (chains.cycleValues value) := by
  change WordCoordinates.combine (cut.rows.get index).a.span.coefficients (chains.chordValues value) = _
  calc
    _ = WordCoordinates.combine (fun column => sumFin (fun position => vget row.a position * vget (vget chains.weights
      position) column))
        (chains.chordValues value) := by
      apply FiniteSum.Fin.sumFin_congr
      intro column
      rw [chains.a_coefficients row column]
    _ = _ := Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleWords.combine_rows (vget row.a) (fun position =>
      vget (vget chains.weights position)) (chains.chordValues value)

/-- The actual B chord-chain value equals the retained full handle-coordinate combination of cached cycle values. -/
theorem b_chain_value (chains : Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleWords.CutBank.HandleChains cut)
  (row : CutBank.HandleRow cut index)
    (value : Stokes.OrientedEdge lifted.vertices.count → Data.Gaussian.Basic.Canonical) :
    CutCycleChain.edgeValue (chains.chords.rows.get index).bPhysical.chain value =
      WordCoordinates.combine (vget row.b) (chains.cycleValues value) := by
  change WordCoordinates.combine (cut.rows.get index).b.span.coefficients (chains.chordValues value) = _
  calc
    _ = WordCoordinates.combine (fun column => sumFin (fun position => vget row.b position * vget (vget chains.weights
      position) column))
        (chains.chordValues value) := by
      apply FiniteSum.Fin.sumFin_congr
      intro column
      rw [chains.b_coefficients row column]
    _ = _ := Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleWords.combine_rows (vget row.b) (fun position =>
      vget (vget chains.weights position)) (chains.chordValues value)

/-- The actual A word valuation is its full retained handle combination plus original physical-boundary and face
corrections. -/
theorem a_word_value (chains : Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleWords.CutBank.HandleChains cut)
  (row : CutBank.HandleRow cut index)
    (value : Stokes.OrientedEdge lifted.vertices.count → Data.Gaussian.Basic.Canonical) (anti : ∀ edge, value
      edge.reverse = -value edge) :
    SewingRetraction.wordValue value (prepared.aWord index) =
      WordCoordinates.combine (vget row.a) (chains.cycleValues value) +
        WordCoordinates.combine (chains.chords.rows.get index).aPhysical.physical
          (fun column => value (OrientedEdge.map lifted.cutPolygon.patch.cut.vertexLabels
            (lifted.cutBoundaryWord.alphabet.generators column))) +
        SewingRetraction.faceValue lifted.mesh.triangulation.faces value (cut.rows.get index).a.route.correction := by
  rw [(chains.chords.rows.get index).a_value value anti, chains.a_chain_value row value]

/-- The actual B word valuation is its full retained handle combination plus original physical-boundary and face
corrections. -/
theorem b_word_value (chains : Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleWords.CutBank.HandleChains cut)
  (row : CutBank.HandleRow cut index)
    (value : Stokes.OrientedEdge lifted.vertices.count → Data.Gaussian.Basic.Canonical) (anti : ∀ edge, value
      edge.reverse = -value edge) :
    SewingRetraction.wordValue value (prepared.bWord index) =
      WordCoordinates.combine (vget row.b) (chains.cycleValues value) +
        WordCoordinates.combine (chains.chords.rows.get index).bPhysical.physical
          (fun column => value (OrientedEdge.map lifted.cutPolygon.patch.cut.vertexLabels
            (lifted.cutBoundaryWord.alphabet.generators column))) +
        SewingRetraction.faceValue lifted.mesh.triangulation.faces value (cut.rows.get index).b.route.correction := by
  rw [(chains.chords.rows.get index).b_value value anti, chains.b_chain_value row value]

end HandleChains
end CutBank
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleWords

end
