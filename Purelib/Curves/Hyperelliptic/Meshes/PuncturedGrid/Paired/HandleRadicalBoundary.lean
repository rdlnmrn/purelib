module
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Vector.Basic
import Purelib.LinearAlgebra.Alternating.Handle.Basic
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Chain.PathBoundary

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleWords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Topology.Surface.Chord.PhysicalBoundary
import Purelib.Topology.Surface.Chord.Spanning
import Purelib.Topology.Surface.Sewing.VertexSewing
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleRadicalValues
import Mathlib.Algebra.Ring.Int.Defs
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryWord
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Surface.Word.NormalForm
import Purelib.Topology.Surface.Word.PairedWord

open Purelib.Algebra

open Purelib.Curves

open Purelib.LinearAlgebra.Alternating

open Purelib.Riemann

open Purelib

@[expose] public section

/-! The physical remainder of every unused normal-form chord cycle is closed. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleWords.CutBank.HandleChains

local notation "vget" => Data.Vector.get

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {bank :
    Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted} {sheet : Fin 2}
  {ordered : Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered bank sheet}
    {paired : Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered.Paired ordered} {prepared :
    Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired}

variable {cut : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates.CutBank prepared} (chains :
  Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleWords.CutBank.HandleChains cut)

/-- Every unused normal-form row defines a closed chain on the original physical grid vertices. -/
theorem unused_physicalCycleRow_closed (index : Fin lifted.cutBoundaryWord.alphabet.count)
    (unused : index ∉ Handle.Basic.handleIndices cut.normal.pivots) (vertex : Fin lifted.vertices.count) :
    FiniteSum.Fin.sumFin (fun column => vget (chains.physicalCycleRow index) column *
      Topology.Chain.PathBoundary.edgeBoundaryAt Topology.Polygon.Stokes.OrientedEdge.start
        Topology.Polygon.Stokes.OrientedEdge.finish
        (Topology.Surface.Sewing.VertexSewing.OrientedEdge.map lifted.cutPolygon.patch.cut.vertexLabels
          (lifted.cutBoundaryWord.alphabet.generators column)) vertex) = 0 := by
  let boundary := fun column => Topology.Chain.PathBoundary.edgeBoundaryAt Topology.Polygon.Stokes.OrientedEdge.start
    Topology.Polygon.Stokes.OrientedEdge.finish
    (Topology.Surface.Sewing.VertexSewing.OrientedEdge.map lifted.cutPolygon.patch.cut.vertexLabels
      (lifted.cutBoundaryWord.alphabet.generators column)) vertex
  have row (column : Fin lifted.cutBoundaryWord.alphabet.count) :
      vget (chains.physicalCycleRow index) column = FiniteSum.Fin.sumFin (fun position =>
        vget (vget chains.weights index) position *
          (cut.integral.paired position column +
            (Topology.Surface.Chord.Spanning.CutBoundaryWord.ChordCoordinate.physicalRow
            (chains.chords.chords.coordinates position)) column)) := by
    calc
      _ = FiniteSum.Fin.sumFin (fun position => vget (vget chains.weights index) position * cut.integral.paired position
        column) +
          FiniteSum.Fin.sumFin (fun position => vget (vget chains.weights index) position *
            (Topology.Surface.Chord.Spanning.CutBoundaryWord.ChordCoordinate.physicalRow
            (chains.chords.chords.coordinates position)) column) := by
        rw [chains.unused_paired_row index unused column, zero_add, chains.physicalCycleRow_apply]
      _ = _ := (FiniteSum.Fin.sumFin_add _ _).symm.trans (FiniteSum.Fin.sumFin_congr (fun position => (mul_add _ _
        _).symm))
  calc
    _ = FiniteSum.Fin.sumFin (fun column => FiniteSum.Fin.sumFin (fun position =>
        vget (vget chains.weights index) position *
          (cut.integral.paired position column +
            (Topology.Surface.Chord.Spanning.CutBoundaryWord.ChordCoordinate.physicalRow
            (chains.chords.chords.coordinates position)) column) * boundary column)) := by
      apply FiniteSum.Fin.sumFin_congr
      intro column
      rw [row, FiniteSum.Fin.sumFin_mul_right]
    _ = FiniteSum.Fin.sumFin (fun position => vget (vget chains.weights index) position * FiniteSum.Fin.sumFin (fun
      column =>
        (cut.integral.paired position column +
          (Topology.Surface.Chord.Spanning.CutBoundaryWord.ChordCoordinate.physicalRow (chains.chords.chords.coordinates
          position)) column) * boundary column)) := by
      rw [FiniteSum.Fin.sumFin_swap]
      apply FiniteSum.Fin.sumFin_congr
      intro position
      exact (FiniteSum.Fin.sumFin_congr (fun column => _root_.mul_assoc _ _ _)).trans (FiniteSum.Fin.sumFin_mul_left _
        _)
    _ = 0 := by
      apply (FiniteSum.Fin.sumFin_congr ?_).trans FiniteSum.Fin.sumFin_zero
      intro position
      have closed := Topology.Surface.Chord.PhysicalBoundary.ChordCycleBank.boundary_zero chains.chords.chords
        cut.integral lifted.cutPolygon.patch.cut.closed position vertex
      exact (congrArg (vget (vget chains.weights index) position * ·) closed).trans (mul_zero _)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleWords.CutBank.HandleChains
