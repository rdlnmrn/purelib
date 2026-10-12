module
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Vector.Basic
import Purelib.LinearAlgebra.Alternating.Handle.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleCoordinates
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleWords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Boundary.BoundaryCoordinates
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Topology.Surface.Sewing.VertexSewing
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleRadicalValues
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryWord
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Surface.Chord.Spanning
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Surface.Word.NormalForm
import Purelib.Topology.Surface.Word.PairedWord

open Purelib.Algebra

open Purelib.Curves

open Purelib.Data

open Purelib.LinearAlgebra.Alternating

open Purelib.Riemann

open Purelib

@[expose] public section

/-! Separate the actual ordered words into handle, physical, and face contributions. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleWords.CutBank.HandleChains

open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian

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

/-- Evaluate only coordinates belonging to the retained handle pivots. -/
def handleValue (weights : Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleCoordinates.CutBank.HandleVector cut) (value
  : Topology.Polygon.Stokes.OrientedEdge lifted.vertices.count → Gaussian.Basic.Canonical) : Gaussian :=
  FiniteSum.Fin.sumFin fun index => if index ∈ Handle.Basic.handleIndices cut.normal.pivots then
    ((vget weights index : Int) : Gaussian.Basic.Canonical) * chains.cycleValues value index else 0

/-- Keep every unused cycle contribution until its physical readback has been applied. -/
def radicalValue (weights : Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleCoordinates.CutBank.HandleVector cut) (value
  : Topology.Polygon.Stokes.OrientedEdge lifted.vertices.count → Gaussian.Basic.Canonical) : Gaussian :=
  FiniteSum.Fin.sumFin fun index => if index ∈ Handle.Basic.handleIndices cut.normal.pivots then 0 else
    ((vget weights index : Int) : Gaussian.Basic.Canonical) * chains.cycleValues value index

/-- The original normal-form cycle reading is the sum of its retained handle and radical contributions. -/
theorem value_split (weights : Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleCoordinates.CutBank.HandleVector cut)
  (value : Topology.Polygon.Stokes.OrientedEdge lifted.vertices.count → Gaussian.Basic.Canonical) :
    Topology.Surface.Boundary.BoundaryCoordinates.WordCoordinates.combine (vget weights) (chains.cycleValues value) =
      chains.handleValue weights value + chains.radicalValue weights value := by
  unfold Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleWords.CutBank.HandleChains.handleValue
    Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleWords.CutBank.HandleChains.radicalValue
  rw [← FiniteSum.Fin.sumFin_add]
  apply FiniteSum.Fin.sumFin_congr
  intro index
  by_cases used : index ∈ Handle.Basic.handleIndices cut.normal.pivots
  · rw [if_pos used, if_pos used, add_zero]
  · rw [if_neg used, if_neg used, zero_add]

/-- This is a physical-boundary sum, not a claimed zero period. -/
theorem radicalValue_physical (weights :
  Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleCoordinates.CutBank.HandleVector cut)
    (value : Topology.Polygon.Stokes.OrientedEdge lifted.vertices.count → Gaussian.Basic.Canonical) (anti : ∀ edge,
      value edge.reverse = -value edge) :
    chains.radicalValue weights value = FiniteSum.Fin.sumFin (fun index =>
      if index ∈ Handle.Basic.handleIndices cut.normal.pivots then 0 else
        ((vget weights index : Int) : Gaussian.Basic.Canonical) *
          Topology.Surface.Boundary.BoundaryCoordinates.WordCoordinates.combine (vget (chains.physicalCycleRow index))
          (fun column => value (Topology.Surface.Sewing.VertexSewing.OrientedEdge.map
            lifted.cutPolygon.patch.cut.vertexLabels (lifted.cutBoundaryWord.alphabet.generators column)))) := by
  apply FiniteSum.Fin.sumFin_congr
  intro index
  by_cases used : index ∈ Handle.Basic.handleIndices cut.normal.pivots
  · rw [if_pos used, if_pos used]
  · rw [if_neg used, if_neg used, chains.unused_cycleValues index used value anti]

/-- Combine the old physical remainder with the explicitly retained unused-cycle values. -/
def aPhysicalValue {index : Fin genus} (row :
  Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleCoordinates.CutBank.HandleRow cut index)
    (value : Topology.Polygon.Stokes.OrientedEdge lifted.vertices.count → Gaussian.Basic.Canonical) : Gaussian :=
  chains.radicalValue row.a value +
    Topology.Surface.Boundary.BoundaryCoordinates.WordCoordinates.combine (chains.chords.rows.get
      index).aPhysical.physical
      (fun column => value (Topology.Surface.Sewing.VertexSewing.OrientedEdge.map
        lifted.cutPolygon.patch.cut.vertexLabels (lifted.cutBoundaryWord.alphabet.generators column)))

/-- The b-cycle physical reading combines its original radical row with the retained physical boundary correction. -/
def bPhysicalValue {index : Fin genus} (row :
  Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleCoordinates.CutBank.HandleRow cut index)
    (value : Topology.Polygon.Stokes.OrientedEdge lifted.vertices.count → Gaussian.Basic.Canonical) : Gaussian :=
  chains.radicalValue row.b value +
    Topology.Surface.Boundary.BoundaryCoordinates.WordCoordinates.combine (chains.chords.rows.get
      index).bPhysical.physical
      (fun column => value (Topology.Surface.Sewing.VertexSewing.OrientedEdge.map
        lifted.cutPolygon.patch.cut.vertexLabels (lifted.cutBoundaryWord.alphabet.generators column)))

/-- The a-cycle word reading equals its handle reading, original physical correction and retained face-boundary
correction. -/
theorem a_word_handle_value {index : Fin genus} (row :
  Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleCoordinates.CutBank.HandleRow cut index)
    (value : Topology.Polygon.Stokes.OrientedEdge lifted.vertices.count → Gaussian.Basic.Canonical) (anti : ∀ edge,
      value edge.reverse = -value edge) :
    Topology.Surface.Sewing.SewingRetraction.wordValue value (prepared.aWord index) =
      chains.handleValue row.a value + chains.aPhysicalValue row value +
        Topology.Surface.Sewing.SewingRetraction.faceValue lifted.mesh.triangulation.faces value (cut.rows.get
          index).a.route.correction := by
  rw [chains.a_word_value row value anti, chains.value_split row.a value]
  exact congrArg (· + Topology.Surface.Sewing.SewingRetraction.faceValue lifted.mesh.triangulation.faces value
    (cut.rows.get index).a.route.correction)
    (add_assoc _ _ _)

/-- The b-cycle word reading equals its handle reading, original physical correction and retained face-boundary
correction. -/
theorem b_word_handle_value {index : Fin genus} (row :
  Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleCoordinates.CutBank.HandleRow cut index)
    (value : Topology.Polygon.Stokes.OrientedEdge lifted.vertices.count → Gaussian.Basic.Canonical) (anti : ∀ edge,
      value edge.reverse = -value edge) :
    Topology.Surface.Sewing.SewingRetraction.wordValue value (prepared.bWord index) =
      chains.handleValue row.b value + chains.bPhysicalValue row value +
        Topology.Surface.Sewing.SewingRetraction.faceValue lifted.mesh.triangulation.faces value (cut.rows.get
          index).b.route.correction := by
  rw [chains.b_word_value row value anti, chains.value_split row.b value]
  exact congrArg (· + Topology.Surface.Sewing.SewingRetraction.faceValue lifted.mesh.triangulation.faces value
    (cut.rows.get index).b.route.correction)
    (add_assoc _ _ _)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleWords.CutBank.HandleChains
