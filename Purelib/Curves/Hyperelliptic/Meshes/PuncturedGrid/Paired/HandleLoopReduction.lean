module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
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
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PhysicalCycles
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Topology.Surface.Sewing.VertexSewing
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleUnusedLoops
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleWordReduction
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryComponents
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryWord
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedBoundaryLoops
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Surface.Boundary.BoundaryCoordinates
import Purelib.Topology.Surface.Chord.Spanning
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.PhysicalCycleCoordinates
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Surface.Sewing.SimpleBoundaryCycles
import Purelib.Topology.Surface.Word.NormalForm
import Purelib.Topology.Surface.Word.PairedWord
import Purelib.Topology.Surface.Word.ProjectedEdgePairs

open Purelib.Algebra

open Purelib.Curves

open Purelib.Data

open Purelib

open Purelib.LinearAlgebra.Alternating

open Purelib.Riemann

@[expose] public section

/-! Cache all physical-loop corrections of the actual ordered handle reconstruction. -/
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

set_option genInjectivity false in
/-- One boundary cache serves the original chord remainders and every unused normal coordinate. -/
structure LoopReduction where
  /-- The shared original chord-loop boundary decomposition. -/ original :
    Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates.CutBank.OnChords.Loops chains.chords
  /-- The retained handle membership or physical-loop remainder of every original coordinate. -/ remainders :
    Data.Vector.DependentVector (fun index : Fin lifted.cutBoundaryWord.alphabet.count =>
    Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleWords.CutBank.HandleChains.CycleRemainder chains original.boundary
      index)

constructive_injectivity LoopReduction

namespace LoopReduction

/-- Cache one original boundary decomposition and the certified remainder of each original normal coordinate. -/
def build : Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleWords.CutBank.HandleChains.LoopReduction chains :=
  let original := Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates.CutBank.OnChords.loops chains.chords
  let matching := fun edge => (lifted.cut_boundary_iff_boundaryComponents edge :
    edge ∈ lifted.cutBoundaryPairs.boundary.map (Topology.Surface.Sewing.VertexSewing.OrientedEdge.map
      lifted.cutPolygon.patch.cut.vertexLabels) ↔
      edge ∈ original.boundary.cycles.flatten)
  ⟨original, Data.Vector.DependentVector.ofFn
    (Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleWords.CutBank.HandleChains.CycleRemainder.build chains
    original.boundary matching)⟩

variable {chains} (data :
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleWords.CutBank.HandleChains.LoopReduction chains)

/-- Evaluate retained whole loops; no physical-row decomposition is recomputed. -/
def radicalValue (weights : Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleCoordinates.CutBank.HandleVector cut) (value
  : Topology.Polygon.Stokes.OrientedEdge lifted.vertices.count → Gaussian.Basic.Canonical) : Gaussian :=
  FiniteSum.Fin.sumFin fun index => ((vget weights index : Int) : Gaussian.Basic.Canonical) * (data.remainders.get
    index).value value

/-- The retained whole-loop radical reading equals the original normal-form radical reading. -/
theorem radicalValue_eq (weights : Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleCoordinates.CutBank.HandleVector cut)
    (value : Topology.Polygon.Stokes.OrientedEdge lifted.vertices.count → Gaussian.Basic.Canonical) (anti : ∀ edge,
      value edge.reverse = -value edge) :
    data.radicalValue weights value = chains.radicalValue weights value := by
  apply FiniteSum.Fin.sumFin_congr
  intro index
  rw [(data.remainders.get index).value_eq value anti]
  by_cases used : index ∈ Handle.Basic.handleIndices cut.normal.pivots
  · rw [if_pos used, if_pos used, mul_zero]
  · rw [if_neg used, if_neg used]

/-- The original a-row physical correction read from the retained radical and boundary-loop caches. -/
def aPhysicalValue {index : Fin genus} (row :
  Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleCoordinates.CutBank.HandleRow cut index)
    (value : Topology.Polygon.Stokes.OrientedEdge lifted.vertices.count → Gaussian.Basic.Canonical) : Gaussian :=
  data.radicalValue row.a value + Data.Gaussian.Norm.Sum.Basic.gaussianSum
    ((data.original.rows.get index).a.rows.map (fun entry => (entry.1 : Gaussian.Basic.Canonical) *
      Topology.Surface.Sewing.SewingRetraction.wordValue value entry.2))

/-- The original b-row physical correction read from the retained radical and boundary-loop caches. -/
def bPhysicalValue {index : Fin genus} (row :
  Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleCoordinates.CutBank.HandleRow cut index)
    (value : Topology.Polygon.Stokes.OrientedEdge lifted.vertices.count → Gaussian.Basic.Canonical) : Gaussian :=
  data.radicalValue row.b value + Data.Gaussian.Norm.Sum.Basic.gaussianSum
    ((data.original.rows.get index).b.rows.map (fun entry => (entry.1 : Gaussian.Basic.Canonical) *
      Topology.Surface.Sewing.SewingRetraction.wordValue value entry.2))

/-- The cached loop reconstruction gives exactly the original a-row physical correction. -/
theorem aPhysicalValue_eq {index : Fin genus} (row :
  Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleCoordinates.CutBank.HandleRow cut index)
    (value : Topology.Polygon.Stokes.OrientedEdge lifted.vertices.count → Gaussian.Basic.Canonical) (anti : ∀ edge,
      value edge.reverse = -value edge) :
    data.aPhysicalValue row value = chains.aPhysicalValue row value :=
  congrArg₂ (· + ·) (data.radicalValue_eq row.a value anti) ((data.original.rows.get index).a.value_eq value).symm

/-- The cached loop reconstruction gives exactly the original b-row physical correction. -/
theorem bPhysicalValue_eq {index : Fin genus} (row :
  Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleCoordinates.CutBank.HandleRow cut index)
    (value : Topology.Polygon.Stokes.OrientedEdge lifted.vertices.count → Gaussian.Basic.Canonical) (anti : ∀ edge,
      value edge.reverse = -value edge) :
    data.bPhysicalValue row value = chains.bPhysicalValue row value :=
  congrArg₂ (· + ·) (data.radicalValue_eq row.b value anti) ((data.original.rows.get index).b.value_eq value).symm

/-- The actual A program is a handle sum plus cached physical loops and its original face correction. -/
theorem a_word_value {index : Fin genus} (row :
  Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleCoordinates.CutBank.HandleRow cut index)
    (value : Topology.Polygon.Stokes.OrientedEdge lifted.vertices.count → Gaussian.Basic.Canonical) (anti : ∀ edge,
      value edge.reverse = -value edge) :
    Topology.Surface.Sewing.SewingRetraction.wordValue value (prepared.aWord index) =
      chains.handleValue row.a value + data.aPhysicalValue row value +
        Topology.Surface.Sewing.SewingRetraction.faceValue lifted.mesh.triangulation.faces value (cut.rows.get
          index).a.route.correction := by
  rw [data.aPhysicalValue_eq row value anti]
  exact chains.a_word_handle_value row value anti

/-- The corrected B program retains its own cached physical loops and face correction. -/
theorem b_word_value {index : Fin genus} (row :
  Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleCoordinates.CutBank.HandleRow cut index)
    (value : Topology.Polygon.Stokes.OrientedEdge lifted.vertices.count → Gaussian.Basic.Canonical) (anti : ∀ edge,
      value edge.reverse = -value edge) :
    Topology.Surface.Sewing.SewingRetraction.wordValue value (prepared.bWord index) =
      chains.handleValue row.b value + data.bPhysicalValue row value +
        Topology.Surface.Sewing.SewingRetraction.faceValue lifted.mesh.triangulation.faces value (cut.rows.get
          index).b.route.correction := by
  rw [data.bPhysicalValue_eq row value anti]
  exact chains.b_word_handle_value row value anti

/-- Each unused coordinate retains exactly the original ordered physical boundary-loop list. -/
theorem unused_words_eq (index : Fin lifted.cutBoundaryWord.alphabet.count) :
    match data.remainders.get index with
    | .handle _ => True
    | .physical _ row => row.loops.rows.map Prod.snd = lifted.boundaryLoops := by
  cases data.remainders.get index with
  | handle => trivial
  | physical unused row => exact row.words_eq.trans data.original.canonical

end LoopReduction
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleWords.CutBank.HandleChains

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleWords.CutBank.HandleChains.LoopReduction

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleWords.CutBank.HandleChains.LoopReduction
