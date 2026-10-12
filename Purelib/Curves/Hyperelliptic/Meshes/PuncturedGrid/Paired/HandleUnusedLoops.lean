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
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Boundary.BoundaryCoordinates
import Purelib.Topology.Surface.Cut.BoundaryPairs
public import Purelib.Topology.Surface.Sewing.CutPhysicalCycles
import Purelib.Topology.Surface.Sewing.PhysicalCycleCoordinates
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Topology.Surface.Sewing.SimpleBoundaryCycles
import Purelib.Topology.Surface.Sewing.VertexSewing
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleRadicalBoundary
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PhysicalCycles
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryWord
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleRadicalValues
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
import Purelib.Topology.Surface.Word.ProjectedEdgePairs

open Purelib.Curves

open Purelib.Data

open Purelib.LinearAlgebra.Alternating

open Purelib.Riemann

open Purelib

@[expose] public section

/-! Cache whole boundary-loop multiples for the unused normal-form cycles. -/
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

variable (boundary : Topology.Surface.Sewing.SimpleBoundaryCycles.PolygonStokes.BoundaryCycleDecomposition
  (Topology.Polygon.Stokes.triangleEdgeOccurrences lifted.mesh.triangulation.faces))

set_option genInjectivity false in
/-- The computed physical row and its whole-loop decomposition share one boundary owner. -/
structure UnusedLoopRow (index : Fin lifted.cutBoundaryWord.alphabet.count) where
  /-- The cached original physical cycle row. -/ physical :
    Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleCoordinates.CutBank.HandleVector cut
  /-- The cached row is exactly the original handle chain's physical cycle row. -/ physical_eq : physical =
    chains.physicalCycleRow index
  /-- The whole-loop decomposition on the same retained boundary owner and original mapped generators. -/ loops :
    Topology.Surface.Sewing.PhysicalCycleCoordinates.Data boundary
    (fun column => Topology.Surface.Sewing.VertexSewing.OrientedEdge.map lifted.cutPolygon.patch.cut.vertexLabels
      (lifted.cutBoundaryWord.alphabet.generators column))
    (vget physical)

constructive_injectivity UnusedLoopRow

namespace UnusedLoopRow

/-- The original mapped cut-boundary edge list has no duplicate occurrences. -/
public theorem cut_unique :
    (lifted.cutPolygon.patch.cut.boundary.map (Topology.Surface.Sewing.VertexSewing.OrientedEdge.map
      lifted.cutPolygon.patch.cut.vertexLabels)).Nodup := by
  rw [lifted.cutPolygon.patch.cut.boundary_eq]
  exact Topology.Surface.Cut.BoundaryPairs.SewnPatch.boundary_unique lifted.cutPolygon.patch
    (Topology.Surface.Cut.BoundaryPairs.SewingForest.SinglePolygon.originalEdges_unique lifted.cutPolygon
    lifted.mesh.orientedEdges_unique)

/-- Decompose the actual unused physical cycle row into whole original boundary loops on the same certified boundary
owner. -/
def build (matching : ∀ edge, edge ∈ lifted.cutBoundaryPairs.boundary.map
  (Topology.Surface.Sewing.VertexSewing.OrientedEdge.map lifted.cutPolygon.patch.cut.vertexLabels) ↔
    edge ∈ boundary.cycles.flatten) (index : Fin lifted.cutBoundaryWord.alphabet.count)
    (unused : index ∉ Handle.Basic.handleIndices cut.normal.pivots) :
      Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleWords.CutBank.HandleChains.UnusedLoopRow chains boundary index :=
  let physical := chains.physicalCycleRow index
  ⟨physical, rfl, Topology.Surface.Sewing.CutPhysicalCycles.ProjectedEdgePairing.physicalCycles lifted.cutBoundaryPairs
    Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleWords.CutBank.HandleChains.UnusedLoopRow.cut_unique boundary
    matching (vget physical)
    (chains.physicalCycleRow_paired_zero index) (chains.unused_physicalCycleRow_closed index unused)⟩

variable {chains boundary} {index : Fin lifted.cutBoundaryWord.alphabet.count}
  (data : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleWords.CutBank.HandleChains.UnusedLoopRow chains
    boundary index)

/-- The retained loop words equal the original ordered boundary cycle list. -/
theorem words_eq : data.loops.rows.map Prod.snd = boundary.cycles := data.loops.words_eq

/-- For antisymmetric edge readings, the unused original cycle value equals the retained weighted whole-loop sum. -/
theorem value_eq (unused : index ∉ Handle.Basic.handleIndices cut.normal.pivots)
    (value : Topology.Polygon.Stokes.OrientedEdge lifted.vertices.count → Gaussian.Basic.Canonical) (anti : ∀ edge,
      value edge.reverse = -value edge) :
    chains.cycleValues value index = Data.Gaussian.Norm.Sum.Basic.gaussianSum
      (data.loops.rows.map (fun entry => (entry.1 : Gaussian.Basic.Canonical) *
        Topology.Surface.Sewing.SewingRetraction.wordValue value entry.2)) := by
  have physical : Topology.Surface.Boundary.BoundaryCoordinates.WordCoordinates.combine (vget (chains.physicalCycleRow
    index))
      (fun column => value (Topology.Surface.Sewing.VertexSewing.OrientedEdge.map
        lifted.cutPolygon.patch.cut.vertexLabels (lifted.cutBoundaryWord.alphabet.generators column))) =
      Topology.Surface.Boundary.BoundaryCoordinates.WordCoordinates.combine (vget data.physical)
      (fun column => value (Topology.Surface.Sewing.VertexSewing.OrientedEdge.map
        lifted.cutPolygon.patch.cut.vertexLabels (lifted.cutBoundaryWord.alphabet.generators column))) := by
    rw [data.physical_eq]
  exact (chains.unused_cycleValues index unused value anti).trans (physical.trans (data.loops.value_eq value))

end UnusedLoopRow

set_option genInjectivity false in
/-- Used coordinates keep their membership; unused coordinates retain certified physical loops. -/
inductive CycleRemainder (index : Fin lifted.cutBoundaryWord.alphabet.count) where
  /-- The original coordinate is retained as a certified handle index. -/ | handle (used : index ∈
    Handle.Basic.handleIndices cut.normal.pivots)
  /-- The original unused coordinate retains its certified whole-boundary-loop decomposition. -/ | physical (unused :
    index ∉ Handle.Basic.handleIndices cut.normal.pivots) (data :
    Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleWords.CutBank.HandleChains.UnusedLoopRow chains boundary index)

constructive_injectivity CycleRemainder

namespace CycleRemainder

/-- Decide whether the original coordinate is a handle coordinate; otherwise retain its certified physical-loop
decomposition. -/
def build (matching : ∀ edge, edge ∈ lifted.cutBoundaryPairs.boundary.map
  (Topology.Surface.Sewing.VertexSewing.OrientedEdge.map lifted.cutPolygon.patch.cut.vertexLabels) ↔
    edge ∈ boundary.cycles.flatten) (index : Fin lifted.cutBoundaryWord.alphabet.count) :
      Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleWords.CutBank.HandleChains.CycleRemainder chains boundary index :=
  if used : index ∈ Handle.Basic.handleIndices cut.normal.pivots then .handle used
  else .physical used (Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleWords.CutBank.HandleChains.UnusedLoopRow.build
    chains boundary matching index used)

variable {chains boundary} {index : Fin lifted.cutBoundaryWord.alphabet.count}

/-- Read zero on a retained handle coordinate and the original weighted physical loops on an unused coordinate. -/
def value (data : Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleWords.CutBank.HandleChains.CycleRemainder chains
  boundary index) (reading : Topology.Polygon.Stokes.OrientedEdge lifted.vertices.count → Gaussian.Basic.Canonical) :
  Gaussian :=
  match data with
  | .handle _ => 0
  | .physical _ row => Data.Gaussian.Norm.Sum.Basic.gaussianSum
      (row.loops.rows.map (fun entry => (entry.1 : Gaussian.Basic.Canonical) *
        Topology.Surface.Sewing.SewingRetraction.wordValue reading entry.2))

/-- The retained remainder reads zero precisely on handle indices and otherwise the original cycle value. -/
theorem value_eq (data : Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleWords.CutBank.HandleChains.CycleRemainder
  chains boundary index)
    (reading : Topology.Polygon.Stokes.OrientedEdge lifted.vertices.count → Gaussian.Basic.Canonical) (anti : ∀ edge,
      reading edge.reverse = -reading edge) :
    data.value reading = if index ∈ Handle.Basic.handleIndices cut.normal.pivots then 0 else chains.cycleValues reading
      index := by
  cases data with
  | handle used => exact (if_pos used).symm
  | physical unused row =>
      rw [if_neg unused]
      exact (row.value_eq unused reading anti).symm

end CycleRemainder
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleWords.CutBank.HandleChains

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleWords.CutBank.HandleChains.CycleRemainder

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleWords.CutBank.HandleChains.CycleRemainder

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleWords.CutBank.HandleChains.UnusedLoopRow

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleWords.CutBank.HandleChains.UnusedLoopRow
