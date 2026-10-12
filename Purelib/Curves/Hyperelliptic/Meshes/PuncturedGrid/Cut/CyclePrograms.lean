module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period
import Purelib.Data.Vector.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Paths.PreparedPathPrimitiveCover
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.JumpPaths
import Purelib.Topology.Surface.Sewing.ChordCycleBank
import Purelib.Topology.Surface.Sewing.CutCycleChains
import Purelib.Topology.Surface.Sewing.VertexSewing
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.ChordJumps
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks
public import Purelib.RootIsolation.SquareRoot.Grid.Walk.Closure
public import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryWord
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.FromStates
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Paths.OwnerLoopMonodromy
import Purelib.Riemann.RootContinuation.PreparedGridRootClosure
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.Walk.Vertex
import Purelib.Topology.Chain.PathBoundary
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree

open Purelib

open Purelib.Curves.Hyperelliptic

open Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy

open Purelib.Riemann

open Purelib.Riemann.Paths.PreparedPathPrimitiveCover

open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels

open Purelib.Riemann.Periods

open Purelib.Riemann.Periods.PreparedGridPeriodPrograms

open Purelib.Topology.Polygon

open Purelib.Topology.Surface.Sewing

open Purelib.Topology.Surface.Sewing.VertexSewing

public section

/-!
# Root-safe period programs for the actual closed cut-mesh chains

Each original cut cycle retains its cut word, projected mesh word, selected
face detours and actual prepared period state. A vector materializes each
component once; integer rows of the normal form can share this bank.
The programs follow these routed cycles, not the old branch-tour basis.
Identifying their integrals with cut-primitive jumps remains separate.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period.Basis (CertifiedPeriodProgram)
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Topology.Surface.Sewing.CutCycleChains (ClosedCutCycle)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks (RoutedPath)
open Purelib.Topology.Surface.Cut.JumpPaths
open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Purelib.Riemann.Meshes.FramedPuncturedGrid curve branches higher}

set_option genInjectivity false in
/-- An actual closed cut cycle with its retained mesh routing and root-safe period preparation.

The original projected cut word, selected face detours and prepared period walk share an exact walk identity. -/
structure CutCycleProgram (lifted : Meshes.LiftedPuncturedGrid base) (source : Differentials.Basic.Differential genus)
  where
  /-- The original closed cut cycle with its retained occurrence-preserving surface word. -/ cycle :
    CutCycleChains.ClosedCutCycle lifted.cutPolygon.patch.cut.vertexLabels
    (lifted.cutPolygon.patch.cut.boundary.map (OrientedEdge.map lifted.cutPolygon.patch.cut.vertexLabels))
  /-- The retained root-safe mesh routing of this exact original cut cycle. -/ routed : MeshPathWalks.RoutedPath
    lifted.mesh cycle.path.surfaceEdges
    (lifted.cutPolygon.patch.cut.vertexLabels cycle.start) (lifted.cutPolygon.patch.cut.vertexLabels cycle.start)
  /-- The actual period walk prepared on the retained routed path and original starting owner. -/ period :
    PreparedGridPeriodPrograms.PeriodWalk base.bank.grid
    (lifted.vertices.coordinate (lifted.cutPolygon.patch.cut.vertexLabels cycle.start))
    (lifted.vertices.owner lifted.frames (lifted.cutPolygon.patch.cut.vertexLabels cycle.start)) source
  /-- The prepared period walk is exactly the retained routed grid walk. -/ walk_eq : period.closed.walk =
    routed.walk.walk

constructive_injectivity CutCycleProgram

namespace CutCycleProgram

variable {lifted : Purelib.Riemann.Meshes.LiftedPuncturedGrid base} {source :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}

/-- The generated-preparation entry point checks the actual routed path's trace and cover. It does not run or compare
against canonical subdivision. -/
@[expose] def ofCovered (cycle : CutCycleChains.ClosedCutCycle lifted.cutPolygon.patch.cut.vertexLabels
    (lifted.cutPolygon.patch.cut.boundary.map (OrientedEdge.map lifted.cutPolygon.patch.cut.vertexLabels)))
    (routed : MeshPathWalks.RoutedPath lifted.mesh cycle.path.surfaceEdges
      (lifted.cutPolygon.patch.cut.vertexLabels cycle.start) (lifted.cutPolygon.patch.cut.vertexLabels cycle.start))
    (covered : PreparedClearPathModels.CoveredTracedPath routed.walk.walk.path
      (lifted.vertices.owner lifted.frames (lifted.cutPolygon.patch.cut.vertexLabels cycle.start)))
    (source : Differentials.Basic.Differential genus) :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms.CutCycleProgram lifted source :=
  let reference := (BranchCellBank.referenceAt base.bank.toBranchCellBank _
    (lifted.vertices.coordinate_onGrid _)).toLoop
  let closed := routed.walk.rootClosedOfCovered reference covered
  ⟨cycle, routed, PeriodWalk.ofClosed closed source, rfl⟩

/-- Route the original supported cut cycle and retain one root-safe preparation for its actual resulting walk. -/
@[expose] def build (lifted : Meshes.LiftedPuncturedGrid base)
    (cycle : CutCycleChains.ClosedCutCycle lifted.cutPolygon.patch.cut.vertexLabels
      (lifted.cutPolygon.patch.cut.boundary.map (OrientedEdge.map lifted.cutPolygon.patch.cut.vertexLabels)))
    (source : Differentials.Basic.Differential genus) :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms.CutCycleProgram lifted source :=
  let routed := MeshPathWalks.routePath lifted.mesh cycle.path.surfaceEdges cycle.closed (lifted.cutCycle_supported
    cycle)
  let covered := CoveredTracedPath.build routed.walk.walk.path routed.walk.walk.withinAmbient
    (lifted.vertices.owner lifted.frames (lifted.cutPolygon.patch.cut.vertexLabels cycle.start))
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms.CutCycleProgram.ofCovered cycle routed covered source

/-- The constructed period preparation retains exactly the supplied original closed cut cycle. -/
theorem build_cycle (lifted : Meshes.LiftedPuncturedGrid base)
    (cycle : CutCycleChains.ClosedCutCycle lifted.cutPolygon.patch.cut.vertexLabels
      (lifted.cutPolygon.patch.cut.boundary.map (OrientedEdge.map lifted.cutPolygon.patch.cut.vertexLabels)))
    (source : Differentials.Basic.Differential genus) :
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms.CutCycleProgram.build lifted cycle source).cycle =
      cycle := rfl

/-- Read the certified standard-differential period program from the retained original cut-cycle preparation. -/
@[expose] def program (prepared : Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms.CutCycleProgram lifted
  source) (differential : Fin genus) :
    Basis.CertifiedPeriodProgram curve (PeriodMatrix.standardDifferential differential) prepared.period.cycle :=
  prepared.period.program differential

/-- The original retained cut cycle is supported on the actual lifted triangle mesh. -/
theorem original_supported (prepared : Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms.CutCycleProgram
  lifted source) :
    CutPath.Supported (Stokes.triangleEdgeOccurrences lifted.mesh.triangulation.faces) prepared.cycle.path.surfaceEdges
      :=
  lifted.cutCycle_supported prepared.cycle

/-- The retained face-detour realization of the original cycle is supported on the same lifted triangle mesh. -/
theorem routed_supported (prepared : Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms.CutCycleProgram lifted
  source) :
    CutPath.Supported (Stokes.triangleEdgeOccurrences lifted.mesh.triangulation.faces) prepared.routed.walk.indexed :=
      by
  rw [prepared.routed.indexed_eq]
  exact prepared.routed.spine.detour_supported

end CutCycleProgram

set_option genInjectivity false in
/-- The bank is independent of integer row weights. All transformed handle chains can reuse its preparations instead of
preparing every row afresh. -/
structure CutCycleProgramBank (lifted : Meshes.LiftedPuncturedGrid base) (source : Differentials.Basic.Differential
  genus) {count : Nat}
    (cycles : Data.Vector
      (CutCycleChains.ClosedCutCycle lifted.cutPolygon.patch.cut.vertexLabels
        (lifted.cutPolygon.patch.cut.boundary.map (OrientedEdge.map lifted.cutPolygon.patch.cut.vertexLabels))) count)
          where
  /-- The cached original cycle preparations indexed by the supplied cycle vector. -/ programs :
    Data.Vector (Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms.CutCycleProgram lifted source)
    count
  /-- Each cached program retains exactly its original indexed cycle. -/ cycles_eq : ∀ index, (programs index).cycle =
    cycles index

constructive_injectivity CutCycleProgramBank

namespace CutCycleProgramBank

/-- Materialize one original cut-cycle preparation per retained vector entry, preserving exact cycle identity. -/
@[expose] def build (lifted : Meshes.LiftedPuncturedGrid base) (source : Differentials.Basic.Differential genus) {count
  : Nat}
    (cycles : Data.Vector
      (CutCycleChains.ClosedCutCycle lifted.cutPolygon.patch.cut.vertexLabels
        (lifted.cutPolygon.patch.cut.boundary.map (OrientedEdge.map lifted.cutPolygon.patch.cut.vertexLabels))) count) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms.CutCycleProgramBank lifted source cycles :=
  ⟨vectorOfFn (fun index => Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms.CutCycleProgram.build lifted
    (cycles index) source),
    fun index => by rw [Data.Vector.Basic.vectorOfFn_apply,
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms.CutCycleProgram.build_cycle]⟩

end CutCycleProgramBank

set_option genInjectivity false in
/-- One fixed topological bank and its actual root-safe component programs. No dummy primitive sample is needed to start
period preparation. -/
structure CutChordPrograms (lifted : Meshes.LiftedPuncturedGrid base) (source : Differentials.Basic.Differential genus)
  where
  /-- The retained topological chord-cycle bank of the actual original cut boundary word. -/ routes :
    Topology.Surface.Sewing.ChordCycleBank lifted.cutBoundaryWord
  /-- The cached component programs for these exact retained chord cycles. -/ programs :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms.CutCycleProgramBank lifted source routes.cycles

constructive_injectivity CutChordPrograms

namespace CutChordPrograms

/-- Retain the original cut-boundary chord bank and its shared root-safe component programs. -/
@[expose] def build (lifted : Meshes.LiftedPuncturedGrid base) (source : Differentials.Basic.Differential genus) :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms.CutChordPrograms lifted source :=
  let routes := lifted.cutChordCycleBank
  ⟨routes, Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms.CutCycleProgramBank.build lifted source
    routes.cycles⟩

end CutChordPrograms
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms
