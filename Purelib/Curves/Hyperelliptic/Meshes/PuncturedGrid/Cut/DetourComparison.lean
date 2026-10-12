module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.FaceBanks
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodPrimitiveComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PeriodSegmentBanks
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Readings.PreparedPrimitiveChargeBounds
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.TriangleComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RetainedDetourValues
import Purelib.Approximation.Budget.PreparedPrimitiveBatchBudget
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.SynchronizedPrimitives
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RetainedDetourRoutes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleCornerSources
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Program.Gaussian.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Integration.PreparedRefinementProgramCore
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.Periods.PreparedPeriodPrimitiveRequests
import Purelib.Riemann.RootContinuation.PreparedGridRootClosure
import Purelib.Riemann.Topology.PreparedBankRootChains
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.JumpPaths
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.CutCycleChains
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Topology.Surface.Sewing.VertexSewing

open Purelib.Curves

open Purelib.Data

open Purelib.Riemann

@[expose] public section

/-!
# Actual period requests compared with their original routed triangle edges

The retained segment constructor keeps the original face on every side of
a diagonal detour. Its exact telescoping removes any caller-supplied detour
alignment or diagonal-integration premise. Identifying these source routes
with cut-boundary owners and bounding sewing errors remain separate steps.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.DetourComparison

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {source : Hyperelliptic.Differentials.Basic.Differential genus} {prepared :
    Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms.CutCycleProgram lifted source}
  {segments : Hyperelliptic.Meshes.PuncturedGrid.PeriodSegmentBanks.SegmentBank prepared.period} {differential : Fin
    genus}
  {comparison : Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodPrimitiveComparison.PrimitiveBank
    (Hyperelliptic.Meshes.PuncturedGrid.Cut.FaceBanks.FaceBank.ofSegments prepared segments) differential}
  {target : Readings.PreparedPrimitiveChargeBounds.Coordinate} {minimumStage : Nat}

/-- The original requested-period value equals the sum of its exact retained pre-detour route increments. -/
theorem value_eq_original_routes (result :
  Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodPrimitiveComparison.PrimitiveBank.RequestedPeriod comparison target
  minimumStage) :
    result.value = Data.Gaussian.Norm.Sum.Basic.gaussianSum (prepared.routed.spine.values (fun _ route =>
      result.locals.numerics.edgeIncrement route)) :=
  result.value_eq_corners.trans
    (Hyperelliptic.Meshes.PuncturedGrid.RetainedDetourValues.FaceBank.ofSegments_corner_sum prepared segments
      result.locals.numerics)

/-- This compares with the original mesh word, before diagonal detours,
using one shared triangle bank and the actual original period program. -/
theorem original_triangles_accurate (result :
  Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodPrimitiveComparison.PrimitiveBank.RequestedPeriod comparison target
  minimumStage)
    (readings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings result.locals.numerics
      lifted.mesh) :
    Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum (prepared.routed.spine.values (fun _
      route => route.sourceEdge.increment readings.values)) -
      ((prepared.program differential).integral.model result.sample.stage).integralSample) < target := by
  rw [Hyperelliptic.Meshes.PuncturedGrid.RetainedDetourValues.BranchCellBank.LiftedMesh.RouteSpine.triangle_values
    readings prepared.routed.spine, ← Hyperelliptic.Meshes.PuncturedGrid.Cut.DetourComparison.value_eq_original_routes
      result]
  exact result.program_accurate

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.DetourComparison
