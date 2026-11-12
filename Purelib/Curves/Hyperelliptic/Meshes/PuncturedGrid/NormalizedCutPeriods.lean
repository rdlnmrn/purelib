module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CornerRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.FaceBanks
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Readings.PreparedPrimitiveChargeBounds
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedNumerics
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodPrimitiveComparison
import Purelib.Approximation.Budget.PreparedPrimitiveBatchBudget
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.SynchronizedPrimitives
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PeriodSegmentBanks
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
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.Periods.PreparedPeriodPrimitiveRequests
import Purelib.Riemann.RootContinuation.PreparedGridRootClosure
import Purelib.Riemann.Topology.PreparedBankRootChains
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.CutCycleChains
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Surface.Sewing.VertexSewing

open Purelib.Curves

open Purelib.Data

open Purelib.Riemann

@[expose] public section

/-! The normalized shared face bank reads the actual cut-period programs. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedCutPeriods

open Purelib.Riemann.Readings.PreparedPrimitiveChargeBounds

variable {genus : Nat} {curve : Basic.HyperellipticCurve genus} {branches :
  Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {source : Differentials.Basic.Differential genus} {prepared :
    Cut.CyclePrograms.CutCycleProgram lifted source}

namespace PrimitiveBank.RequestedPeriod
variable {bank : Cut.FaceBanks.FaceBank prepared} {differential : Fin genus}
  {comparison : Cut.PeriodPrimitiveComparison.PrimitiveBank bank differential}
    {target : Coordinate} {minimumStage : Nat}

/-- The retained original requested-period value equals the sum of its exact normalized corner increments. -/
theorem value_eq_normalized_corners (result :
  Cut.PeriodPrimitiveComparison.PrimitiveBank.RequestedPeriod comparison target
  minimumStage) :
    result.value = Gaussian.Norm.Sum.Basic.gaussianSum
      (Cut.CornerRequests.AssignedSegments.cornerIncrements
      result.locals.numerics.normalize bank.assigned) := by
  rw [Cut.CornerRequests.AssignedSegments.cornerIncrements_normalize]
  exact result.value_eq_corners

/-- Normalizing the supplied cache preserves accuracy against the same original
root-safe program and the same retained period sample. -/
theorem normalized_corners_program_accurate (result :
  Cut.PeriodPrimitiveComparison.PrimitiveBank.RequestedPeriod comparison target
  minimumStage) :
    Gaussian.Norm.Basic.normSq (Gaussian.Norm.Sum.Basic.gaussianSum
      (Cut.CornerRequests.AssignedSegments.cornerIncrements
      result.locals.numerics.normalize bank.assigned) -
      ((prepared.program differential).integral.model result.sample.stage).integralSample) < target := by
  rw [←
    RequestedPeriod.value_eq_normalized_corners
    result]
  exact result.program_accurate

end PrimitiveBank.RequestedPeriod
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedCutPeriods
