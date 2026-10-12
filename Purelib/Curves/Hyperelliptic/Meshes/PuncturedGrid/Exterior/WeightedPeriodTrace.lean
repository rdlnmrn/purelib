module
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentConnection
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Connection
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Integration.Path.IncrementArea
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedRefinementProgramCore
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.PathArea
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.Periods.PreparedRootSafePeriodPrograms
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CommonScheduledTrace
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentJoins
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Integration.Budget.Trace.Family
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Program.Gaussian.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Integration.PreparedSwitchedRefinements
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.RootContinuation.PreparedGridRootClosure
import Purelib.Riemann.Topology.PreparedBankRootChains
import Purelib.Riemann.Topology.PreparedRootSafeCycleStates
import Purelib.Tactic.Ring
import Purelib.Data.List.Map

open Purelib.Algebra

open Purelib.Curves

open Purelib.Data

open Purelib.Geometry

open Purelib.Integration

open Purelib

open Purelib.Riemann

@[expose] public section

/-! Exact period-program ownership of the weighted exterior child path. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.WeightedPeriodTrace.ExteriorProgram

open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian)

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential : Hyperelliptic.Differentials.Basic.Differential genus}

/-- These are the original program's actual child integrals, in their
retained order, combined using one coefficient vector. -/
def weightedPeriodPath (program : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.ExteriorProgram lifted
  differential)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) (stage : Nat) : List Gaussian :=
  (program.period.initial.states (Integration.PreparedRefinementProgramCore.standardDifferentials genus)
    stage).state.parents.map (fun child =>
    FiniteSum.Fin.sumFin (fun row => coefficients row *
      (Integration.PreparedEdgeRecasting.recastCenteredEdge (Periods.PeriodMatrix.standardDifferential row)
        child).model.integralSample))

/-- Interchange a finite Gaussian list sum and its coefficient-weighted basis sum.

The original list order and coefficient vector remain fixed on both sides. -/
private theorem sum_weighted {Item : Type u} (items : List Item) (values : Item → Fin genus →
  Normalization.InverseRootPolynomial.Gaussian)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (items.map (fun item => FiniteSum.Fin.sumFin (fun row => coefficients row *
      values item row))) =
      FiniteSum.Fin.sumFin (fun row => coefficients row * Data.Gaussian.Norm.Sum.Basic.gaussianSum (items.map (fun item
        => values item row))) := by
  induction items with
  | nil =>
      change (0 : Normalization.InverseRootPolynomial.Gaussian) = FiniteSum.Fin.sumFin (fun row => coefficients row * 0)
      exact (FiniteSum.Fin.sumFin_congr (fun row => Gaussian.Basic.mul_zero (coefficients row))).trans
        FiniteSum.Fin.sumFin_zero |>.symm
  | cons head tail ih =>
      change FiniteSum.Fin.sumFin (fun row => coefficients row * values head row) + _ =
        FiniteSum.Fin.sumFin (fun row => coefficients row * (values head row + Data.Gaussian.Norm.Sum.Basic.gaussianSum
          (tail.map (fun item => values item row))))
      rw [ih, ← FiniteSum.Fin.sumFin_add]
      exact FiniteSum.Fin.sumFin_congr (fun row => by ring1)

/-- Read back the total through the certified program's model, including
its switched/root-safe cells rather than assuming those models are equal. -/
theorem weightedPeriodPath_total (program : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.ExteriorProgram
  lifted differential)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) (stage : Nat) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.WeightedPeriodTrace.ExteriorProgram.weightedPeriodPath program
      coefficients stage) =
      FiniteSum.Fin.sumFin (fun row => coefficients row * ((program.period.program row).integral.model
        stage).integralSample) := by
  rw [Hyperelliptic.Meshes.PuncturedGrid.Exterior.WeightedPeriodTrace.ExteriorProgram.weightedPeriodPath,
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.WeightedPeriodTrace.ExteriorProgram.sum_weighted]
  apply FiniteSum.Fin.sumFin_congr
  intro row
  apply congrArg (coefficients row * ·)
  rw [program.period.program_model]
  have flat := Periods.PreparedRootSafePeriodPrograms.RootClosedState.sample_eq_flat program.period.initial
    (Integration.PreparedRefinementProgramCore.standardDifferentials genus) (Periods.PeriodMatrix.standardDifferential
    row) stage
  dsimp only [Periods.PreparedGridPeriodPrograms.PeriodWalk.state]
  rw [flat, ← Paths.PathArea.increments_sum]
  unfold Periods.PreparedRootSafePeriodPrograms.RootClosedState.flatModel Paths.PathArea.increments
  rw [Data.List.Map.map_map, Data.List.Map.map_map]
  rfl

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.WeightedPeriodTrace.ExteriorProgram

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.WeightedPeriodTrace.SurfacePreparation
namespace CommonBasisRequest
namespace Sampled

open Purelib.Riemann.Normalization

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential : Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {program : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.ExteriorProgram lifted differential} {prepared :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation
    regular domains program}

variable {bounds : Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse.UniformBounds regular.padded}
  {retained : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation.CommonBasisPreparation prepared}
  {basis : Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds.BasisBounds bounds}
  {target coefficientTarget : Normalization.InverseRootPolynomial.Coordinate} {coverFloor floor index minimum stage
    energyFloor radialDepth : Nat}
  {box : Rational.Box} {capSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap
    differential index box}
  {polynomials : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap index box}

variable {request : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation.CommonBasisRequest retained basis
  target coefficientTarget coverFloor floor}
  {plans : request.Plans capSample polynomials minimum} {inputs : retained.Inputs index}
  {readings : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans.Readings retained.anchors retained.sources
    request.schedule.bank plans inputs stage}
  {fans : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Connection.CommonBasisRequest.FanPreparation request plans
    inputs readings energyFloor}
  {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}

/-- The synchronized trace's origin term multiplies the actual weighted
period sample. Root closure alone does not make this finite sample zero. -/
theorem period_trace_decomposition (sample :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Connection.CommonBasisRequest.Sampled fans coefficients radialDepth)
  (periodStage : Nat) :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.CommonScheduledTrace.CommonBasisRequest.Sampled.periodTraceAt sample
      periodStage =
      Path.IncrementArea.pathArea
        (Hyperelliptic.Meshes.PuncturedGrid.Exterior.WeightedPeriodTrace.ExteriorProgram.weightedPeriodPath program
        coefficients periodStage) +
      Path.BoundaryRibbon.area
        (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentConnection.Samples.firstValues retained.anchors
          retained.sources request.schedule.bank
          plans inputs readings fans sample.parents).1
        (FiniteSum.Fin.sumFin (fun row => coefficients row *
          ((program.period.program row).integral.model periodStage).integralSample)) := by
  change Path.IncrementArea.traceArea _
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.WeightedPeriodTrace.ExteriorProgram.weightedPeriodPath program
    coefficients periodStage) = _
  rw [Path.IncrementArea.traceArea_eq,
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.WeightedPeriodTrace.ExteriorProgram.weightedPeriodPath_total program]

end Sampled
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.WeightedPeriodTrace.SurfacePreparation.CommonBasisRequest
