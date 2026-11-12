module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentConnection
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedConcatenation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRestorationPairs
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRestorationTrace
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.WeightedResampling
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
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
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.IncrementArea
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedRefinementProgramCore
import Purelib.Riemann.Integration.PreparedWeightedCoefficientBudget
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.PreparedScheduledPrimitivePaths
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Riemann.Topology.PreparedSurfaceCoercivity
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CommonPreparedComparison
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.ScheduledTraceRequest
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentJoins
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.ScheduledRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ParentOrientation
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Integration.Budget.Trace.Family
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Integration.PreparedSwitchedRefinements
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Paths.PreparedWeightedTraceAllocation
import Purelib.Riemann.Paths.PreparedWeightedTraceStage
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.RootContinuation.PreparedGridRootClosure
import Purelib.Riemann.Topology.PreparedBankRootChains
import Purelib.Riemann.Topology.PreparedRootSafeCycleStates
import Purelib.Tactic.Ring

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis

open Purelib.Data.Rat.Fraction.Order

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CommonPreparedComparison.CommonBasisRequest

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Algebra

open Purelib.Curves

open Purelib.Data

open Purelib.Geometry

open Purelib.Integration

open Purelib

open Purelib.Riemann

public section

/-! Original scheduled source traces on the retained exterior component. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CommonScheduledTrace

open Purelib.Riemann.Normalization

variable {genus : Nat} {curve : Basic.HyperellipticCurve genus} {branches :
  Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential : Differentials.Basic.Differential genus}
  {collar : ReciprocalExteriorCollar.Data curve} {cap :
    ReciprocalInnerInverse.Data curve collar}
  {regular : Disk.RegularBounds.Data cap} {domains :
    Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {program : PeriodPrograms.ExteriorProgram lifted differential} {prepared :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation
    regular domains program}

variable {bounds : ReciprocalPaddedInverse.UniformBounds regular.padded}
  {retained : Preparation.CommonBasisPreparation prepared}
  {basis : ReciprocalPaddedBasisBounds.BasisBounds bounds}
  {target coefficientTarget : InverseRootPolynomial.Coordinate} {coverFloor floor index minimum stage
    energyFloor radialDepth : Nat}
  {box : Rational.Box} {capSample : Cap.Primitives.Sample cap
    differential index box}
  {polynomials : CapBasisEnergy.RegularBasisPolynomials cap index box}

namespace CommonBasisPreparation

/-- Allocate source-trace error using the actual component's retained covers
and its pre-acquisition initial-value ceiling. -/
@[expose] def traceAllocation (retained :
  Preparation.CommonBasisPreparation prepared)
    (basis : ReciprocalPaddedBasisBounds.BasisBounds bounds)
    (errorTarget : InverseRootPolynomial.Coordinate) (positive : 0 < errorTarget) :=
  open Purelib.Data.Rat in Hyperelliptic.Charts.Reciprocal.Disk.Basis.ScheduledTraceRequest.Samples.traceAllocation
    retained.anchors retained.sources
    errorTarget (2 + 8 * basis.coefficient) positive
    (add_nonneg (by decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 2)
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by
          decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 8)
        basis.coefficient_nonnegative))

end CommonBasisPreparation

namespace CommonBasisRequest

variable {request : Preparation.CommonBasisRequest retained basis
  target coefficientTarget coverFloor floor}
  {plans : request.Plans capSample polynomials minimum} {inputs : retained.Inputs index}
  {readings : Disk.Basis.CommonParentPlans.Readings retained.anchors retained.sources
    request.schedule.bank plans inputs stage}
  {fans : Connection.CommonBasisRequest.FanPreparation request plans
    inputs readings energyFloor}
  {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}

namespace Sampled

/-- The retained source bank computes the threshold for every later comparison. -/
@[expose] def sourceSelection (sample :
  Connection.CommonBasisRequest.Sampled fans coefficients radialDepth)
    (comparisons :
      (Sampled.PreparedComparisons
      sample))
    (errorTarget : InverseRootPolynomial.Coordinate) (positive : 0 < errorTarget)
    (coefficientNonnegative : 0 ≤ coefficientTarget)
    (coefficientLe : coefficientTarget ≤
      Integration.PreparedWeightedCoefficientBudget.coefficientTolerance
        program.period.initial
          ((CommonBasisPreparation.traceAllocation
          retained basis errorTarget positive)).half)
    := Disk.Basis.ScheduledTraceRequest.Samples.TraceRequest.select
      program.period.initial (Integration.PreparedRefinementProgramCore.standardDifferentials genus)
      retained.anchors retained.sources
        ((CommonBasisPreparation.traceAllocation
        retained basis errorTarget positive))
      request.schedule.bank plans inputs readings fans sample.parents comparisons coefficientNonnegative coefficientLe
      Integration.PreparedRefinementProgramCore.standardDifferential_mem_standardDifferentials program.parents_oriented

/-- Compare this component's cached source trace at its actual initial value
with its original period schedule. Endpoint restoration remains separate. -/
theorem scheduled_source_bound (sample :
  Connection.CommonBasisRequest.Sampled fans coefficients radialDepth)
    (comparisons :
      (Sampled.PreparedComparisons
      sample))
    (branch : HyperellipticReciprocal.originOrder curve = 1)
    (errorTarget : InverseRootPolynomial.Coordinate) (positive : 0 < errorTarget)
    (coefficientNonnegative : 0 ≤ coefficientTarget)
    (coefficientLe : coefficientTarget ≤
      Integration.PreparedWeightedCoefficientBudget.coefficientTolerance
        program.period.initial
          ((CommonBasisPreparation.traceAllocation
          retained basis errorTarget positive)).half)
    (coverLater :
      ((CommonBasisPreparation.traceAllocation retained
      basis errorTarget positive)).coverFloor ≤ coverFloor)
    (predecessor : Nat)
    (later :
      (Sampled.sourceSelection
      sample comparisons errorTarget positive coefficientNonnegative coefficientLe).predecessor ≤ predecessor) :
    let current := program.period.initial.states (Integration.PreparedRefinementProgramCore.standardDifferentials genus)
      (predecessor + 1)
    let pairs :=
      Disk.Basis.WeightedResampling.BasisCommonParentBank.Samples.sourceResamplingPairs
      (Paths.PreparedScheduledPrimitivePaths.RootClosedState.spatialDepth program.period.initial
        (Integration.PreparedRefinementProgramCore.standardDifferentials genus) (predecessor + 1))
      retained.anchors retained.sources request.schedule.bank plans inputs readings fans sample.parents comparisons
    let previous := (Disk.Basis.CommonParentConnection.Samples.firstValues
      retained.anchors retained.sources request.schedule.bank
      plans inputs readings fans sample.parents).1
    Gaussian.Norm.Basic.normSq
      (Path.IncrementArea.traceArea previous (pairs.map Prod.snd).flatten -
        Path.IncrementArea.traceArea previous (current.state.parents.map (fun child =>
          FiniteSum.Fin.sumFin (fun row => coefficients row *
            (Integration.PreparedEdgeRecasting.recastCenteredEdge
              (Periods.PeriodMatrix.standardDifferential row) child).model.integralSample)))) ≤
      errorTarget * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients ^ 2 :=
  Disk.Basis.ScheduledTraceRequest.Samples.TraceRequest.accurate program.period.initial
    (Integration.PreparedRefinementProgramCore.standardDifferentials genus)
    retained.anchors retained.sources
      ((CommonBasisPreparation.traceAllocation retained
      basis errorTarget positive))
    request.schedule.bank plans inputs readings fans sample.parents comparisons coefficientNonnegative coefficientLe
    Integration.PreparedRefinementProgramCore.standardDifferential_mem_standardDifferentials program.parents_oriented
      coverLater _
    (Disk.Basis.CommonPreparedConcatenation.Samples.firstValue_bound branch
      retained.anchors retained.sources request.schedule.bank
      plans inputs readings fans sample.parents comparisons)
    predecessor later

/-- Literal source trace on the retained bank at an original schedule stage. -/
@[expose] def sourceTraceAt (sample :
  Connection.CommonBasisRequest.Sampled fans coefficients radialDepth)
    (comparisons :
      (Sampled.PreparedComparisons
      sample)) (stage : Nat) : InverseRootPolynomial.Gaussian :=
  let pairs :=
    Disk.Basis.WeightedResampling.BasisCommonParentBank.Samples.sourceResamplingPairs
    (Paths.PreparedScheduledPrimitivePaths.RootClosedState.spatialDepth program.period.initial
    (Integration.PreparedRefinementProgramCore.standardDifferentials genus) stage)
    retained.anchors retained.sources request.schedule.bank plans inputs readings fans sample.parents comparisons
  let previous := (Disk.Basis.CommonParentConnection.Samples.firstValues
    retained.anchors retained.sources request.schedule.bank
    plans inputs readings fans sample.parents).1
  Path.IncrementArea.traceArea previous (pairs.map Prod.snd).flatten

/-- The actual original period children, with the same retained trace origin. -/
@[expose] def periodTraceAt (sample :
  Connection.CommonBasisRequest.Sampled fans coefficients radialDepth)
  (stage : Nat) : InverseRootPolynomial.Gaussian :=
  let previous := (Disk.Basis.CommonParentConnection.Samples.firstValues
    retained.anchors retained.sources request.schedule.bank
    plans inputs readings fans sample.parents).1
  let current := program.period.initial.states (Integration.PreparedRefinementProgramCore.standardDifferentials genus)
    stage
  Path.IncrementArea.traceArea previous (current.state.parents.map (fun child =>
    FiniteSum.Fin.sumFin (fun row => coefficients row *
      (Integration.PreparedEdgeRecasting.recastCenteredEdge (Periods.PeriodMatrix.standardDifferential row)
        child).model.integralSample)))

open Purelib.Data.Rat in
/-- The component request pays restoration on the actual prepared paths,
including their joining polygon and initial-value ribbon. -/
theorem restored_source_bound (sample :
  Connection.CommonBasisRequest.Sampled fans coefficients radialDepth)
    (comparisons :
      (Sampled.PreparedComparisons
      sample))
    (branch : HyperellipticReciprocal.originOrder curve = 1)
    (later : request.readingStage plans ≤ stage) (periodStage : Nat) :
    let previous := (Disk.Basis.CommonParentConnection.Samples.firstValues
      retained.anchors retained.sources request.schedule.bank
      plans inputs readings fans sample.parents).1
    Gaussian.Norm.Basic.normSq
      (Path.IncrementArea.traceArea previous
        ((Sampled.preparedPaths
        sample comparisons)).flatten -
        (Sampled.sourceTraceAt
          sample comparisons periodStage)) ≤
      target^2 * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients ^ 2 := by
  have bounded :=
    Disk.Basis.SourceRestorationTrace.Samples.SourceRestoration.trace_bound
    sample.parents comparisons request.schedule.joins branch
    (request.joins_later plans later)
  dsimp only at bounded
  rw [Disk.Basis.SourceRestorationPairs.Samples.SourceRestoration.left,
    Disk.Basis.SourceRestorationPairs.Samples.SourceRestoration.right
      (Paths.PreparedScheduledPrimitivePaths.RootClosedState.spatialDepth program.period.initial
      (Integration.PreparedRefinementProgramCore.standardDifferentials genus) periodStage)] at bounded
  exact bounded.trans (Arithmetic.mul_le_mul_of_nonneg_right_direct request.source_trace_paid
    (Arithmetic.sq_nonneg_direct _))

/-- The complete prepared-trace lower bound transfers to the cached source
trace with one further component allowance. -/
theorem source_lower (sample : Connection.CommonBasisRequest.Sampled
  fans coefficients radialDepth)
    (comparisons :
      (Sampled.PreparedComparisons
      sample)) (trace :
      (Sampled.PreparedTrace
      sample comparisons))
    (branch : HyperellipticReciprocal.originOrder curve = 1)
    (later : request.readingStage plans ≤ stage) (periodStage : Nat) :
    -(4 * target * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients) ≤
      (-((Sampled.sourceTraceAt
        sample comparisons periodStage))).im / 4 := open Rat in by
  have normNonnegative : 0 ≤ Readings.PreparedObservationCoercivity.coefficientNormSq coefficients :=
    FiniteSum.Fin.sumFin_zero.symm.trans_le
      (FiniteSum.Rational.Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 :
        InverseRootPolynomial.Coordinate)) _
        (fun row => Gaussian.Basic.Canonical.normSq_nonneg (coefficients row)))
  have targetNonnegative : 0 ≤ target :=
    ((Arithmetic.mul_nonneg_direct
      (Arithmetic.mul_nonneg_direct (by
          decide : (0 : InverseRootPolynomial.Coordinate) ≤ 4)
        (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le program.cache.parents.length)))
          request.allocation.positive.le).trans_eq
      request.allocation.loss_eq.symm).trans request.allocation.paid
  have bounded :=
    Sampled.restored_source_bound
    sample comparisons branch later periodStage
  dsimp only at bounded
  rw [← trace.trace_eq] at bounded
  have error : Gaussian.Norm.Basic.normSq
      ((-trace.trace) -
        (-((Sampled.sourceTraceAt
        sample comparisons periodStage)))) ≤
      (4 * (target * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients))^2 := by
    rw [show (-trace.trace) -
      (-((Sampled.sourceTraceAt
      sample comparisons periodStage))) =
      -(trace.trace -
        (Sampled.sourceTraceAt
        sample comparisons periodStage)) by ring1, Gaussian.Norm.Basic.normSq_neg]
    apply bounded.trans
    exact (show target^2 * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients ^ 2 =
      1 * (target * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)^2 by ring1).trans_le
      ((Arithmetic.mul_le_mul_of_nonneg_right_direct (by
          decide : (1 : InverseRootPolynomial.Coordinate) ≤ 16)
        (Arithmetic.sq_nonneg_direct _)).trans_eq (by ring1))
  have comparison := Topology.PreparedSurfaceCoercivity.boundaryEnergy_sub_budget_le
    (-trace.trace)
      (-((Sampled.sourceTraceAt
      sample comparisons periodStage)))
    (target * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)
    (Arithmetic.mul_nonneg_direct targetNonnegative normNonnegative) error
  exact (show -(4 * target * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients) =
      -((target + target + target) * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients) -
        target * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients by ring1).trans_le
    ((Arithmetic.sub_le_sub_right_direct trace.trace_lower
      (target * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)).trans comparison)

set_option genInjectivity false in
/-- Cache the selected stage and both trace values for later surface transport. -/
structure ScheduledSourceComparison (sample :
  Connection.CommonBasisRequest.Sampled fans coefficients radialDepth)
    (comparisons :
      (Sampled.PreparedComparisons
      sample)) (errorTarget : InverseRootPolynomial.Coordinate) where
  /-- The retained original period-schedule stage. -/ stage : Nat
  /-- The cached source trace on the retained common parent bank. -/ source :
    InverseRootPolynomial.Gaussian
  /-- The cached source value is the original source trace at the retained stage. -/ source_eq : source =
    (Sampled.sourceTraceAt sample
    comparisons stage)
  /-- The cached trace of the original scheduled period children. -/ period :
    InverseRootPolynomial.Gaussian
  /-- The cached period value is the original period trace at that same stage. -/ period_eq : period =
    (Sampled.periodTraceAt sample
    stage)
  /-- The two retained traces satisfy the requested coefficient-homogeneous error bound. -/ bounded :
    Gaussian.Norm.Basic.normSq (source - period) ≤
    errorTarget * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients ^ 2

constructive_injectivity ScheduledSourceComparison

/-- Cache both the original scheduled period trace and retained source trace at the selected paid stage.

The source allocation, coefficient tolerance and cover threshold pay their homogeneous comparison on the same component
bank. -/
@[expose] def compareScheduledSource (sample :
  Connection.CommonBasisRequest.Sampled fans coefficients radialDepth)
    (comparisons :
      (Sampled.PreparedComparisons
      sample))
    (branch : HyperellipticReciprocal.originOrder curve = 1)
    (errorTarget : InverseRootPolynomial.Coordinate) (positive : 0 < errorTarget)
    (coefficientNonnegative : 0 ≤ coefficientTarget)
    (coefficientLe : coefficientTarget ≤
      Integration.PreparedWeightedCoefficientBudget.coefficientTolerance
        program.period.initial
          ((CommonBasisPreparation.traceAllocation
          retained basis errorTarget positive)).half)
    (coverLater :
      ((CommonBasisPreparation.traceAllocation retained
      basis errorTarget positive)).coverFloor ≤ coverFloor)
    (predecessor : Nat)
    (later :
      (Sampled.sourceSelection
      sample comparisons errorTarget positive coefficientNonnegative coefficientLe).predecessor ≤ predecessor) :

      (ScheduledSourceComparison
      sample comparisons errorTarget) :=
  let stage := predecessor + 1
  ⟨stage, (Sampled.sourceTraceAt
    sample comparisons stage), rfl,
    (Sampled.periodTraceAt sample
    stage), rfl,
    Sampled.scheduled_source_bound
      sample comparisons branch errorTarget positive coefficientNonnegative coefficientLe coverLater predecessor later⟩

end Sampled
end CommonBasisRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CommonScheduledTrace
