module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentJoins
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentReturn
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedConcatenation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRestorationTrace
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.WeightedResampling
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Vector.Dependent
import Purelib.Integration.Budget.Trace.Family
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.PreparedPathGluing
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.RootContinuation.PreparedCachedParentRoots
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceComparison
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ParentOrientation
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonNumericalBank
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedFamilyAllowance
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonClosingJoins
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Nat.Basic
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Integration.Path.IncrementArea
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Paths.PreparedPathPrimitiveCover
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.RootContinuation.PreparedGridRootClosure
import Purelib.Riemann.Topology.PreparedBankRootChains

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.WeightedResampling.BasisCommonParentBank

open Purelib.Approximation

open Purelib.Curves

open Purelib

open Purelib.Geometry

open Purelib.Integration

open Purelib.Riemann

public section

/-! Common-basis requests on an actual exterior surface component. Anchor
covers come from its retained occurrences; basis covers recast the same
period cache. The original program supplies the parent orientation proof. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation

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

set_option genInjectivity false in
/-- The original exterior anchor covers and recast covers for every basis differential.

The anchor identity binds the common parent bank to the retained surface preparation. -/
structure CommonBasisPreparation (prepared :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation
  regular domains program) where
  /-- The retained covers of the original program's anchor-differential parents. -/ anchors :
    Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.ParentCovers program.cache.parents
  /-- The anchor covers are exactly those of the original surface preparation. -/ anchors_eq : anchors =
    prepared.sourceCovers
  /-- The recast original parent covers for every standard basis differential. -/ sources :
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations.BasisParentSourceCovers program.cache.parents

constructive_injectivity CommonBasisPreparation

namespace CommonBasisPreparation

/-- Construct all basis source covers by recasting the original exterior program cache. -/
@[expose] def build (prepared :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation
  regular domains program) : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation.CommonBasisPreparation
  prepared :=
  ⟨prepared.sourceCovers, rfl,
    Data.Vector.DependentVector.ofFn fun row => prepared.otherSourceCovers (Periods.PeriodMatrix.standardDifferential
      row)⟩

/-- Retain these numerical values across every common-parent acquisition
and every coefficient vector evaluated at the selected index. -/
@[expose] def Inputs (retained : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation.CommonBasisPreparation
  prepared) (index : Nat) :=
  Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans.NumericalBank index retained.anchors retained.sources

/-- Acquire the numerical bank at the supplied stage for these exact retained anchor and basis covers. -/
@[expose] def inputs (retained : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation.CommonBasisPreparation
  prepared) (index : Nat) : retained.Inputs index :=
  Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonNumericalBank.NumericalBank.build index retained.anchors
    retained.sources

end CommonBasisPreparation

variable {bounds : Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse.UniformBounds regular.padded}

set_option genInjectivity false in
/-- A paid common-basis parent schedule with its actual closing root junction.

Concatenation, trace, return and source-restoration costs retain their distinct bounds, while one cached stage covers
both internal and closing joins. -/
structure CommonBasisRequest (retained :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation.CommonBasisPreparation prepared)
    (basis : Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds.BasisBounds bounds)
    (target coefficientTarget : Normalization.InverseRootPolynomial.Coordinate) (coverFloor floor : Nat) where
  /-- The complete original parent-count allocation for the common target. -/ allocation :
    Budget.Trace.Family.BasisFamilyAllowance program.cache.parents.length target
  /-- The common concatenation scale is paid by the squared target. -/ comparison_paid :
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedConcatenation.Samples.concatenationScale (basis := basis)
    (allowance := allocation.allowance)
    program.cache.parents.length ≤ target^2
  /-- The common trace-comparison scale is paid by the squared target. -/ trace_comparison_paid :
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedConcatenation.Samples.traceComparisonScale (basis := basis)
    (allowance := allocation.allowance)
    program.cache.parents.length ≤ target^2
  /-- The retained source-return scale is paid by the squared target. -/ return_paid :
    Charts.Reciprocal.Disk.Basis.CommonParentReturn.BasisCommonParentRequest.Plan.Acquisition.Sample.returnScale
    (basis := basis) (allowance := allocation.allowance) ≤ target^2
  /-- The original weighted source-trace restoration scale is paid by the squared target. -/ source_trace_paid :
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRestorationTrace.Samples.SourceRestoration.traceScale
    (basis := basis) (allowance := allocation.allowance) program.cache.parents.length

        (Charts.Reciprocal.Disk.Basis.WeightedResampling.BasisCommonParentBank.Samples.weightedSourceSlopeMaximum
        retained.anchors retained.sources) ≤ target^2
  /-- The retained common-parent schedule for these anchor and basis covers. -/ schedule :
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentJoins.BasisCommonParentBank.Schedule retained.anchors
    retained.sources basis allocation.allowance coefficientTarget coverFloor floor
  /-- The actual closing junction on the schedule's exact retained parent bank. -/ closing :
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonClosingJoins.BasisCommonParentBank.ClosingJunction retained.anchors
    retained.sources schedule.bank
  /-- The cached stage covering both the schedule and its closing junction. -/ index : Nat
  /-- The cached stage is the maximum of the internal schedule and closing-junction stages. -/ index_eq : index = max
    schedule.index
    (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonClosingJoins.BasisCommonParentBank.ClosingJunction.stage
    retained.anchors retained.sources schedule.bank closing)

constructive_injectivity CommonBasisRequest

namespace CommonBasisRequest

variable {retained : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation.CommonBasisPreparation
  prepared}
  {basis : Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds.BasisBounds bounds}
  {target coefficientTarget : Normalization.InverseRootPolynomial.Coordinate} {coverFloor floor index minimum stage :
    Nat} {box : Rational.Box}

/-- Allocate the common-basis comparison costs and prepare the original parent and closing-junction schedule.

The original program provides its retained root return; the positive area and coefficient tolerances determine the
allocations. -/
@[expose] def build (retained : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation.CommonBasisPreparation
  prepared)
    (basis : Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds.BasisBounds bounds)
    (target coefficientTarget : Normalization.InverseRootPolynomial.Coordinate) (positive : 0 < target)
      (coefficientPositive : 0 < coefficientTarget)
    (coverFloor floor : Nat) : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation.CommonBasisRequest retained
      basis target coefficientTarget coverFloor floor :=
  let budget := Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedFamilyAllowance.BasisPreparedFamilyAllowance.build
    basis program.cache.parents.length target

      (Charts.Reciprocal.Disk.Basis.WeightedResampling.BasisCommonParentBank.Samples.weightedSourceSlopeMaximum
      retained.anchors retained.sources) positive

      (Samples.weightedSourceSlopeMaximum_nonnegative
      retained.anchors retained.sources)
  let allocation := budget.allocation
  let schedule := Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentJoins.BasisCommonParentBank.Schedule.ofCache
    program.cache retained.anchors retained.sources basis
    allocation.allowance coefficientTarget allocation.positive coefficientPositive coverFloor floor
  let closing :=
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonClosingJoins.BasisCommonParentBank.ClosingJunction.build
    retained.anchors retained.sources schedule.bank
    (RootContinuation.PreparedCachedParentRoots.ParentCache.rootChain program.cache) program.cache.chain rfl (by
      change Gaussian.Equivalence.NamedEquivalent
        (Paths.OwnerTraceReadings.ownerName (Paths.PreparedPathGluing.finishOwner
          program.period.closed.traced.prepared))
        (Paths.OwnerTraceReadings.ownerName (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.exteriorOwner
          lifted program.sheet))
      rw [← program.period.closed.traced.finishOwner_eq]
      exact program.period.closed.rootReturn)
  ⟨allocation, budget.paid, budget.trace_paid, budget.return_paid, budget.source_trace_paid, schedule, closing,
    max schedule.index
      (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonClosingJoins.BasisCommonParentBank.ClosingJunction.stage
      retained.anchors retained.sources schedule.bank closing), rfl⟩

variable (request : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation.CommonBasisRequest
  retained basis target coefficientTarget coverFloor floor)
  (capSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box)
  (polynomials : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap index box)

/-- The exact common-parent plans for the supplied cap sample, basis polynomials and retained schedule. -/
@[expose] def Plans (minimum : Nat) :=
  Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans.Plans capSample polynomials minimum retained.anchors
    retained.sources request.schedule.bank

/-- Construct the retained common-parent plans at the supplied minimum stage. -/
@[expose] def plans (minimum : Nat) : request.Plans capSample polynomials minimum :=
  Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans.Plans.build capSample polynomials minimum
    retained.anchors retained.sources request.schedule.bank

variable {capSample polynomials}

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation.CommonBasisRequest in
/-- Root readings pay the closing comparison as well as every internal join. -/
@[expose] def readingStage (plans : request.Plans capSample polynomials minimum) : Nat :=
  max request.index (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans.Schedule.readingStage request.schedule
    plans)

/-- The cached common request stage dominates its internal parent schedule. -/
theorem schedule_index_le : request.schedule.index ≤ request.index :=
  (Purelib.Data.Nat.Order.le_max_left ..).trans_eq request.index_eq.symm

section
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation.CommonBasisRequest
/-- A stage after the retained reading threshold pays all internal parent joins. -/
theorem joins_later (plans : request.Plans capSample polynomials minimum)
    (later : request.readingStage plans ≤ stage) :
    request.schedule.joins.stage retained.anchors retained.sources request.schedule.bank ≤ stage :=
  Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans.Schedule.joins_later request.schedule plans
    ((Purelib.Data.Nat.Order.le_max_right ..).trans later)

/-- A stage after the retained reading threshold also pays the actual closing root junction. -/
theorem closing_later (plans : request.Plans capSample polynomials minimum)
    (later : request.readingStage plans ≤ stage) :
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonClosingJoins.BasisCommonParentBank.ClosingJunction.stage
      retained.anchors retained.sources request.schedule.bank request.closing ≤ stage :=
  (Purelib.Data.Nat.Order.le_max_right ..).trans (request.index_eq.symm.trans_le ((Purelib.Data.Nat.Order.le_max_left
    ..).trans later))

end

variable (capSample polynomials)

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation.CommonBasisRequest in
/-- Acquire the exact occurrence-derived parent bank. Both odd laps retain
all their original parents and inherit orientation from the exterior program. -/
@[expose] def acquire (plans : request.Plans capSample polynomials minimum) (inputs : retained.Inputs index)
    (branch : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1)
    (modelLater : request.index ≤ index) (stage : Nat)
    (later : request.readingStage plans ≤ stage) :
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans.Readings retained.anchors retained.sources
      request.schedule.bank plans inputs stage :=
  Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans.Schedule.acquire request.schedule plans inputs branch
    program.parents_oriented (request.schedule_index_le.trans modelLater) stage
    ((Purelib.Data.Nat.Order.le_max_right ..).trans later)

end CommonBasisRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation
