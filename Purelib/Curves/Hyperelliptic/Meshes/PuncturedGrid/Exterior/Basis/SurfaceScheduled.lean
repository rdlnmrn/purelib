module
import Purelib.Data.Nat.Order
import Purelib.Data.List.Membership
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Gaussian.Norm.Sum.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.ScheduledTraceRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfacePlans
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfacePrepared
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceSamples
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CommonScheduledTrace
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Integration.PreparedWeightedCoefficientBudget
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedObservationCoercivity
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceEnergy
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceTraceRequest
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Basic
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentJoins
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.ScheduledRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.WeightedResampling
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Connection
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CommonPreparedComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Integration.Budget.Trace.Family
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Integration.PreparedRefinementProgramCore
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
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Curves

open Purelib.Data

open Purelib.Geometry

open Purelib

open Purelib.Riemann

@[expose] public section

/-! Aggregate certified source comparisons on the actual surface acquisition. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceScheduled

open Purelib.Riemann.Normalization

open Purelib.Data.Rat.Fraction.Compatibility

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential : Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {bounds : Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse.UniformBounds regular.padded}

variable {basis : Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds.BasisBounds bounds}
  {target coefficientTarget : Normalization.InverseRootPolynomial.Coordinate} {coverFloor floor index minimum
    readingIndex : Nat}
  {box : Rational.Box} {capSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap
    differential index box}
  {polynomials : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap index box}

variable {energyFloor radialDepth : Nat}
  {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}

namespace Plans.Samples

/-- The dependent spine of scheduled source-versus-period comparisons on the original acquired components.

Each component retains its exact samples and prepared comparisons at the common error target. -/
def ScheduledComparisons (errorTarget : Normalization.InverseRootPolynomial.Coordinate) :
    (entries : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRequest.Entry (domains := domains)
      (differential := differential) basis target coefficientTarget coverFloor floor)) →
    (plans : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfacePlans.Plans capSample polynomials minimum entries)
      → (readings : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfacePlans.Plans.Readings entries plans
      readingIndex) →
    (fans : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceSamples.Plans.FanPreparations energyFloor entries
      plans readings) →
    (samples : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceSamples.Plans.Samples coefficients radialDepth
      entries plans readings fans) →
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfacePrepared.Plans.Samples.PreparedComparisons entries plans
      readings fans samples → Type
  | [], _, _, _, _, _ => PUnit
  | _ :: tail, plans, readings, fans, samples, comparisons =>

        CommonScheduledTrace.CommonBasisRequest.Sampled.ScheduledSourceComparison
        samples.1 comparisons.1 errorTarget ×

          ScheduledComparisons
          errorTarget tail plans.2 readings.2 fans.2 samples.2 comparisons.2

/-- The shared coefficient tolerance and cover floor pay this original component's trace allocation. -/
def Compatible (errorTarget : Normalization.InverseRootPolynomial.Coordinate) (positive : 0 < errorTarget)
    (entry : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRequest.Entry (domains := domains) (differential
      := differential) basis target coefficientTarget coverFloor floor) : Prop :=
  coefficientTarget ≤ Integration.PreparedWeightedCoefficientBudget.coefficientTolerance
    entry.component.program.period.initial
      (Hyperelliptic.Charts.Reciprocal.Disk.Basis.ScheduledTraceRequest.Samples.traceAllocation entry.retained.anchors
      entry.retained.sources errorTarget (2 + 8 * basis.coefficient) positive
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceTraceRequest.TraceComponent.originBound_nonnegative
      basis)).half ∧
  (Hyperelliptic.Charts.Reciprocal.Disk.Basis.ScheduledTraceRequest.Samples.traceAllocation entry.retained.anchors
    entry.retained.sources errorTarget (2 + 8 * basis.coefficient) positive
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceTraceRequest.TraceComponent.originBound_nonnegative
    basis)).coverFloor ≤ coverFloor

/-- Compute a common original-stage threshold from these exact acquired banks. -/
def threshold (errorTarget : Normalization.InverseRootPolynomial.Coordinate) (positive : 0 < errorTarget)
    (coefficientNonnegative : 0 ≤ coefficientTarget) :
    (entries : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRequest.Entry (domains := domains)
      (differential := differential) basis target coefficientTarget coverFloor floor)) →
    (plans : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfacePlans.Plans capSample polynomials minimum entries)
      → (readings : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfacePlans.Plans.Readings entries plans
      readingIndex) →
    (fans : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceSamples.Plans.FanPreparations energyFloor entries
      plans readings) →
    (samples : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceSamples.Plans.Samples coefficients radialDepth
      entries plans readings fans) →
    (comparisons : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfacePrepared.Plans.Samples.PreparedComparisons
      entries plans readings fans samples) →
    (∀ entry ∈ entries, Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceScheduled.Plans.Samples.Compatible
      errorTarget positive entry) → Nat
  | [], _, _, _, _, _, _ => 0
  | head :: tail, plans, readings, fans, samples, comparisons, compatible =>
      max (Hyperelliptic.Meshes.PuncturedGrid.Exterior.CommonScheduledTrace.CommonBasisRequest.Sampled.sourceSelection
        samples.1 comparisons.1 errorTarget positive coefficientNonnegative
        (compatible head (List.mem_cons_self ..)).1).predecessor
        (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceScheduled.Plans.Samples.threshold
          errorTarget positive coefficientNonnegative tail plans.2 readings.2 fans.2 samples.2 comparisons.2
          (fun entry member => compatible entry (List.mem_cons_of_mem head member)))

/-- Compare every original acquired component at a shared paid predecessor stage.

The exact per-component compatibility witnesses pay both source tolerances and retained cover floors. -/
def compareScheduled (branch : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1)
    (errorTarget : Normalization.InverseRootPolynomial.Coordinate) (positive : 0 < errorTarget) (coefficientNonnegative
      : 0 ≤ coefficientTarget) :
    (entries : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRequest.Entry (domains := domains)
      (differential := differential) basis target coefficientTarget coverFloor floor)) →
    (plans : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfacePlans.Plans capSample polynomials minimum entries)
      → (readings : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfacePlans.Plans.Readings entries plans
      readingIndex) →
    (fans : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceSamples.Plans.FanPreparations energyFloor entries
      plans readings) →
    (samples : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceSamples.Plans.Samples coefficients radialDepth
      entries plans readings fans) →
    (comparisons : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfacePrepared.Plans.Samples.PreparedComparisons
      entries plans readings fans samples) →
    (compatible : ∀ entry ∈ entries,
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceScheduled.Plans.Samples.Compatible errorTarget positive
      entry) →
    (predecessor : Nat) → Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceScheduled.Plans.Samples.threshold
      errorTarget positive coefficientNonnegative entries plans readings fans samples comparisons compatible ≤
      predecessor →
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceScheduled.Plans.Samples.ScheduledComparisons errorTarget
      entries plans readings fans samples comparisons
  | [], _, _, _, _, _, _, _, _ => PUnit.unit
  | head :: tail, plans, readings, fans, samples, comparisons, compatible, predecessor, later =>

        (CommonScheduledTrace.CommonBasisRequest.Sampled.compareScheduledSource
        samples.1 comparisons.1 branch errorTarget positive coefficientNonnegative
        (compatible head (List.mem_cons_self ..)).1 (compatible head (List.mem_cons_self ..)).2 predecessor
        ((Nat.Order.le_max_left ..).trans later),
      Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceScheduled.Plans.Samples.compareScheduled
        branch errorTarget positive coefficientNonnegative tail plans.2 readings.2 fans.2 samples.2 comparisons.2
        (fun entry member => compatible entry (List.mem_cons_of_mem head member)) predecessor ((Nat.Order.le_max_right
          ..).trans later))

/-- Every retained component uses the displayed original stage. -/
def AtStage (stage : Nat) {errorTarget : Normalization.InverseRootPolynomial.Coordinate} :
    (entries : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRequest.Entry (domains := domains)
      (differential := differential) basis target coefficientTarget coverFloor floor)) →
    (plans : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfacePlans.Plans capSample polynomials minimum entries)
      → (readings : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfacePlans.Plans.Readings entries plans
      readingIndex) →
    (fans : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceSamples.Plans.FanPreparations energyFloor entries
      plans readings) →
    (samples : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceSamples.Plans.Samples coefficients radialDepth
      entries plans readings fans) →
    (comparisons : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfacePrepared.Plans.Samples.PreparedComparisons
      entries plans readings fans samples) →
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceScheduled.Plans.Samples.ScheduledComparisons errorTarget
      entries plans readings fans samples comparisons → Prop
  | [], _, _, _, _, _, _ => True
  | _ :: tail, plans, readings, fans, samples, comparisons, scheduled =>
      scheduled.1.stage = stage ∧
        Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceScheduled.Plans.Samples.AtStage stage
        tail plans.2 readings.2 fans.2 samples.2 comparisons.2 scheduled.2

/-- Every comparison constructed at the paid predecessor retains exactly its successor as the original stage. -/
theorem compareScheduled_atStage (branch : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve =
  1)
    (errorTarget : Normalization.InverseRootPolynomial.Coordinate) (positive : 0 < errorTarget) (coefficientNonnegative
      : 0 ≤ coefficientTarget) :
    (entries : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRequest.Entry (domains := domains)
      (differential := differential) basis target coefficientTarget coverFloor floor)) →
    (plans : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfacePlans.Plans capSample polynomials minimum entries)
      → (readings : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfacePlans.Plans.Readings entries plans
      readingIndex) →
    (fans : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceSamples.Plans.FanPreparations energyFloor entries
      plans readings) →
    (samples : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceSamples.Plans.Samples coefficients radialDepth
      entries plans readings fans) →
    (comparisons : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfacePrepared.Plans.Samples.PreparedComparisons
      entries plans readings fans samples) →
    (compatible : ∀ entry ∈ entries,
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceScheduled.Plans.Samples.Compatible errorTarget positive
      entry) →
    (predecessor : Nat) →
    (later : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceScheduled.Plans.Samples.threshold errorTarget
      positive coefficientNonnegative entries plans readings fans samples comparisons compatible ≤ predecessor) →
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceScheduled.Plans.Samples.AtStage (predecessor + 1) entries
      plans readings fans samples comparisons
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceScheduled.Plans.Samples.compareScheduled branch
        errorTarget positive coefficientNonnegative entries plans readings fans samples comparisons compatible
        predecessor later)
  | [], _, _, _, _, _, _, _, _ => trivial
  | head :: tail, plans, readings, fans, samples, comparisons, compatible, predecessor, later =>
      ⟨rfl,
        compareScheduled_atStage
        branch errorTarget positive coefficientNonnegative tail plans.2 readings.2 fans.2 samples.2 comparisons.2
        (fun entry member => compatible entry (List.mem_cons_of_mem head member)) predecessor ((Nat.Order.le_max_right
          ..).trans later)⟩

/-- Read the ordered list of original source-minus-period trace discrepancies. -/
def scheduledErrors {errorTarget : Normalization.InverseRootPolynomial.Coordinate} :
    (entries : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRequest.Entry (domains := domains)
      (differential := differential) basis target coefficientTarget coverFloor floor)) →
    (plans : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfacePlans.Plans capSample polynomials minimum entries)
      → (readings : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfacePlans.Plans.Readings entries plans
      readingIndex) →
    (fans : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceSamples.Plans.FanPreparations energyFloor entries
      plans readings) →
    (samples : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceSamples.Plans.Samples coefficients radialDepth
      entries plans readings fans) →
    (comparisons : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfacePrepared.Plans.Samples.PreparedComparisons
      entries plans readings fans samples) →
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceScheduled.Plans.Samples.ScheduledComparisons errorTarget
      entries plans readings fans samples comparisons → List Normalization.InverseRootPolynomial.Gaussian
  | [], _, _, _, _, _, _ => []
  | _ :: tail, plans, readings, fans, samples, comparisons, scheduled =>
      (scheduled.1.source - scheduled.1.period) ::
        Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceScheduled.Plans.Samples.scheduledErrors
          tail plans.2 readings.2 fans.2 samples.2 comparisons.2 scheduled.2

/-- There is exactly one retained scheduled discrepancy for each original component entry. -/
theorem scheduledErrors_length {errorTarget : Normalization.InverseRootPolynomial.Coordinate} :
    (entries : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRequest.Entry (domains := domains)
      (differential := differential) basis target coefficientTarget coverFloor floor)) →
    (plans : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfacePlans.Plans capSample polynomials minimum entries)
      → (readings : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfacePlans.Plans.Readings entries plans
      readingIndex) →
    (fans : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceSamples.Plans.FanPreparations energyFloor entries
      plans readings) →
    (samples : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceSamples.Plans.Samples coefficients radialDepth
      entries plans readings fans) →
    (comparisons : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfacePrepared.Plans.Samples.PreparedComparisons
      entries plans readings fans samples) →
    (scheduled : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceScheduled.Plans.Samples.ScheduledComparisons
      errorTarget entries plans readings fans samples comparisons) →
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceScheduled.Plans.Samples.scheduledErrors entries plans
      readings fans samples comparisons scheduled).length = entries.length
  | [], _, _, _, _, _, _ => rfl
  | _ :: tail, plans, readings, fans, samples, comparisons, scheduled =>
      congrArg Nat.succ
        (scheduledErrors_length
        tail plans.2 readings.2 fans.2 samples.2 comparisons.2 scheduled.2)

/-- Every retained component discrepancy meets the common homogeneous trace-error bound. -/
theorem scheduledErrors_bounded {errorTarget : Normalization.InverseRootPolynomial.Coordinate} :
    (entries : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRequest.Entry (domains := domains)
      (differential := differential) basis target coefficientTarget coverFloor floor)) →
    (plans : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfacePlans.Plans capSample polynomials minimum entries)
      → (readings : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfacePlans.Plans.Readings entries plans
      readingIndex) →
    (fans : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceSamples.Plans.FanPreparations energyFloor entries
      plans readings) →
    (samples : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceSamples.Plans.Samples coefficients radialDepth
      entries plans readings fans) →
    (comparisons : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfacePrepared.Plans.Samples.PreparedComparisons
      entries plans readings fans samples) →
    (scheduled : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceScheduled.Plans.Samples.ScheduledComparisons
      errorTarget entries plans readings fans samples comparisons) →
    ∀ value ∈ Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceScheduled.Plans.Samples.scheduledErrors entries
      plans readings fans samples comparisons scheduled,
      Data.Gaussian.Norm.Basic.normSq value ≤ errorTarget * Readings.PreparedObservationCoercivity.coefficientNormSq
        coefficients ^ 2
  | [], _, _, _, _, _, _, _, member => False.elim (List.not_mem_nil member)
  | _ :: tail, plans, readings, fans, samples, comparisons, scheduled, value, member => by
      rcases List.Membership.mem_cons.mp member with same | later
      · subst value; exact scheduled.1.bounded
      · exact
          scheduledErrors_bounded
          tail plans.2 readings.2 fans.2 samples.2 comparisons.2 scheduled.2 value later

end Plans.Samples

namespace ScheduledRequest

variable {prepared :
  SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
  regular domains differential} {errorTarget : Normalization.InverseRootPolynomial.Coordinate}
  (scheduled : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceTraceRequest.ScheduledRequest prepared basis
    target errorTarget floor)
  (acquired : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceEnergy.Request.Acquisition scheduled.request
    capSample polynomials minimum energyFloor)
  (evaluation : acquired.Evaluation coefficients)

/-- The exact component-comparison spine for this scheduled request and original cached evaluation. -/
def Comparisons := Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceScheduled.Plans.Samples.ScheduledComparisons
  scheduled.localError scheduled.request.entries
  acquired.plans acquired.readings acquired.fans evaluation.samples evaluation.comparisons

set_option genInjectivity false in
/-- The common stage and the component values are retained together with
literal stage readbacks; no equality between distinct samples is asserted. -/
structure SynchronizedComparisons where
  /-- The retained common predecessor of all original comparison stages. -/ predecessor : Nat
  /-- The component comparisons on the exact original acquisition and evaluation. -/ comparisons :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceScheduled.ScheduledRequest.Comparisons scheduled acquired
    evaluation
  /-- Every retained component comparison uses exactly the shared predecessor's successor stage. -/ atStage :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceScheduled.Plans.Samples.AtStage (predecessor + 1)
    scheduled.request.entries
    acquired.plans acquired.readings acquired.fans evaluation.samples evaluation.comparisons comparisons

constructive_injectivity SynchronizedComparisons

/-- Reuse the complete-surface evaluation's banks and compare every component
at the maximum of its internally certified original-stage thresholds. -/
def compareSources (branch : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1) :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceScheduled.ScheduledRequest.SynchronizedComparisons scheduled
  acquired evaluation :=
  let predecessor := Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceScheduled.Plans.Samples.threshold
    scheduled.localError scheduled.positive scheduled.coefficientPositive.le
    scheduled.request.entries acquired.plans acquired.readings acquired.fans evaluation.samples evaluation.comparisons
      scheduled.compatible
  let comparisons := Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceScheduled.Plans.Samples.compareScheduled
    branch scheduled.localError scheduled.positive scheduled.coefficientPositive.le
    scheduled.request.entries acquired.plans acquired.readings acquired.fans evaluation.samples evaluation.comparisons
      scheduled.compatible predecessor le_rfl
  ⟨predecessor, comparisons,
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceScheduled.Plans.Samples.compareScheduled_atStage branch
    scheduled.localError scheduled.positive scheduled.coefficientPositive.le
    scheduled.request.entries acquired.plans acquired.readings acquired.fans evaluation.samples evaluation.comparisons
      scheduled.compatible predecessor le_rfl⟩

/-- The sum compares source and period traces component by component; it
introduces no joining polygon between disconnected surface components. -/
theorem source_error_bound (comparisons :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceScheduled.ScheduledRequest.Comparisons scheduled acquired
  evaluation) :
    Data.Gaussian.Norm.Basic.normSq
      (Data.Gaussian.Norm.Sum.Basic.gaussianSum
        (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceScheduled.Plans.Samples.scheduledErrors
          scheduled.request.entries acquired.plans acquired.readings acquired.fans
          evaluation.samples evaluation.comparisons comparisons)) ≤
      errorTarget * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients ^ 2 := open Purelib.Data.Rat
        in by
  have bounded := Gaussian.Norm.Sum.Bounds.normSq_sum_le
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceScheduled.Plans.Samples.scheduledErrors
      scheduled.request.entries acquired.plans acquired.readings acquired.fans
      evaluation.samples evaluation.comparisons comparisons) _
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceScheduled.Plans.Samples.scheduledErrors_bounded
      scheduled.request.entries acquired.plans acquired.readings acquired.fans
      evaluation.samples evaluation.comparisons comparisons)
  rw [Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceScheduled.Plans.Samples.scheduledErrors_length,
    scheduled.request.entries_length] at bounded
  apply bounded.trans
  exact (show (prepared.components.length : Normalization.InverseRootPolynomial.Coordinate) *
      ((prepared.components.length : Normalization.InverseRootPolynomial.Coordinate) * (scheduled.localError *
        Readings.PreparedObservationCoercivity.coefficientNormSq coefficients ^ 2)) =
      ((prepared.components.length : Normalization.InverseRootPolynomial.Coordinate)^2 * scheduled.localError) *
        Readings.PreparedObservationCoercivity.coefficientNormSq coefficients ^ 2 by ring1).trans_le
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct scheduled.paid
      (Fraction.Order.Arithmetic.sq_nonneg_direct _))

end ScheduledRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceScheduled
