module
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Cast
import Purelib.Data.Nat.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfacePlans
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfacePrepared
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceSamples
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceTraceRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CommonScheduledTrace
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Riemann.Topology.PreparedSurfaceCoercivity
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceScheduled
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Connection
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CommonPreparedComparison
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Tactic.Ring

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib

open Purelib.Riemann

@[expose] public section

/-! Transfer the complete-surface lower bound through cached source traces. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceScheduledEnergy

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

open Purelib.Data.Gaussian.Basic.Canonical

namespace Plans.Samples

/-- Read the negated original source traces in retained component order. -/
def sourceValues {errorTarget : Normalization.InverseRootPolynomial.Coordinate} :
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
      (-scheduled.1.source) ::
        sourceValues
        tail plans.2 readings.2 fans.2 samples.2 comparisons.2 scheduled.2

/-- Read the negated original period traces in retained component order. -/
def periodValues {errorTarget : Normalization.InverseRootPolynomial.Coordinate} :
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
      (-scheduled.1.period) ::
        periodValues
        tail plans.2 readings.2 fans.2 samples.2 comparisons.2 scheduled.2

/-- Read the actual period trace of every component at one original stage. -/
def periodValuesAt (stage : Nat) :
    (entries : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRequest.Entry (domains := domains)
      (differential := differential) basis target coefficientTarget coverFloor floor)) →
    (plans : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfacePlans.Plans capSample polynomials minimum entries)
      → (readings : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfacePlans.Plans.Readings entries plans
      readingIndex) →
    (fans : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceSamples.Plans.FanPreparations energyFloor entries
      plans readings) →
    (samples : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceSamples.Plans.Samples coefficients radialDepth
      entries plans readings fans) →
    List Normalization.InverseRootPolynomial.Gaussian
  | [], _, _, _, _ => []
  | _ :: tail, plans, readings, fans, samples =>
      (-Hyperelliptic.Meshes.PuncturedGrid.Exterior.CommonScheduledTrace.CommonBasisRequest.Sampled.periodTraceAt
        samples.1 stage) ::
        periodValuesAt
        stage tail plans.2 readings.2 fans.2 samples.2

/-- Synchronized cached period values equal the original component period traces at the specified shared stage. -/
theorem periodValues_atStage (stage : Nat) {errorTarget : Normalization.InverseRootPolynomial.Coordinate} :
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
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceScheduled.Plans.Samples.AtStage stage entries plans
      readings fans samples comparisons scheduled →
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceScheduledEnergy.Plans.Samples.periodValues entries plans
      readings fans samples comparisons scheduled =
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceScheduledEnergy.Plans.Samples.periodValuesAt stage
      entries plans readings fans samples
  | [], _, _, _, _, _, _, _ => rfl
  | _ :: tail, plans, readings, fans, samples, comparisons, scheduled, synchronized =>
      congrArg₂ List.cons
        (congrArg Neg.neg (scheduled.1.period_eq.trans (congrArg
          (Hyperelliptic.Meshes.PuncturedGrid.Exterior.CommonScheduledTrace.CommonBasisRequest.Sampled.periodTraceAt
          samples.1) synchronized.1)))

          (periodValues_atStage
          stage tail plans.2 readings.2 fans.2 samples.2 comparisons.2 scheduled.2 synchronized.2)

/-- The difference of the two retained trace sums is the negated sum of their original component discrepancies. -/
theorem values_difference {errorTarget : Normalization.InverseRootPolynomial.Coordinate} :
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
    Data.Gaussian.Norm.Sum.Basic.gaussianSum
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceScheduledEnergy.Plans.Samples.sourceValues entries plans
      readings fans samples comparisons scheduled) -
      Data.Gaussian.Norm.Sum.Basic.gaussianSum
        (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceScheduledEnergy.Plans.Samples.periodValues entries
        plans readings fans samples comparisons scheduled) =
      -Data.Gaussian.Norm.Sum.Basic.gaussianSum
        (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceScheduled.Plans.Samples.scheduledErrors entries plans
        readings fans samples comparisons scheduled)
  | [], _, _, _, _, _, _ => by change (0 : Normalization.InverseRootPolynomial.Gaussian) - 0 = -0; ring1
  | _ :: tail, plans, readings, fans, samples, comparisons, scheduled => by
      have ih :=
        values_difference
        tail plans.2 readings.2 fans.2 samples.2 comparisons.2 scheduled.2
      change (-scheduled.1.source + Data.Gaussian.Norm.Sum.Basic.gaussianSum
        (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceScheduledEnergy.Plans.Samples.sourceValues tail
        plans.2 readings.2 fans.2 samples.2 comparisons.2 scheduled.2)) -
        (-scheduled.1.period + Data.Gaussian.Norm.Sum.Basic.gaussianSum
          (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceScheduledEnergy.Plans.Samples.periodValues tail
          plans.2 readings.2 fans.2 samples.2 comparisons.2 scheduled.2)) =
        -((scheduled.1.source - scheduled.1.period) + Data.Gaussian.Norm.Sum.Basic.gaussianSum
          (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceScheduled.Plans.Samples.scheduledErrors tail plans.2
          readings.2 fans.2 samples.2 comparisons.2 scheduled.2))
      rw [show (-scheduled.1.source + Data.Gaussian.Norm.Sum.Basic.gaussianSum
        (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceScheduledEnergy.Plans.Samples.sourceValues tail
        plans.2 readings.2 fans.2 samples.2 comparisons.2 scheduled.2)) -
        (-scheduled.1.period + Data.Gaussian.Norm.Sum.Basic.gaussianSum
          (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceScheduledEnergy.Plans.Samples.periodValues tail
          plans.2 readings.2 fans.2 samples.2 comparisons.2 scheduled.2)) =
        -(scheduled.1.source - scheduled.1.period) +
          (Data.Gaussian.Norm.Sum.Basic.gaussianSum
            (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceScheduledEnergy.Plans.Samples.sourceValues tail
            plans.2 readings.2 fans.2 samples.2 comparisons.2 scheduled.2) -
            Data.Gaussian.Norm.Sum.Basic.gaussianSum
              (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceScheduledEnergy.Plans.Samples.periodValues tail
              plans.2 readings.2 fans.2 samples.2 comparisons.2 scheduled.2)) by ring1, ih]
      ring1

/-- Bound the imaginary reading of all original source traces using their retained component returns.

The paid shared reading stage and branch condition give four local allowances per actual component, scaled by the common
coefficient norm. -/
theorem sourceLower (branch : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1)
  {errorTarget : Normalization.InverseRootPolynomial.Coordinate} :
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
    (traces : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfacePrepared.Plans.Samples.PreparedTraces entries
      plans readings fans samples comparisons) →
    (scheduled : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceScheduled.Plans.Samples.ScheduledComparisons
      errorTarget entries plans readings fans samples comparisons) →
    plans.stage entries ≤ readingIndex →
    -((entries.length : Normalization.InverseRootPolynomial.Coordinate) * (4 * target) *
      Readings.PreparedObservationCoercivity.coefficientNormSq coefficients) ≤
      (Data.Gaussian.Norm.Sum.Basic.gaussianSum
        (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceScheduledEnergy.Plans.Samples.sourceValues entries
        plans readings fans samples comparisons scheduled)).im / 4
  | [], _, _, _, _, _, _, _, _ => by
      change -(0 * (4 * target) * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients) ≤ 0 / 4
      exact (show -(0 * (4 * target) * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients) = (0 :
        Normalization.InverseRootPolynomial.Coordinate) / 4 by
        simp only [Fraction.Field.div_eq_mul_inv_direct]; ring1).le
  | head :: tail, plans, readings, fans, samples, comparisons, traces, scheduled, later => by
      have first :=
        Hyperelliptic.Meshes.PuncturedGrid.Exterior.CommonScheduledTrace.CommonBasisRequest.Sampled.source_lower
        samples.1 comparisons.1 traces.1 branch
        (plans.1.stage_eq.symm.trans_le ((Data.Nat.Order.le_max_left ..).trans later)) scheduled.1.stage
      rw [← scheduled.1.source_eq] at first
      have bounded := Fraction.Order.Arithmetic.add_le_add_direct first

          (sourceLower
          branch tail plans.2 readings.2 fans.2 samples.2 comparisons.2 traces.2 scheduled.2
          ((Data.Nat.Order.le_max_right ..).trans later))
      have left : -(((head :: tail).length : Normalization.InverseRootPolynomial.Coordinate) * (4 * target) *
        Readings.PreparedObservationCoercivity.coefficientNormSq coefficients) =
          -(4 * target * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients) -
            ((tail.length : Normalization.InverseRootPolynomial.Coordinate) * (4 * target) *
              Readings.PreparedObservationCoercivity.coefficientNormSq coefficients) := by
        simp only [List.length_cons, Fraction.Cast.natCast_add_direct, Nat.cast_one]
        ring1
      rw [left]
      apply bounded.trans_eq
      change (-scheduled.1.source).im / 4 +
        (Data.Gaussian.Norm.Sum.Basic.gaussianSum
          (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceScheduledEnergy.Plans.Samples.sourceValues tail
          plans.2 readings.2 fans.2 samples.2 comparisons.2 scheduled.2)).im / 4 =
        ((-scheduled.1.source) + Data.Gaussian.Norm.Sum.Basic.gaussianSum
          (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceScheduledEnergy.Plans.Samples.sourceValues tail
          plans.2 readings.2 fans.2 samples.2 comparisons.2 scheduled.2)).im / 4
      rw [Gaussian.Basic.add_im]
      simp only [Fraction.Field.div_eq_mul_inv_direct]
      ring1

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

/-- The common surface allocation pays the source lower bound, with all
components and their retained root returns included. -/
theorem source_lower (comparisons :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceScheduled.ScheduledRequest.Comparisons scheduled acquired
  evaluation)
    (branch : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1) :
    -(target * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients) ≤
      (Data.Gaussian.Norm.Sum.Basic.gaussianSum
        (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceScheduledEnergy.Plans.Samples.sourceValues
        scheduled.request.entries acquired.plans acquired.readings acquired.fans
        evaluation.samples evaluation.comparisons comparisons)).im / 4 := open Purelib.Algebra in by
  have lower := Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceScheduledEnergy.Plans.Samples.sourceLower
    branch scheduled.request.entries acquired.plans acquired.readings acquired.fans
    evaluation.samples evaluation.comparisons evaluation.traces comparisons acquired.reading_eq.symm.le
  have paid : (scheduled.request.entries.length : Normalization.InverseRootPolynomial.Coordinate) * (4 *
    scheduled.request.localTarget) ≤ target := by
    rw [scheduled.request.entries_length]
    exact (show (prepared.components.length : Normalization.InverseRootPolynomial.Coordinate) * (4 *
      scheduled.request.localTarget) =
      (4 * (prepared.components.length : Normalization.InverseRootPolynomial.Coordinate)) *
        scheduled.request.localTarget by ring1).trans_le scheduled.request.paid
  have nonnegative : 0 ≤ Readings.PreparedObservationCoercivity.coefficientNormSq coefficients :=
    FiniteSum.Fin.sumFin_zero.symm.trans_le
    (FiniteSum.Rational.Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 :
      Normalization.InverseRootPolynomial.Coordinate)) _ (fun row => Gaussian.Basic.Canonical.normSq_nonneg
      (coefficients row)))
  exact (Fraction.Order.Arithmetic.neg_le_neg_direct (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct paid
    nonnegative)).trans lower

/-- The paired cached source and period totals carry the same aggregate
error certificate as the component errors. -/
theorem totals_error (comparisons :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceScheduled.ScheduledRequest.Comparisons scheduled acquired
  evaluation) :
    Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceScheduledEnergy.Plans.Samples.sourceValues
      scheduled.request.entries acquired.plans acquired.readings acquired.fans
      evaluation.samples evaluation.comparisons comparisons) -
      Data.Gaussian.Norm.Sum.Basic.gaussianSum
        (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceScheduledEnergy.Plans.Samples.periodValues
        scheduled.request.entries acquired.plans acquired.readings acquired.fans
        evaluation.samples evaluation.comparisons comparisons)) ≤ errorTarget *
          Readings.PreparedObservationCoercivity.coefficientNormSq coefficients ^ 2 := by
  rw [Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceScheduledEnergy.Plans.Samples.values_difference,
    Gaussian.Norm.Basic.normSq_neg]
  exact Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceScheduled.ScheduledRequest.source_error_bound scheduled
    acquired evaluation comparisons

/-- A squared trace-error request transfers the lower bound to the retained
period totals. Component stages are still those in the cached comparisons. -/
theorem period_lower {errorAllowance : Normalization.InverseRootPolynomial.Coordinate} (errorNonnegative : 0 ≤
  errorAllowance)
    (request : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceTraceRequest.ScheduledRequest prepared basis
      target (errorAllowance ^ 2) floor)
    (acquired : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceEnergy.Request.Acquisition request.request
      capSample polynomials minimum energyFloor)
    (evaluation : acquired.Evaluation coefficients)
    (comparisons : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceScheduled.ScheduledRequest.Comparisons
      request acquired evaluation)
    (branch : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1) :
    -((target + errorAllowance) * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients) ≤
      (Data.Gaussian.Norm.Sum.Basic.gaussianSum
        (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceScheduledEnergy.Plans.Samples.periodValues
        request.request.entries acquired.plans acquired.readings acquired.fans
        evaluation.samples evaluation.comparisons comparisons)).im / 4 := open Purelib.Algebra in by
  let source := Data.Gaussian.Norm.Sum.Basic.gaussianSum
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceScheduledEnergy.Plans.Samples.sourceValues
    request.request.entries acquired.plans acquired.readings acquired.fans
    evaluation.samples evaluation.comparisons comparisons)
  let period := Data.Gaussian.Norm.Sum.Basic.gaussianSum
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceScheduledEnergy.Plans.Samples.periodValues
    request.request.entries acquired.plans acquired.readings acquired.fans
    evaluation.samples evaluation.comparisons comparisons)
  have normNonnegative : 0 ≤ Readings.PreparedObservationCoercivity.coefficientNormSq coefficients :=
    FiniteSum.Fin.sumFin_zero.symm.trans_le
    (FiniteSum.Rational.Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 :
      Normalization.InverseRootPolynomial.Coordinate)) _ (fun row => Gaussian.Basic.Canonical.normSq_nonneg
      (coefficients row)))
  have error : Data.Gaussian.Norm.Basic.normSq (source - period) ≤ (4 * (errorAllowance *
    Readings.PreparedObservationCoercivity.coefficientNormSq coefficients))^2 :=
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceScheduledEnergy.ScheduledRequest.totals_error request
      acquired evaluation comparisons).trans
      ((show errorAllowance^2 * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients ^ 2 =
        1 * (errorAllowance * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)^2 by
          ring1).trans_le
        ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (by decide : (1 :
          Normalization.InverseRootPolynomial.Coordinate) ≤ 16) (Fraction.Order.Arithmetic.sq_nonneg_direct _)).trans_eq
          (by ring1)))
  have comparison := Topology.PreparedSurfaceCoercivity.boundaryEnergy_sub_budget_le source period
    (errorAllowance * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)
      (Fraction.Order.Arithmetic.mul_nonneg_direct errorNonnegative normNonnegative) error
  exact (show -((target + errorAllowance) * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients) =
    -(target * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients) - errorAllowance *
      Readings.PreparedObservationCoercivity.coefficientNormSq coefficients by ring1).trans_le
      ((Fraction.Order.Arithmetic.sub_le_sub_right_direct
        (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceScheduledEnergy.ScheduledRequest.source_lower request
        acquired evaluation comparisons branch)
        (errorAllowance * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)).trans comparison)

/-- The lower bound holds on literal component period traces at the common
retained stage, rather than on an unrelated collection of sample indices. -/
theorem synchronized_period_lower {errorAllowance : Normalization.InverseRootPolynomial.Coordinate} (errorNonnegative :
  0 ≤ errorAllowance)
    (request : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceTraceRequest.ScheduledRequest prepared basis
      target (errorAllowance ^ 2) floor)
    (acquired : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceEnergy.Request.Acquisition request.request
      capSample polynomials minimum energyFloor)
    (evaluation : acquired.Evaluation coefficients)
    (synchronized :
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceScheduled.ScheduledRequest.SynchronizedComparisons
      request acquired evaluation)
    (branch : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1) :
    -((target + errorAllowance) * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients) ≤
      (Data.Gaussian.Norm.Sum.Basic.gaussianSum
        (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceScheduledEnergy.Plans.Samples.periodValuesAt
        (synchronized.predecessor + 1) request.request.entries
        acquired.plans acquired.readings acquired.fans evaluation.samples)).im / 4 := by
  rw [← Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceScheduledEnergy.Plans.Samples.periodValues_atStage _ _
    _ _ _ _ _ synchronized.comparisons synchronized.atStage]
  exact Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceScheduledEnergy.ScheduledRequest.period_lower
    errorNonnegative request acquired evaluation synchronized.comparisons branch

end ScheduledRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceScheduledEnergy
