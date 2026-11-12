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

open Purelib.Data.Rat.Fraction.Order

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfacePrepared.Plans

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceScheduled

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

variable {genus : Nat} {curve : Basic.HyperellipticCurve genus} {branches :
  Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential : Differentials.Basic.Differential genus}
  {collar : Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {bounds : Charts.Reciprocal.ReciprocalPaddedInverse.UniformBounds regular.padded}

variable {basis : Charts.Reciprocal.ReciprocalPaddedBasisBounds.BasisBounds bounds}
  {target coefficientTarget : InverseRootPolynomial.Coordinate} {coverFloor floor index minimum
    readingIndex : Nat}
  {box : Rational.Box} {capSample : Charts.Reciprocal.Cap.Primitives.Sample cap
    differential index box}
  {polynomials : CapBasisEnergy.RegularBasisPolynomials cap index box}

variable {energyFloor radialDepth : Nat}
  {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}

open Purelib.Data.Gaussian.Basic.Canonical

namespace Plans.Samples

/-- Read the negated original source traces in retained component order. -/
def sourceValues {errorTarget : InverseRootPolynomial.Coordinate} :
    (entries : List (SurfaceRequest.Entry (domains := domains)
      (differential := differential) basis target coefficientTarget coverFloor floor)) →
    (plans : SurfacePlans.Plans capSample polynomials minimum entries)
      → (readings : SurfacePlans.Plans.Readings entries plans
      readingIndex) →
    (fans : SurfaceSamples.Plans.FanPreparations energyFloor entries
      plans readings) →
    (samples : SurfaceSamples.Plans.Samples coefficients radialDepth
      entries plans readings fans) →
    (comparisons : Samples.PreparedComparisons
      entries plans readings fans samples) →
    Plans.Samples.ScheduledComparisons errorTarget
      entries plans readings fans samples comparisons → List InverseRootPolynomial.Gaussian
  | [], _, _, _, _, _, _ => []
  | _ :: tail, plans, readings, fans, samples, comparisons, scheduled =>
      (-scheduled.1.source) ::
        sourceValues
        tail plans.2 readings.2 fans.2 samples.2 comparisons.2 scheduled.2

/-- Read the negated original period traces in retained component order. -/
def periodValues {errorTarget : InverseRootPolynomial.Coordinate} :
    (entries : List (SurfaceRequest.Entry (domains := domains)
      (differential := differential) basis target coefficientTarget coverFloor floor)) →
    (plans : SurfacePlans.Plans capSample polynomials minimum entries)
      → (readings : SurfacePlans.Plans.Readings entries plans
      readingIndex) →
    (fans : SurfaceSamples.Plans.FanPreparations energyFloor entries
      plans readings) →
    (samples : SurfaceSamples.Plans.Samples coefficients radialDepth
      entries plans readings fans) →
    (comparisons : Samples.PreparedComparisons
      entries plans readings fans samples) →
    Plans.Samples.ScheduledComparisons errorTarget
      entries plans readings fans samples comparisons → List InverseRootPolynomial.Gaussian
  | [], _, _, _, _, _, _ => []
  | _ :: tail, plans, readings, fans, samples, comparisons, scheduled =>
      (-scheduled.1.period) ::
        periodValues
        tail plans.2 readings.2 fans.2 samples.2 comparisons.2 scheduled.2

/-- Read the actual period trace of every component at one original stage. -/
def periodValuesAt (stage : Nat) :
    (entries : List (SurfaceRequest.Entry (domains := domains)
      (differential := differential) basis target coefficientTarget coverFloor floor)) →
    (plans : SurfacePlans.Plans capSample polynomials minimum entries)
      → (readings : SurfacePlans.Plans.Readings entries plans
      readingIndex) →
    (fans : SurfaceSamples.Plans.FanPreparations energyFloor entries
      plans readings) →
    (samples : SurfaceSamples.Plans.Samples coefficients radialDepth
      entries plans readings fans) →
    List InverseRootPolynomial.Gaussian
  | [], _, _, _, _ => []
  | _ :: tail, plans, readings, fans, samples =>
      (-CommonScheduledTrace.CommonBasisRequest.Sampled.periodTraceAt
        samples.1 stage) ::
        periodValuesAt
        stage tail plans.2 readings.2 fans.2 samples.2

/-- Synchronized cached period values equal the original component period traces at the specified shared stage. -/
theorem periodValues_atStage (stage : Nat) {errorTarget : InverseRootPolynomial.Coordinate} :
    (entries : List (SurfaceRequest.Entry (domains := domains)
      (differential := differential) basis target coefficientTarget coverFloor floor)) →
    (plans : SurfacePlans.Plans capSample polynomials minimum entries)
      → (readings : SurfacePlans.Plans.Readings entries plans
      readingIndex) →
    (fans : SurfaceSamples.Plans.FanPreparations energyFloor entries
      plans readings) →
    (samples : SurfaceSamples.Plans.Samples coefficients radialDepth
      entries plans readings fans) →
    (comparisons : Samples.PreparedComparisons
      entries plans readings fans samples) →
    (scheduled : Plans.Samples.ScheduledComparisons
      errorTarget entries plans readings fans samples comparisons) →
    Plans.Samples.AtStage stage entries plans
      readings fans samples comparisons scheduled →
    Samples.periodValues entries plans
      readings fans samples comparisons scheduled =
      Samples.periodValuesAt stage
      entries plans readings fans samples
  | [], _, _, _, _, _, _, _ => rfl
  | _ :: tail, plans, readings, fans, samples, comparisons, scheduled, synchronized =>
      congrArg₂ List.cons
        (congrArg Neg.neg (scheduled.1.period_eq.trans (congrArg
          (CommonScheduledTrace.CommonBasisRequest.Sampled.periodTraceAt
          samples.1) synchronized.1)))

          (periodValues_atStage
          stage tail plans.2 readings.2 fans.2 samples.2 comparisons.2 scheduled.2 synchronized.2)

/-- The difference of the two retained trace sums is the negated sum of their original component discrepancies. -/
theorem values_difference {errorTarget : InverseRootPolynomial.Coordinate} :
    (entries : List (SurfaceRequest.Entry (domains := domains)
      (differential := differential) basis target coefficientTarget coverFloor floor)) →
    (plans : SurfacePlans.Plans capSample polynomials minimum entries)
      → (readings : SurfacePlans.Plans.Readings entries plans
      readingIndex) →
    (fans : SurfaceSamples.Plans.FanPreparations energyFloor entries
      plans readings) →
    (samples : SurfaceSamples.Plans.Samples coefficients radialDepth
      entries plans readings fans) →
    (comparisons : Samples.PreparedComparisons
      entries plans readings fans samples) →
    (scheduled : Plans.Samples.ScheduledComparisons
      errorTarget entries plans readings fans samples comparisons) →
    Gaussian.Norm.Sum.Basic.gaussianSum
      (Samples.sourceValues entries plans
      readings fans samples comparisons scheduled) -
      Gaussian.Norm.Sum.Basic.gaussianSum
        (Samples.periodValues entries
        plans readings fans samples comparisons scheduled) =
      -Gaussian.Norm.Sum.Basic.gaussianSum
        (Plans.Samples.scheduledErrors entries plans
        readings fans samples comparisons scheduled)
  | [], _, _, _, _, _, _ => by change (0 : InverseRootPolynomial.Gaussian) - 0 = -0; ring1
  | _ :: tail, plans, readings, fans, samples, comparisons, scheduled => by
      have ih :=
        values_difference
        tail plans.2 readings.2 fans.2 samples.2 comparisons.2 scheduled.2
      change (-scheduled.1.source + Gaussian.Norm.Sum.Basic.gaussianSum
        (Samples.sourceValues tail
        plans.2 readings.2 fans.2 samples.2 comparisons.2 scheduled.2)) -
        (-scheduled.1.period + Gaussian.Norm.Sum.Basic.gaussianSum
          (Samples.periodValues tail
          plans.2 readings.2 fans.2 samples.2 comparisons.2 scheduled.2)) =
        -((scheduled.1.source - scheduled.1.period) + Gaussian.Norm.Sum.Basic.gaussianSum
          (Plans.Samples.scheduledErrors tail plans.2
          readings.2 fans.2 samples.2 comparisons.2 scheduled.2))
      rw [show (-scheduled.1.source + Gaussian.Norm.Sum.Basic.gaussianSum
        (Samples.sourceValues tail
        plans.2 readings.2 fans.2 samples.2 comparisons.2 scheduled.2)) -
        (-scheduled.1.period + Gaussian.Norm.Sum.Basic.gaussianSum
          (Samples.periodValues tail
          plans.2 readings.2 fans.2 samples.2 comparisons.2 scheduled.2)) =
        -(scheduled.1.source - scheduled.1.period) +
          (Gaussian.Norm.Sum.Basic.gaussianSum
            (Samples.sourceValues tail
            plans.2 readings.2 fans.2 samples.2 comparisons.2 scheduled.2) -
            Gaussian.Norm.Sum.Basic.gaussianSum
              (Samples.periodValues tail
              plans.2 readings.2 fans.2 samples.2 comparisons.2 scheduled.2)) by ring1, ih]
      ring1

/-- Bound the imaginary reading of all original source traces using their retained component returns.

The paid shared reading stage and branch condition give four local allowances per actual component, scaled by the common
coefficient norm. -/
theorem sourceLower (branch : Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1)
  {errorTarget : InverseRootPolynomial.Coordinate} :
    (entries : List (SurfaceRequest.Entry (domains := domains)
      (differential := differential) basis target coefficientTarget coverFloor floor)) →
    (plans : SurfacePlans.Plans capSample polynomials minimum entries)
      → (readings : SurfacePlans.Plans.Readings entries plans
      readingIndex) →
    (fans : SurfaceSamples.Plans.FanPreparations energyFloor entries
      plans readings) →
    (samples : SurfaceSamples.Plans.Samples coefficients radialDepth
      entries plans readings fans) →
    (comparisons : Samples.PreparedComparisons
      entries plans readings fans samples) →
    (traces : Samples.PreparedTraces entries
      plans readings fans samples comparisons) →
    (scheduled : Plans.Samples.ScheduledComparisons
      errorTarget entries plans readings fans samples comparisons) →
    plans.stage entries ≤ readingIndex →
    -((entries.length : InverseRootPolynomial.Coordinate) * (4 * target) *
      Readings.PreparedObservationCoercivity.coefficientNormSq coefficients) ≤
      (Gaussian.Norm.Sum.Basic.gaussianSum
        (Samples.sourceValues entries
        plans readings fans samples comparisons scheduled)).im / 4
  | [], _, _, _, _, _, _, _, _ => by
      change -(0 * (4 * target) * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients) ≤ 0 / 4
      exact (show -(0 * (4 * target) * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients) = (0 :
        InverseRootPolynomial.Coordinate) / 4 by
        simp only [Fraction.Field.div_eq_mul_inv_direct]; ring1).le
  | head :: tail, plans, readings, fans, samples, comparisons, traces, scheduled, later => by
      have first :=
        CommonScheduledTrace.CommonBasisRequest.Sampled.source_lower
        samples.1 comparisons.1 traces.1 branch
        (plans.1.stage_eq.symm.trans_le ((Nat.Order.le_max_left ..).trans later)) scheduled.1.stage
      rw [← scheduled.1.source_eq] at first
      have bounded := Arithmetic.add_le_add_direct first

          (sourceLower
          branch tail plans.2 readings.2 fans.2 samples.2 comparisons.2 traces.2 scheduled.2
          ((Nat.Order.le_max_right ..).trans later))
      have left : -(((head :: tail).length : InverseRootPolynomial.Coordinate) * (4 * target) *
        Readings.PreparedObservationCoercivity.coefficientNormSq coefficients) =
          -(4 * target * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients) -
            ((tail.length : InverseRootPolynomial.Coordinate) * (4 * target) *
              Readings.PreparedObservationCoercivity.coefficientNormSq coefficients) := by
        simp only [List.length_cons, Fraction.Cast.natCast_add_direct, Nat.cast_one]
        ring1
      rw [left]
      apply bounded.trans_eq
      change (-scheduled.1.source).im / 4 +
        (Gaussian.Norm.Sum.Basic.gaussianSum
          (Samples.sourceValues tail
          plans.2 readings.2 fans.2 samples.2 comparisons.2 scheduled.2)).im / 4 =
        ((-scheduled.1.source) + Gaussian.Norm.Sum.Basic.gaussianSum
          (Samples.sourceValues tail
          plans.2 readings.2 fans.2 samples.2 comparisons.2 scheduled.2)).im / 4
      rw [Gaussian.Basic.add_im]
      simp only [Fraction.Field.div_eq_mul_inv_direct]
      ring1

end Plans.Samples

namespace ScheduledRequest

variable {prepared :
  SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
  regular domains differential} {errorTarget : InverseRootPolynomial.Coordinate}
  (scheduled : SurfaceTraceRequest.ScheduledRequest prepared basis
    target errorTarget floor)
  (acquired : SurfaceEnergy.Request.Acquisition scheduled.request
    capSample polynomials minimum energyFloor)
  (evaluation : acquired.Evaluation coefficients)

/-- The common surface allocation pays the source lower bound, with all
components and their retained root returns included. -/
theorem source_lower (comparisons :
  ScheduledRequest.Comparisons scheduled acquired
  evaluation)
    (branch : Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1) :
    -(target * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients) ≤
      (Gaussian.Norm.Sum.Basic.gaussianSum
        (Plans.Samples.sourceValues
        scheduled.request.entries acquired.plans acquired.readings acquired.fans
        evaluation.samples evaluation.comparisons comparisons)).im / 4 := open Algebra in by
  have lower := Plans.Samples.sourceLower
    branch scheduled.request.entries acquired.plans acquired.readings acquired.fans
    evaluation.samples evaluation.comparisons evaluation.traces comparisons acquired.reading_eq.symm.le
  have paid : (scheduled.request.entries.length : InverseRootPolynomial.Coordinate) * (4 *
    scheduled.request.localTarget) ≤ target := by
    rw [scheduled.request.entries_length]
    exact (show (prepared.components.length : InverseRootPolynomial.Coordinate) * (4 *
      scheduled.request.localTarget) =
      (4 * (prepared.components.length : InverseRootPolynomial.Coordinate)) *
        scheduled.request.localTarget by ring1).trans_le scheduled.request.paid
  have nonnegative : 0 ≤ Readings.PreparedObservationCoercivity.coefficientNormSq coefficients :=
    FiniteSum.Fin.sumFin_zero.symm.trans_le
    (FiniteSum.Rational.Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 :
      InverseRootPolynomial.Coordinate)) _ (fun row => Gaussian.Basic.Canonical.normSq_nonneg
      (coefficients row)))
  exact (Arithmetic.neg_le_neg_direct (Arithmetic.mul_le_mul_of_nonneg_right_direct paid
    nonnegative)).trans lower

/-- The paired cached source and period totals carry the same aggregate
error certificate as the component errors. -/
theorem totals_error (comparisons :
  ScheduledRequest.Comparisons scheduled acquired
  evaluation) :
    Gaussian.Norm.Basic.normSq (Gaussian.Norm.Sum.Basic.gaussianSum
      (Plans.Samples.sourceValues
      scheduled.request.entries acquired.plans acquired.readings acquired.fans
      evaluation.samples evaluation.comparisons comparisons) -
      Gaussian.Norm.Sum.Basic.gaussianSum
        (Plans.Samples.periodValues
        scheduled.request.entries acquired.plans acquired.readings acquired.fans
        evaluation.samples evaluation.comparisons comparisons)) ≤ errorTarget *
          Readings.PreparedObservationCoercivity.coefficientNormSq coefficients ^ 2 := by
  rw [Plans.Samples.values_difference,
    Gaussian.Norm.Basic.normSq_neg]
  exact ScheduledRequest.source_error_bound scheduled
    acquired evaluation comparisons

/-- A squared trace-error request transfers the lower bound to the retained
period totals. Component stages are still those in the cached comparisons. -/
theorem period_lower {errorAllowance : InverseRootPolynomial.Coordinate} (errorNonnegative : 0 ≤
  errorAllowance)
    (request : SurfaceTraceRequest.ScheduledRequest prepared basis
      target (errorAllowance ^ 2) floor)
    (acquired : SurfaceEnergy.Request.Acquisition request.request
      capSample polynomials minimum energyFloor)
    (evaluation : acquired.Evaluation coefficients)
    (comparisons : ScheduledRequest.Comparisons
      request acquired evaluation)
    (branch : Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1) :
    -((target + errorAllowance) * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients) ≤
      (Gaussian.Norm.Sum.Basic.gaussianSum
        (Plans.Samples.periodValues
        request.request.entries acquired.plans acquired.readings acquired.fans
        evaluation.samples evaluation.comparisons comparisons)).im / 4 := open Algebra in by
  let source := Gaussian.Norm.Sum.Basic.gaussianSum
    (Plans.Samples.sourceValues
    request.request.entries acquired.plans acquired.readings acquired.fans
    evaluation.samples evaluation.comparisons comparisons)
  let period := Gaussian.Norm.Sum.Basic.gaussianSum
    (Plans.Samples.periodValues
    request.request.entries acquired.plans acquired.readings acquired.fans
    evaluation.samples evaluation.comparisons comparisons)
  have normNonnegative : 0 ≤ Readings.PreparedObservationCoercivity.coefficientNormSq coefficients :=
    FiniteSum.Fin.sumFin_zero.symm.trans_le
    (FiniteSum.Rational.Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 :
      InverseRootPolynomial.Coordinate)) _ (fun row => Gaussian.Basic.Canonical.normSq_nonneg
      (coefficients row)))
  have error : Gaussian.Norm.Basic.normSq (source - period) ≤ (4 * (errorAllowance *
    Readings.PreparedObservationCoercivity.coefficientNormSq coefficients))^2 :=
    (ScheduledRequest.totals_error request
      acquired evaluation comparisons).trans
      ((show errorAllowance^2 * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients ^ 2 =
        1 * (errorAllowance * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)^2 by
          ring1).trans_le
        ((Arithmetic.mul_le_mul_of_nonneg_right_direct (by decide : (1 :
          InverseRootPolynomial.Coordinate) ≤ 16) (Arithmetic.sq_nonneg_direct _)).trans_eq
          (by ring1)))
  have comparison := Topology.PreparedSurfaceCoercivity.boundaryEnergy_sub_budget_le source period
    (errorAllowance * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)
      (Arithmetic.mul_nonneg_direct errorNonnegative normNonnegative) error
  exact (show -((target + errorAllowance) * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients) =
    -(target * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients) - errorAllowance *
      Readings.PreparedObservationCoercivity.coefficientNormSq coefficients by ring1).trans_le
      ((Arithmetic.sub_le_sub_right_direct
        (ScheduledRequest.source_lower request
        acquired evaluation comparisons branch)
        (errorAllowance * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)).trans comparison)

/-- The lower bound holds on literal component period traces at the common
retained stage, rather than on an unrelated collection of sample indices. -/
theorem synchronized_period_lower {errorAllowance : InverseRootPolynomial.Coordinate} (errorNonnegative :
  0 ≤ errorAllowance)
    (request : SurfaceTraceRequest.ScheduledRequest prepared basis
      target (errorAllowance ^ 2) floor)
    (acquired : SurfaceEnergy.Request.Acquisition request.request
      capSample polynomials minimum energyFloor)
    (evaluation : acquired.Evaluation coefficients)
    (synchronized :
      ScheduledRequest.SynchronizedComparisons
      request acquired evaluation)
    (branch : Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1) :
    -((target + errorAllowance) * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients) ≤
      (Gaussian.Norm.Sum.Basic.gaussianSum
        (Plans.Samples.periodValuesAt
        (synchronized.predecessor + 1) request.request.entries
        acquired.plans acquired.readings acquired.fans evaluation.samples)).im / 4 := by
  rw [← Plans.Samples.periodValues_atStage _ _
    _ _ _ _ _ synchronized.comparisons synchronized.atStage]
  exact ScheduledRequest.period_lower
    errorNonnegative request acquired evaluation synchronized.comparisons branch

end ScheduledRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceScheduledEnergy
