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
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceScheduled
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceTraceRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceScheduledEnergy
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CommonSourceArea
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Connection
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CommonPreparedComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CommonScheduledTrace
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

/-! Sum centered common-source polygon bounds without discarding return ribbons. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceSourceArea

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

/-- Read each original component's negated centered source area at its retained scheduled stage. -/
def sourceAreaValues {errorTarget : Normalization.InverseRootPolynomial.Coordinate} :
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
      (-Hyperelliptic.Meshes.PuncturedGrid.Exterior.CommonSourceArea.CommonBasisRequest.Sampled.sourceAreaAt samples.1
        comparisons.1 scheduled.1.stage) ::
        sourceAreaValues
        tail plans.2 readings.2 fans.2 samples.2 comparisons.2 scheduled.2

/-- Bound the imaginary reading of the complete retained source-area sum.

The actual component count pays five local allowances per component, including centering, at the shared paid reading
stage. -/
theorem sourceAreaLower (branch : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1)
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
    -((entries.length : Normalization.InverseRootPolynomial.Coordinate) * (5 * target) *
      Readings.PreparedObservationCoercivity.coefficientNormSq coefficients) ≤
      (Data.Gaussian.Norm.Sum.Basic.gaussianSum
        (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceSourceArea.Plans.Samples.sourceAreaValues entries
        plans readings fans samples comparisons scheduled)).im / 4
  | [], _, _, _, _, _, _, _, _ => by
      change -(0 * (5 * target) * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients) ≤ 0 / 4
      exact (show -(0 * (5 * target) * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients) = (0 :
        Normalization.InverseRootPolynomial.Coordinate) / 4 by
        simp only [Fraction.Field.div_eq_mul_inv_direct]; ring1).le
  | head :: tail, plans, readings, fans, samples, comparisons, traces, scheduled, later => by
      have first :=
        Hyperelliptic.Meshes.PuncturedGrid.Exterior.CommonSourceArea.CommonBasisRequest.Sampled.source_area_lower
        samples.1 comparisons.1 traces.1 branch
        (plans.1.stage_eq.symm.trans_le ((Data.Nat.Order.le_max_left ..).trans later)) scheduled.1.stage
      have bounded := Fraction.Order.Arithmetic.add_le_add_direct first

          (sourceAreaLower
          branch tail plans.2 readings.2 fans.2 samples.2 comparisons.2 traces.2 scheduled.2
          ((Data.Nat.Order.le_max_right ..).trans later))
      have left : -(((head :: tail).length : Normalization.InverseRootPolynomial.Coordinate) * (5 * target) *
        Readings.PreparedObservationCoercivity.coefficientNormSq coefficients) =
          -(5 * target * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients) -
            ((tail.length : Normalization.InverseRootPolynomial.Coordinate) * (5 * target) *
              Readings.PreparedObservationCoercivity.coefficientNormSq coefficients) := by
        simp only [List.length_cons, Fraction.Cast.natCast_add_direct, Nat.cast_one]
        ring1
      rw [left]
      apply bounded.trans_eq
      change (-Hyperelliptic.Meshes.PuncturedGrid.Exterior.CommonSourceArea.CommonBasisRequest.Sampled.sourceAreaAt
        samples.1 comparisons.1 scheduled.1.stage).im / 4 +
        (Data.Gaussian.Norm.Sum.Basic.gaussianSum
          (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceSourceArea.Plans.Samples.sourceAreaValues tail
          plans.2 readings.2 fans.2 samples.2 comparisons.2 scheduled.2)).im / 4 =
        ((-Hyperelliptic.Meshes.PuncturedGrid.Exterior.CommonSourceArea.CommonBasisRequest.Sampled.sourceAreaAt
          samples.1 comparisons.1 scheduled.1.stage) + Data.Gaussian.Norm.Sum.Basic.gaussianSum
          (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceSourceArea.Plans.Samples.sourceAreaValues tail
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

/-- Centering retains the extra quarter of the requested surface allowance;
all components and their complete source polygons remain in the sum. -/
theorem source_area_lower (comparisons :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceScheduled.ScheduledRequest.Comparisons scheduled acquired
  evaluation)
    (branch : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1) :
    -((5 / 4 * target) * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients) ≤
      (Data.Gaussian.Norm.Sum.Basic.gaussianSum
        (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceSourceArea.Plans.Samples.sourceAreaValues
        scheduled.request.entries acquired.plans acquired.readings acquired.fans
        evaluation.samples evaluation.comparisons comparisons)).im / 4 := open Purelib.Algebra in by
  have lower := Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceSourceArea.Plans.Samples.sourceAreaLower branch
    scheduled.request.entries acquired.plans acquired.readings acquired.fans
    evaluation.samples evaluation.comparisons evaluation.traces comparisons acquired.reading_eq.symm.le
  have tracePaid : (scheduled.request.entries.length : Normalization.InverseRootPolynomial.Coordinate) * (4 *
    scheduled.request.localTarget) ≤ target := by
    rw [scheduled.request.entries_length]
    exact (show (prepared.components.length : Normalization.InverseRootPolynomial.Coordinate) * (4 *
      scheduled.request.localTarget) =
      (4 * (prepared.components.length : Normalization.InverseRootPolynomial.Coordinate)) *
        scheduled.request.localTarget by ring1).trans_le scheduled.request.paid
  have paid : (scheduled.request.entries.length : Normalization.InverseRootPolynomial.Coordinate) * (5 *
    scheduled.request.localTarget) ≤ 5 / 4 * target := by
    have scaled := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct tracePaid (by
        decide +kernel : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 5 / 4)
    exact (show (scheduled.request.entries.length : Normalization.InverseRootPolynomial.Coordinate) * (5 *
      scheduled.request.localTarget) =
      5 / 4 * ((scheduled.request.entries.length : Normalization.InverseRootPolynomial.Coordinate) * (4 *
        scheduled.request.localTarget)) by
        calc
          _ = 5 * ((scheduled.request.entries.length : Normalization.InverseRootPolynomial.Coordinate) *
            scheduled.request.localTarget) := by
            ring1
          _ = ((5 / 4 : Normalization.InverseRootPolynomial.Coordinate) * 4) * ((scheduled.request.entries.length :
            Normalization.InverseRootPolynomial.Coordinate) * scheduled.request.localTarget) :=
            congrArg (fun scalar => scalar * ((scheduled.request.entries.length :
              Normalization.InverseRootPolynomial.Coordinate) * scheduled.request.localTarget))
              (by decide +kernel : (5 : Normalization.InverseRootPolynomial.Coordinate) = (5 / 4) * 4)
          _ = _ := by ring1).trans_le scaled
  have nonnegative : 0 ≤ Readings.PreparedObservationCoercivity.coefficientNormSq coefficients :=
    FiniteSum.Fin.sumFin_zero.symm.trans_le
    (FiniteSum.Rational.Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 :
      Normalization.InverseRootPolynomial.Coordinate)) _ (fun row => Gaussian.Basic.Canonical.normSq_nonneg
      (coefficients row)))
  exact (Fraction.Order.Arithmetic.neg_le_neg_direct (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct paid
    nonnegative)).trans lower

end ScheduledRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceSourceArea
