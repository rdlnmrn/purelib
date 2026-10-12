module
import Purelib.Data.Nat.Order
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction.Field
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
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedObservationCoercivity
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalSurfaceEnergy
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootBoundaryEnergy
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Connection
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalComponentEnergy
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

/-! Sum the root-corrected physical boundaries on the complete retained surface. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootSurfaceEnergy

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

/-- Each component must pay its own retained root-polygon comparison cost. -/
def RootPayments (requested rootAllowance : Normalization.InverseRootPolynomial.Coordinate) :
    (entries : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRequest.Entry (domains := domains)
      (differential := differential) basis target coefficientTarget coverFloor floor)) →
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfacePlans.Plans capSample polynomials minimum entries → Prop
  | [], _ => True
  | head :: tail, plans =>
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootBoundaryEnergy.CommonBasisRequest.Sampled.rootJoiningCost
        (request := head.request) (inputs := plans.1.inputs) requested ≤
        16 * rootAllowance^2 ∧
          Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootSurfaceEnergy.Plans.Samples.RootPayments
          requested rootAllowance tail plans.2

/-- Sum disconnected component boundaries without adding connectors between them. -/
def rootBoundaryValues {requested : Normalization.InverseRootPolynomial.Coordinate} :
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
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalSurfaceEnergy.Plans.Samples.PhysicalCertificates requested
      entries plans readings fans samples comparisons → List Normalization.InverseRootPolynomial.Gaussian
  | [], _, _, _, _, _, _ => []
  | _ :: tail, plans, readings, fans, samples, comparisons, physical =>

        (RootBoundaryEnergy.CommonBasisRequest.Sampled.PhysicalCertificate.rootBoundary
        physical.1) ::
        rootBoundaryValues
        tail plans.2 readings.2 fans.2 samples.2 comparisons.2 physical.2

/-- Both comparison allowances are homogeneous and charged once per component. -/
theorem rootUpper {requested physicalAllowance rootAllowance : Normalization.InverseRootPolynomial.Coordinate} (positive
  : 0 < requested)
    (physicalNN : 0 ≤ physicalAllowance) (rootNN : 0 ≤ rootAllowance)
    (physicalPaid : requested ≤ 16 * physicalAllowance ^ 2)
    (branch : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1) :
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
    (physical :
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalSurfaceEnergy.Plans.Samples.PhysicalCertificates
      requested entries plans readings fans samples comparisons) →
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootSurfaceEnergy.Plans.Samples.RootPayments requested
      rootAllowance entries plans → plans.stage entries ≤ readingIndex →
    (Data.Gaussian.Norm.Sum.Basic.gaussianSum
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootSurfaceEnergy.Plans.Samples.rootBoundaryValues entries
      plans readings fans samples comparisons physical)).im / 4 ≤
      ((entries.length : Normalization.InverseRootPolynomial.Coordinate) * (5 * target + physicalAllowance +
        rootAllowance)) * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients
  | [], _, _, _, _, _, _, _, _, _ => by
      change (0 : Normalization.InverseRootPolynomial.Coordinate) / 4 ≤ (0 * (5 * target + physicalAllowance +
        rootAllowance)) * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients
      exact (show (0 : Normalization.InverseRootPolynomial.Coordinate) / 4 = (0 * (5 * target + physicalAllowance +
        rootAllowance)) * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients by
        simp only [Fraction.Field.div_eq_mul_inv_direct]; ring1).le
  | head :: tail, plans, readings, fans, samples, comparisons, traces, physical, rootPaid, later => by
      have first :=
        RootBoundaryEnergy.CommonBasisRequest.Sampled.PhysicalCertificate.rootBoundary_upper
        physical.1 positive physicalNN rootNN physicalPaid rootPaid.1 traces.1 branch
        (plans.1.stage_eq.symm.trans_le ((Data.Nat.Order.le_max_left ..).trans later))
      have rest :=
        Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootSurfaceEnergy.Plans.Samples.rootUpper
        positive physicalNN rootNN physicalPaid branch tail plans.2 readings.2 fans.2 samples.2
        comparisons.2 traces.2 physical.2 rootPaid.2 ((Data.Nat.Order.le_max_right ..).trans later)
      have both := Fraction.Order.Arithmetic.add_le_add_direct first rest
      have split : (Data.Gaussian.Norm.Sum.Basic.gaussianSum
        (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootSurfaceEnergy.Plans.Samples.rootBoundaryValues (head ::
        tail) plans readings fans samples comparisons physical)).im / 4 =

            (RootBoundaryEnergy.CommonBasisRequest.Sampled.PhysicalCertificate.rootBoundary
            physical.1).im / 4 +
            (Data.Gaussian.Norm.Sum.Basic.gaussianSum
              (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootSurfaceEnergy.Plans.Samples.rootBoundaryValues tail
              plans.2 readings.2 fans.2 samples.2 comparisons.2 physical.2)).im / 4 := by
        change
          ((RootBoundaryEnergy.CommonBasisRequest.Sampled.PhysicalCertificate.rootBoundary
          physical.1) + _).im / 4 = _
        rw [Gaussian.Basic.add_im]
        simp only [Fraction.Field.div_eq_mul_inv_direct]
        ring1
      exact split.trans_le (both.trans_eq (by
        simp only [List.length_cons, Fraction.Cast.natCast_add_direct, Nat.cast_one]
        ring1))

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
  {requested allowance : Normalization.InverseRootPolynomial.Coordinate}
  (physical : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalSurfaceEnergy.Plans.Samples.PhysicalCertificates
    requested scheduled.request.entries acquired.plans acquired.readings
    acquired.fans evaluation.samples evaluation.comparisons)

/-- The complete physical upper bound pays the source estimate's explicit
five-quarter loss and both retained comparison allowances per component. -/
theorem root_boundary_energy_upper (positive : 0 < requested) (nonnegative : 0 ≤ allowance)
    (comparisonPaid : requested ≤ 16 * allowance ^ 2)
    {rootAllowance : Normalization.InverseRootPolynomial.Coordinate} (rootNN : 0 ≤ rootAllowance)
    (rootPaid : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootSurfaceEnergy.Plans.Samples.RootPayments requested
      rootAllowance scheduled.request.entries acquired.plans)
    (branch : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1) :
    (Data.Gaussian.Norm.Sum.Basic.gaussianSum
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootSurfaceEnergy.Plans.Samples.rootBoundaryValues
      scheduled.request.entries acquired.plans acquired.readings acquired.fans
      evaluation.samples evaluation.comparisons physical)).im / 4 ≤
      (5 / 4 * target + (scheduled.request.entries.length : Normalization.InverseRootPolynomial.Coordinate) * (allowance
        + rootAllowance)) * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients := open
        Purelib.Algebra in by
  have upper := Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootSurfaceEnergy.Plans.Samples.rootUpper positive
    nonnegative rootNN comparisonPaid branch scheduled.request.entries
    acquired.plans acquired.readings acquired.fans evaluation.samples evaluation.comparisons evaluation.traces physical
      rootPaid
    acquired.reading_eq.symm.le
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
  have massNN : 0 ≤ Readings.PreparedObservationCoercivity.coefficientNormSq coefficients :=
    FiniteSum.Fin.sumFin_zero.symm.trans_le
    (FiniteSum.Rational.Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 :
      Normalization.InverseRootPolynomial.Coordinate)) _
      (fun row => Gaussian.Basic.Canonical.normSq_nonneg (coefficients row)))
  exact upper.trans ((show ((scheduled.request.entries.length : Normalization.InverseRootPolynomial.Coordinate) *
    (5 * scheduled.request.localTarget + allowance + rootAllowance)) *
      Readings.PreparedObservationCoercivity.coefficientNormSq coefficients =
    ((scheduled.request.entries.length : Normalization.InverseRootPolynomial.Coordinate) * (5 *
      scheduled.request.localTarget) +
      (scheduled.request.entries.length : Normalization.InverseRootPolynomial.Coordinate) * (allowance + rootAllowance))
        * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients by ring1).trans_le
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (Fraction.Order.Arithmetic.add_le_add_right_direct paid
      _) massNN))

end ScheduledRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootSurfaceEnergy
