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

/-- Each component must pay its own retained root-polygon comparison cost. -/
def RootPayments (requested rootAllowance : InverseRootPolynomial.Coordinate) :
    (entries : List (SurfaceRequest.Entry (domains := domains)
      (differential := differential) basis target coefficientTarget coverFloor floor)) →
    SurfacePlans.Plans capSample polynomials minimum entries → Prop
  | [], _ => True
  | head :: tail, plans =>
      RootBoundaryEnergy.CommonBasisRequest.Sampled.rootJoiningCost
        (request := head.request) (inputs := plans.1.inputs) requested ≤
        16 * rootAllowance^2 ∧
          RootPayments
          requested rootAllowance tail plans.2

/-- Sum disconnected component boundaries without adding connectors between them. -/
def rootBoundaryValues {requested : InverseRootPolynomial.Coordinate} :
    (entries : List (SurfaceRequest.Entry (domains := domains)
      (differential := differential) basis target coefficientTarget coverFloor floor)) →
    (plans : SurfacePlans.Plans capSample polynomials minimum entries)
      → (readings : SurfacePlans.Plans.Readings entries plans
      readingIndex) →
    (fans : SurfaceSamples.Plans.FanPreparations energyFloor entries
      plans readings) →
    (samples : SurfaceSamples.Plans.Samples coefficients radialDepth
      entries plans readings fans) →
    (comparisons : SurfacePrepared.Plans.Samples.PreparedComparisons
      entries plans readings fans samples) →
    PhysicalSurfaceEnergy.Plans.Samples.PhysicalCertificates requested
      entries plans readings fans samples comparisons → List InverseRootPolynomial.Gaussian
  | [], _, _, _, _, _, _ => []
  | _ :: tail, plans, readings, fans, samples, comparisons, physical =>

        (RootBoundaryEnergy.CommonBasisRequest.Sampled.PhysicalCertificate.rootBoundary
        physical.1) ::
        rootBoundaryValues
        tail plans.2 readings.2 fans.2 samples.2 comparisons.2 physical.2

/-- Both comparison allowances are homogeneous and charged once per component. -/
theorem rootUpper {requested physicalAllowance rootAllowance : InverseRootPolynomial.Coordinate} (positive
  : 0 < requested)
    (physicalNN : 0 ≤ physicalAllowance) (rootNN : 0 ≤ rootAllowance)
    (physicalPaid : requested ≤ 16 * physicalAllowance ^ 2)
    (branch : Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1) :
    (entries : List (SurfaceRequest.Entry (domains := domains)
      (differential := differential) basis target coefficientTarget coverFloor floor)) →
    (plans : SurfacePlans.Plans capSample polynomials minimum entries)
      → (readings : SurfacePlans.Plans.Readings entries plans
      readingIndex) →
    (fans : SurfaceSamples.Plans.FanPreparations energyFloor entries
      plans readings) →
    (samples : SurfaceSamples.Plans.Samples coefficients radialDepth
      entries plans readings fans) →
    (comparisons : SurfacePrepared.Plans.Samples.PreparedComparisons
      entries plans readings fans samples) →
    (traces : SurfacePrepared.Plans.Samples.PreparedTraces entries
      plans readings fans samples comparisons) →
    (physical :
      PhysicalSurfaceEnergy.Plans.Samples.PhysicalCertificates
      requested entries plans readings fans samples comparisons) →
    RootPayments requested
      rootAllowance entries plans → plans.stage entries ≤ readingIndex →
    (Gaussian.Norm.Sum.Basic.gaussianSum
      (Samples.rootBoundaryValues entries
      plans readings fans samples comparisons physical)).im / 4 ≤
      ((entries.length : InverseRootPolynomial.Coordinate) * (5 * target + physicalAllowance +
        rootAllowance)) * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients
  | [], _, _, _, _, _, _, _, _, _ => by
      change (0 : InverseRootPolynomial.Coordinate) / 4 ≤ (0 * (5 * target + physicalAllowance +
        rootAllowance)) * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients
      exact (show (0 : InverseRootPolynomial.Coordinate) / 4 = (0 * (5 * target + physicalAllowance +
        rootAllowance)) * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients by
        simp only [Fraction.Field.div_eq_mul_inv_direct]; ring1).le
  | head :: tail, plans, readings, fans, samples, comparisons, traces, physical, rootPaid, later => by
      have first :=
        RootBoundaryEnergy.CommonBasisRequest.Sampled.PhysicalCertificate.rootBoundary_upper
        physical.1 positive physicalNN rootNN physicalPaid rootPaid.1 traces.1 branch
        (plans.1.stage_eq.symm.trans_le ((Nat.Order.le_max_left ..).trans later))
      have rest :=
        Samples.rootUpper
        positive physicalNN rootNN physicalPaid branch tail plans.2 readings.2 fans.2 samples.2
        comparisons.2 traces.2 physical.2 rootPaid.2 ((Nat.Order.le_max_right ..).trans later)
      have both := Fraction.Order.Arithmetic.add_le_add_direct first rest
      have split : (Gaussian.Norm.Sum.Basic.gaussianSum
        (Samples.rootBoundaryValues (head ::
        tail) plans readings fans samples comparisons physical)).im / 4 =

            (RootBoundaryEnergy.CommonBasisRequest.Sampled.PhysicalCertificate.rootBoundary
            physical.1).im / 4 +
            (Gaussian.Norm.Sum.Basic.gaussianSum
              (Samples.rootBoundaryValues tail
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
  regular domains differential} {errorTarget : InverseRootPolynomial.Coordinate}
  (scheduled : SurfaceTraceRequest.ScheduledRequest prepared basis
    target errorTarget floor)
  (acquired : SurfaceEnergy.Request.Acquisition scheduled.request
    capSample polynomials minimum energyFloor)
  (evaluation : acquired.Evaluation coefficients)
  {requested allowance : InverseRootPolynomial.Coordinate}
  (physical : PhysicalSurfaceEnergy.Plans.Samples.PhysicalCertificates
    requested scheduled.request.entries acquired.plans acquired.readings
    acquired.fans evaluation.samples evaluation.comparisons)

/-- The complete physical upper bound pays the source estimate's explicit
five-quarter loss and both retained comparison allowances per component. -/
theorem root_boundary_energy_upper (positive : 0 < requested) (nonnegative : 0 ≤ allowance)
    (comparisonPaid : requested ≤ 16 * allowance ^ 2)
    {rootAllowance : InverseRootPolynomial.Coordinate} (rootNN : 0 ≤ rootAllowance)
    (rootPaid : Plans.Samples.RootPayments requested
      rootAllowance scheduled.request.entries acquired.plans)
    (branch : Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1) :
    (Gaussian.Norm.Sum.Basic.gaussianSum
      (Plans.Samples.rootBoundaryValues
      scheduled.request.entries acquired.plans acquired.readings acquired.fans
      evaluation.samples evaluation.comparisons physical)).im / 4 ≤
      (5 / 4 * target + (scheduled.request.entries.length : InverseRootPolynomial.Coordinate) * (allowance
        + rootAllowance)) * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients := open
        Algebra in by
  have upper := Plans.Samples.rootUpper positive
    nonnegative rootNN comparisonPaid branch scheduled.request.entries
    acquired.plans acquired.readings acquired.fans evaluation.samples evaluation.comparisons evaluation.traces physical
      rootPaid
    acquired.reading_eq.symm.le
  have tracePaid : (scheduled.request.entries.length : InverseRootPolynomial.Coordinate) * (4 *
    scheduled.request.localTarget) ≤ target := by
    rw [scheduled.request.entries_length]
    exact (show (prepared.components.length : InverseRootPolynomial.Coordinate) * (4 *
      scheduled.request.localTarget) =
      (4 * (prepared.components.length : InverseRootPolynomial.Coordinate)) *
        scheduled.request.localTarget by ring1).trans_le scheduled.request.paid
  have paid : (scheduled.request.entries.length : InverseRootPolynomial.Coordinate) * (5 *
    scheduled.request.localTarget) ≤ 5 / 4 * target := by
    have scaled := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct tracePaid (by
        decide +kernel : (0 : InverseRootPolynomial.Coordinate) ≤ 5 / 4)
    exact (show (scheduled.request.entries.length : InverseRootPolynomial.Coordinate) * (5 *
      scheduled.request.localTarget) =
      5 / 4 * ((scheduled.request.entries.length : InverseRootPolynomial.Coordinate) * (4 *
        scheduled.request.localTarget)) by
        calc
          _ = 5 * ((scheduled.request.entries.length : InverseRootPolynomial.Coordinate) *
            scheduled.request.localTarget) := by
            ring1
          _ = ((5 / 4 : InverseRootPolynomial.Coordinate) * 4) * ((scheduled.request.entries.length :
            InverseRootPolynomial.Coordinate) * scheduled.request.localTarget) :=
            congrArg (fun scalar => scalar * ((scheduled.request.entries.length :
              InverseRootPolynomial.Coordinate) * scheduled.request.localTarget))
              (by decide +kernel : (5 : InverseRootPolynomial.Coordinate) = (5 / 4) * 4)
          _ = _ := by ring1).trans_le scaled
  have massNN : 0 ≤ Readings.PreparedObservationCoercivity.coefficientNormSq coefficients :=
    FiniteSum.Fin.sumFin_zero.symm.trans_le
    (FiniteSum.Rational.Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 :
      InverseRootPolynomial.Coordinate)) _
      (fun row => Gaussian.Basic.Canonical.normSq_nonneg (coefficients row)))
  exact upper.trans ((show ((scheduled.request.entries.length : InverseRootPolynomial.Coordinate) *
    (5 * scheduled.request.localTarget + allowance + rootAllowance)) *
      Readings.PreparedObservationCoercivity.coefficientNormSq coefficients =
    ((scheduled.request.entries.length : InverseRootPolynomial.Coordinate) * (5 *
      scheduled.request.localTarget) +
      (scheduled.request.entries.length : InverseRootPolynomial.Coordinate) * (allowance + rootAllowance))
        * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients by ring1).trans_le
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (Fraction.Order.Arithmetic.add_le_add_right_direct paid
      _) massNN))

end ScheduledRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootSurfaceEnergy
