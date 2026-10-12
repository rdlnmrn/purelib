module
import Purelib.Data.Gaussian.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
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
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalSurfaceEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootSurfaceEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedObservationCoercivity
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootSourceSchedule
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedRootSurface
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootSurfaceRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceTraceRequest
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.PuncturedGridFaces

open Purelib.Curves

open Purelib.Data

open Purelib.Geometry

open Purelib

open Purelib.Riemann

@[expose] public section

/-! The surface bound with automatically paid source and physical root comparisons. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootSourceEnergy

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

namespace RootSourceSchedule
variable {prepared :
  SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
  regular domains differential}
  {desired errorTarget rootAllowance : Normalization.InverseRootPolynomial.Coordinate} {errorPositive : 0 < errorTarget}
  (schedule : RootSourceSchedule prepared basis
    desired errorTarget rootAllowance errorPositive floor)
  (acquired : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceEnergy.Request.Acquisition
    schedule.scheduled.request capSample polynomials minimum energyFloor)
  (evaluation : acquired.Evaluation coefficients)
  {physicalAllowance : Normalization.InverseRootPolynomial.Coordinate}
  (physicalPositive : 0 < physicalAllowance) (rootPositive : 0 < rootAllowance)
  (physical : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalSurfaceEnergy.Plans.Samples.PhysicalCertificates
    (schedule.request acquired.plans physicalPositive rootPositive).requested
    schedule.scheduled.request.entries acquired.plans acquired.readings acquired.fans evaluation.samples
      evaluation.comparisons)

/-- The complete root-corrected boundary is bounded using automatically chosen
source and physical tolerances, at the originally requested surface allowance. -/
theorem energy_upper (branch : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1) :
    (Data.Gaussian.Norm.Sum.Basic.gaussianSum
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootSurfaceEnergy.Plans.Samples.rootBoundaryValues
      schedule.scheduled.request.entries acquired.plans acquired.readings
      acquired.fans evaluation.samples evaluation.comparisons physical)).im / 4 ≤
      (5 / 4 * desired + (schedule.scheduled.request.entries.length : Normalization.InverseRootPolynomial.Coordinate) *
        (physicalAllowance + rootAllowance)) *
        Readings.PreparedObservationCoercivity.coefficientNormSq coefficients := open Purelib.Algebra in open
          Purelib.Data.Rat in by
  have upper :=
    RequestedRootSurface.ScheduledRequest.requested_root_boundary_upper
    schedule.scheduled acquired evaluation
    (schedule.request acquired.plans physicalPositive rootPositive) physical physicalPositive.le rootPositive.le branch
  have targetLe := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct schedule.target_le (by
      decide +kernel : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 5 / 4)
  have massNN : 0 ≤ Readings.PreparedObservationCoercivity.coefficientNormSq coefficients :=
    FiniteSum.Fin.sumFin_zero.symm.trans_le
    (FiniteSum.Rational.Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 :
      Normalization.InverseRootPolynomial.Coordinate)) _ (fun row => Gaussian.Basic.Canonical.normSq_nonneg
      (coefficients row)))
  exact upper.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (Fraction.Order.Arithmetic.add_le_add_right_direct targetLe _) massNN)

end RootSourceSchedule
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootSourceEnergy
