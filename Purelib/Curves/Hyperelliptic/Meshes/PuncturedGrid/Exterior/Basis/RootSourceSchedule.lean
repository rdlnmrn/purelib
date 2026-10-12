module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootSurfaceRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfacePlans
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceTraceRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootSourceSurface
import Mathlib.Order.Defs.LinearOrder
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRequest
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.PuncturedGridFaces

open Purelib.Curves

open Purelib.Geometry

open Purelib

open Purelib.Data.Rat

open Purelib.Riemann

@[expose] public section

/-! Construct source and physical root-comparison payments from positive budgets. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis

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

set_option genInjectivity false in
/-- A source-safe schedule caches the positive reduced target and the actual
canonical acquisition schedule, including its original component owners. -/
structure RootSourceSchedule (prepared :
  SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
  regular domains differential)
    (basis : Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds.BasisBounds bounds)
    (desired errorTarget rootAllowance : Normalization.InverseRootPolynomial.Coordinate) (errorPositive : 0 <
      errorTarget) (floor : Nat) where
  /-- The common source-restoration ceiling computed on the original surface components. -/ ceiling :
    Normalization.InverseRootPolynomial.Coordinate
  /-- The ceiling equals the fixed-cover source target of the original component list. -/ ceiling_eq : ceiling =
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootSourceSurface.sourceSurfaceTarget rootAllowance
    prepared.components
  /-- The reduced positive source target used by the retained canonical scheduler. -/ target :
    Normalization.InverseRootPolynomial.Coordinate
  /-- The reduced target is exactly the minimum of the desired target and source ceiling. -/ target_eq : target = min
    desired ceiling
  /-- The retained reduced source target is positive. -/ positive : 0 < target
  /-- The reduced source target does not exceed the desired target. -/ target_le : target ≤ desired
  /-- The reduced target fits the retained source-restoration ceiling. -/ source_paid : target ≤ ceiling
  /-- The canonical original-component trace scheduler at the reduced source target. -/ scheduled :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceTraceRequest.ScheduledRequest prepared basis target
    errorTarget floor
  /-- The stored scheduler is exactly the original constructor at the retained reduced target. -/ canonical : scheduled
    = Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceTraceRequest.ScheduledRequest.build prepared basis target
    errorTarget positive errorPositive floor

constructive_injectivity RootSourceSchedule

namespace RootSourceSchedule
variable {prepared :
  SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
  regular domains differential}
  {desired errorTarget rootAllowance : Normalization.InverseRootPolynomial.Coordinate} {errorPositive : 0 < errorTarget}

/-- Reduce the desired source target to the fixed-cover ceiling and retain its canonical component scheduler.

Positive desired, error and root allowances supply the stored positivity and source-payment bounds before numerical
acquisition. -/
def build (prepared :
  SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
  regular domains differential)
    (basis : Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds.BasisBounds bounds)
    (desired errorTarget rootAllowance : Normalization.InverseRootPolynomial.Coordinate) (desiredPositive : 0 < desired)
    (errorPositive : 0 < errorTarget) (rootPositive : 0 < rootAllowance) (floor : Nat) :
    RootSourceSchedule prepared basis desired
      errorTarget rootAllowance errorPositive floor := by
  let ceiling := Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootSourceSurface.sourceSurfaceTarget rootAllowance
    prepared.components
  let target := min desired ceiling
  have positive : 0 < target := Fraction.Order.Basic.lt_min desiredPositive
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootSourceSurface.sourceSurfaceTarget_positive rootPositive
    prepared.components)
  exact ⟨ceiling, rfl, target, rfl, positive, Fraction.Order.Basic.min_le_left .., Fraction.Order.Basic.min_le_right ..,
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceTraceRequest.ScheduledRequest.build prepared basis target
      errorTarget positive errorPositive floor, rfl⟩

variable (schedule :
  RootSourceSchedule prepared basis
  desired errorTarget rootAllowance errorPositive floor)

/-- Every later numerical plan inherits the automatically paid source cost. -/
theorem sources_paid (plans : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfacePlans.Plans capSample polynomials
  minimum schedule.scheduled.request.entries) :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootSurfaceRequest.Plans.Samples.RootSourcePayments rootAllowance
      schedule.scheduled.request.entries plans :=
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootSourceSurface.ScheduledRequest.root_sources_paid
    schedule.positive errorPositive schedule.scheduled schedule.canonical
    (schedule.source_paid.trans_eq schedule.ceiling_eq) plans

/-- Both root and physical comparison requests are now computed from positive
allowances; no source-restoration certificate is supplied by the caller. -/
def request (plans : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfacePlans.Plans capSample polynomials minimum
  schedule.scheduled.request.entries)
    {physicalAllowance : Normalization.InverseRootPolynomial.Coordinate} (physicalPositive : 0 < physicalAllowance)
      (rootPositive : 0 < rootAllowance) :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootSurfaceRequest.Plans.Samples.RootRequest physicalAllowance
      rootAllowance schedule.scheduled.request.entries plans :=
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootSurfaceRequest.Plans.Samples.RootRequest.build physicalPositive
    rootPositive schedule.scheduled.request.entries plans
    (schedule.sources_paid plans)

end RootSourceSchedule
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis
