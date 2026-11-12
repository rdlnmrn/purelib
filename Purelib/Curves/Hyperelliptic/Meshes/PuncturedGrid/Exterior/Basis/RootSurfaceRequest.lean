module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfacePlans
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootSurfaceEnergy
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootJoiningBudget
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.PuncturedGridFaces

open Purelib.Curves

open Purelib.Geometry

open Purelib

open Purelib.Data.Rat

open Purelib.Riemann

@[expose] public section

/-! Compute one physical comparison target for all retained root polygons. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootSurfaceRequest.Plans.Samples

open Purelib.Riemann.Normalization

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootJoiningBudget.CommonBasisRequest.Sampled
  (rootSourceCost rootPhysicalTarget rootPhysicalTarget_positive rootJoiningCost_paid_of_target_le)

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

section Plans.Samples

/-- Retain the source-restoration payment independently of physical refinement. -/
def RootSourcePayments (rootAllowance : InverseRootPolynomial.Coordinate) :
    (entries : List (SurfaceRequest.Entry (domains := domains)
      (differential := differential) basis target coefficientTarget coverFloor floor)) →
    SurfacePlans.Plans capSample polynomials minimum entries → Prop
  | [], _ => True
  | head :: tail, plans =>
      RootJoiningBudget.CommonBasisRequest.Sampled.rootSourceCost
        (request := head.request) (inputs := plans.1.inputs) ≤ 8 * rootAllowance^2 ∧

          RootSourcePayments
          rootAllowance tail plans.2

/-- One positive target refines every component's independently computed cap. -/
def rootTarget (physicalAllowance rootAllowance : InverseRootPolynomial.Coordinate) :
    (entries : List (SurfaceRequest.Entry (domains := domains)
      (differential := differential) basis target coefficientTarget coverFloor floor)) →
    SurfacePlans.Plans capSample polynomials minimum entries →
      InverseRootPolynomial.Coordinate
  | [], _ => 16 * physicalAllowance^2
  | head :: tail, plans =>
      min
        (RootJoiningBudget.CommonBasisRequest.Sampled.rootPhysicalTarget
        (request := head.request) (inputs := plans.1.inputs) physicalAllowance rootAllowance)
        (rootTarget
          physicalAllowance rootAllowance tail plans.2)

/-- Positive physical and root allowances give a positive common target across the original component plans. -/
theorem rootTarget_positive {physicalAllowance rootAllowance : InverseRootPolynomial.Coordinate}
    (physicalPositive : 0 < physicalAllowance) (rootPositive : 0 < rootAllowance) :
    (entries : List (SurfaceRequest.Entry (domains := domains)
      (differential := differential) basis target coefficientTarget coverFloor floor)) →
    (plans : SurfacePlans.Plans capSample polynomials minimum entries)
      → 0 < Samples.rootTarget
      physicalAllowance rootAllowance entries plans
  | [], _ => Fraction.Order.Arithmetic.mul_pos_direct (by decide) (by
      simpa only [pow_two] using Fraction.Order.Arithmetic.mul_pos_direct physicalPositive
        physicalPositive)
  | _ :: tail, plans => Fraction.Order.Basic.lt_min
    (RootJoiningBudget.CommonBasisRequest.Sampled.rootPhysicalTarget_positive
    physicalPositive rootPositive)

        (rootTarget_positive
        physicalPositive rootPositive tail plans.2)

/-- The common component target fits the squared physical energy allowance. -/
theorem rootTarget_physical_paid (physicalAllowance rootAllowance : InverseRootPolynomial.Coordinate) :
    (entries : List (SurfaceRequest.Entry (domains := domains)
      (differential := differential) basis target coefficientTarget coverFloor floor)) →
    (plans : SurfacePlans.Plans capSample polynomials minimum entries)
      →
    Samples.rootTarget physicalAllowance
      rootAllowance entries plans ≤ 16 * physicalAllowance^2
  | [], _ => le_rfl
  | _ :: tail, plans => (Fraction.Order.Basic.min_le_right ..).trans
    (rootTarget_physical_paid
    physicalAllowance rootAllowance tail plans.2)

/-- The common minimum pays every root polygon on its own retained source inputs. -/
theorem rootTarget_root_paid {physicalAllowance rootAllowance requested :
  InverseRootPolynomial.Coordinate}
    (physicalPositive : 0 < physicalAllowance) (rootPositive : 0 < rootAllowance) :
    (entries : List (SurfaceRequest.Entry (domains := domains)
      (differential := differential) basis target coefficientTarget coverFloor floor)) →
    (plans : SurfacePlans.Plans capSample polynomials minimum entries)
      →
    RootSourcePayments rootAllowance
      entries plans →
    requested ≤ Samples.rootTarget
      physicalAllowance rootAllowance entries plans →
    RootSurfaceEnergy.Plans.Samples.RootPayments requested
      rootAllowance entries plans
  | [], _, _, _ => True.intro
  | _ :: tail, plans, sourcePaid, targetPaid =>
      ⟨rootJoiningCost_paid_of_target_le physicalPositive rootPositive sourcePaid.1 (targetPaid.trans
        (Fraction.Order.Basic.min_le_left ..)),

          rootTarget_root_paid
          physicalPositive rootPositive tail plans.2 sourcePaid.2 (targetPaid.trans (Fraction.Order.Basic.min_le_right
          ..))⟩

set_option genInjectivity false in
/-- An executable common request retains the certificates consumed by both
physical and root boundary estimates. Source payment is established separately. -/
structure RootRequest (physicalAllowance rootAllowance : InverseRootPolynomial.Coordinate)
    (entries : List (SurfaceRequest.Entry (domains := domains)
      (differential := differential) basis target coefficientTarget coverFloor floor))
    (plans : SurfacePlans.Plans capSample polynomials minimum entries)
      where
  /-- The common physical comparison target for the retained component plans. -/ requested :
    InverseRootPolynomial.Coordinate
  /-- The retained target is exactly the computed finite minimum of component caps. -/ requested_eq : requested =
    Samples.rootTarget physicalAllowance
    rootAllowance entries plans
  /-- The common comparison target is positive. -/ positive : 0 < requested
  /-- The common target fits the squared physical energy allowance. -/ physical_paid : requested ≤ 16 *
    physicalAllowance^2
  /-- Every original component root-polygon comparison is paid at this common target. -/ root_paid :
    RootSurfaceEnergy.Plans.Samples.RootPayments requested
    rootAllowance entries plans

constructive_injectivity RootRequest

/-- Compute the common physical target and retain both physical and componentwise root-payment certificates.

Positive allowances give positivity; each original component must separately retain its source-restoration payment. -/
def RootRequest.build {physicalAllowance rootAllowance : InverseRootPolynomial.Coordinate}
    (physicalPositive : 0 < physicalAllowance) (rootPositive : 0 < rootAllowance)
    (entries : List (SurfaceRequest.Entry (domains := domains)
      (differential := differential) basis target coefficientTarget coverFloor floor))
    (plans : SurfacePlans.Plans capSample polynomials minimum entries)
    (sourcePaid : RootSourcePayments
      rootAllowance entries plans) :
    RootRequest physicalAllowance
      rootAllowance entries plans :=
  ⟨rootTarget physicalAllowance rootAllowance entries plans, rfl,
    Samples.rootTarget_positive
      physicalPositive rootPositive entries plans,
    Samples.rootTarget_physical_paid
      physicalAllowance rootAllowance entries plans,
    Samples.rootTarget_root_paid
      physicalPositive rootPositive entries plans sourcePaid le_rfl⟩

end Plans.Samples
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootSurfaceRequest.Plans.Samples
