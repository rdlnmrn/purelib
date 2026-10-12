module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BasisArcSamples
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisAggregate
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisBounds
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapGeometry
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.Dyadic.RadialTriangles
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Readings.PreparedObservationCoercivity
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BasisArcRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BasisEnergyUpper
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Approximation.Rational.Budget

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BasisArcRequest

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BasisEnergyUpper

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisAggregate

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisBounds

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisRequest

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Data.Rat

open Purelib.Integration.Path.Dyadic

open Purelib.Integration.Path.Dyadic.RadialTriangles

open Purelib.LinearAlgebra.Gaussian.Energy

open Purelib.Riemann.Readings

public section

/-! Common requested regular exterior energy on the actual cached basis
samples and reciprocal cap refinement, with automatic sampling payment. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (AllSurfacePreparation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation (CapAttachment)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy (RegularBasisPolynomials)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisBounds (RegularBasisBounds)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisRequest (RegularBasisRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisAggregate (RegularBasisCap)
open Purelib.Riemann.Normalization
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {differential other :
    Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    FaceDomainBank lifted.frames base.faces.regulars}

open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Riemann.Readings.PreparedObservationCoercivity (coefficientNormSq)

namespace BasisRegularEnergy

/-- The two basis-index factors are paid before any numerical sampling. -/
@[expose] def basisEnergyPairTarget (genus : Nat) (allowance : Fraction.Rational) : Fraction.Rational :=
  Aggregate.perTerm ((4 * allowance)^2) genus

/-- A positive original energy allowance gives a strictly positive common basis-pair target. -/
theorem basisEnergyPairTarget_positive {allowance : Fraction.Rational} (positive : 0 < allowance) :
    0 < basisEnergyPairTarget genus allowance :=
  Aggregate.perTerm_positive (Fraction.Order.Arithmetic.pow_pos_direct (Fraction.Order.Arithmetic.mul_pos_direct (by
    decide) positive) 2) genus

/-- The retained common pair target pays both original basis-index factors within sixteen times the squared allowance.
-/
theorem basisEnergyPairTarget_paid {allowance : Fraction.Rational} (positive : 0 < allowance) :
    (genus : Fraction.Rational)^2 *
      basisEnergyPairTarget genus allowance ≤ 16 *
      allowance^2 := by
  have paid := Aggregate.count_mul_perTerm_lt
    (Fraction.Order.Arithmetic.pow_pos_direct (Fraction.Order.Arithmetic.mul_pos_direct (by
        decide : (0 : Fraction.Rational) < 4) positive) 2) genus
  exact (show (genus : Fraction.Rational)^2 *
    basisEnergyPairTarget genus allowance =
    (genus : Fraction.Rational) * ((genus : Fraction.Rational) *
      basisEnergyPairTarget genus allowance) by
      ring1).trans_le
      (paid.le.trans_eq (by ring1))

end BasisRegularEnergy

namespace BasisRegularEnergy.BasisArcRequest

/-- Request all original regular exterior basis arcs at the pair tolerance determined by the supplied positive energy
allowance. -/
@[expose] def forEnergyAllowance (regular : RegularBounds.Data cap)
    (domains : DomainBanks.FaceDomainBank lifted.frames base.faces.regulars)
    (allowance : Fraction.Rational) (positive : 0 < allowance) (minimum depthFloor : Nat) :
    BasisArcRequest regular domains
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BasisRegularEnergy.basisEnergyPairTarget genus allowance)
      minimum depthFloor :=
  BasisArcRequest.build regular domains _
    (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BasisRegularEnergy.basisEnergyPairTarget_positive positive)
    minimum depthFloor

end BasisRegularEnergy.BasisArcRequest

variable {allowance capTarget : Rational} {minimum depthFloor stage : Nat} {box :
  Purelib.Geometry.Rational.Box}
  {prepared :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
    regular domains differential} {attached :
    CapAttachment prepared}
  (request : BasisArcRequest regular domains
    (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BasisRegularEnergy.basisEnergyPairTarget genus
    allowance) minimum depthFloor)
  (polynomials : RegularBasisPolynomials cap
    stage box)
  (geometry :
    Caps.AllSurfacePreparation.CapAttachment.ReciprocalGeometry
    attached)

set_option genInjectivity false in
/-- Cache the cap geometry, basis values and every source pair at one chosen refinement. The numerical bank is the one
supplied at the common late stage. -/
structure BasisRegularEnergy (capTarget : Fraction.Rational) where
  /-- The retained original energy allowance is strictly positive. -/ allowance_positive : 0 < allowance
  /-- The magnitude bounds of the actual original basis polynomial bank. -/ bounds : CapBasisBounds.RegularBasisBounds
    polynomials
  /-- The retained cap request paying the cap target beyond the original arc depth floor. -/ refinement :
    CapBasisRequest.RegularBasisRequest bounds attached.caps.length capTarget request.depth
  /-- The cached dyadic parameters at that exact retained cap refinement depth. -/ parameters :
    RadialTriangles.Parameters refinement.depth
  /-- The actual cap geometry and basis data evaluated on those cached parameters. -/ caps :
    CapBasisAggregate.RegularBasisCap geometry parameters polynomials
  /-- The original basis arc samples at the same retained refinement depth and paid pair target. -/ samples :
    BasisArcSamples (regular := regular) (domains := domains) polynomials
    (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BasisRegularEnergy.basisEnergyPairTarget genus allowance)
      minimum refinement.depth

constructive_injectivity BasisRegularEnergy

namespace BasisRegularEnergy

/-- The cap request starts after every exterior arc's required depth. Both sides then use that exact depth, without
resampling the polynomial bank. -/
@[expose] def build (positive : 0 < allowance) (capTarget : Fraction.Rational) (capPositive : 0 < capTarget)
    (chart : HyperellipticReciprocal.originOrder curve = 0) (later : request.index ≤ stage) :
    BasisRegularEnergy request polynomials
      geometry capTarget := by
  let bounds := RegularBasisBounds.build polynomials
  let refinement := RegularBasisRequest.build bounds attached.caps.length capTarget capPositive request.depth
  let parameters := Parameters.build refinement.depth
  let caps := RegularBasisCap.build geometry parameters polynomials chart capTarget capPositive
  let samples := request.evaluate polynomials chart later refinement.minimum_le
  exact ⟨positive, bounds, refinement, parameters, caps, samples⟩

variable {request polynomials geometry}

/-- No caller error-payment inequality or separately chosen cap depth remains. The endpoint-corrected source energy is
homogeneous in arbitrary coefficients. -/
theorem energy_upper (energy : BasisRegularEnergy
  request polynomials geometry capTarget)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) :
    (energy.samples.sourceEnergy coefficients).im / 4 ≤
      (capTarget + allowance) * PreparedObservationCoercivity.coefficientNormSq coefficients :=
  BasisArcSamples.energy_upper attached energy.refinement energy.caps coefficients
    ((energy.refinement.certify energy.caps).evaluate coefficients) energy.samples allowance
      energy.allowance_positive.le
    (basisEnergyPairTarget_paid
      energy.allowance_positive)

end BasisRegularEnergy
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior
