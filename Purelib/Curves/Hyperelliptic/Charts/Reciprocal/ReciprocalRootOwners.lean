module
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Purelib.Approximation.Gaussian.Name.Coherent.Power
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Value
meta import Purelib.Elab.ConstructiveInjectivity

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRootNames
public import Purelib.Riemann.RootContinuation.SquareRootChannelOwnership
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalCollarTransport
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Name.Coherent.Division.Equivalence
import Purelib.Algebra.Ring.Multiplication
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Paths.ClearBoxPaths

open Purelib

open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product

open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed

open Purelib.Curves

open Purelib.Curves.Hyperelliptic

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Differentials

open Purelib.Riemann.Paths

open Purelib.Riemann.RootContinuation

open Purelib.Riemann.Topology

open Purelib.Approximation.Gaussian

open Purelib.Approximation.Gaussian.Name

@[expose] public section

/-!
# Reciprocal winding owners from the retained affine root

The scaled original root channel now supplies its own winding-track owner,
with a finite operational identification. The existing collar continuation
therefore starts at that same occurrence. This supplies root and integrand
handoffs, not yet the finite path-substitution or integral-gluing theorem.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRootOwners

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRootNames (Gaussian CoherentNamed NamedEquivalent
  ScaledRoot factor)
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed.Coherence (exact)
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed (mul)
open Purelib.Riemann.RootContinuation.SquareRootChannelOwnership (Attachment attach)
open Purelib.Algebra.Quadratic.Pair.Polynomial (Expression)

/-- The winding owner is selected from the scaled original channel, with its operational identification, rather than
chosen independently at `q(w)`. -/
def attach {parameter factor point : Gaussian} {radicand : HyperellipticReciprocal.GaussianPolynomial}
    {original : CertifiedSquareRoot.Certificate parameter}
    (root : ScaledRoot original factor radicand point) :
    SquareRootChannelOwnership.Attachment root.certificate.value (radicand.eval point) :=
  SquareRootChannelOwnership.attach root.certificate

set_option genInjectivity false in
/-- One cached coefficient at the operationally attached owner of the same original scaled root.

The source coefficient retains its original pullback certificate and pair.
The attached owner supplies an explicit comparison to the original prepared
root; transport reuses that pair rather than evaluating either table again.
-/
structure Coefficient (root : ScaledRoot original scale radicand point) (differential : Differential genus) where
  /-- The actual retained source coefficient cache. -/
  source : ScaledRoot.Coefficients root differential
  /-- The attached winding owner of the same prepared original root. -/
  attached : Attachment root.certificate.value (radicand.eval point)
  /-- The same cached exact pair interpreted at the attached owner's original channel. -/
  denotation : Expression.Denotation source.pullback point
    (attached.owner.certificate attached.owner.parameterNonzero).value
  /-- The transported channel agrees with the actual source coefficient channel. -/
  equivalent : NamedEquivalent denotation.channel.name source.denotation.channel.name

constructive_injectivity Coefficient

namespace Coefficient

variable {genus : Nat} {differential : Differential genus}
  {parameter scale point : Gaussian} {radicand : HyperellipticReciprocal.GaussianPolynomial}
  {original : CertifiedSquareRoot.Certificate parameter} {root : ScaledRoot original scale radicand point}

/-- Interpret the retained coefficient pair at the same operationally attached owner once. -/
def build (source : ScaledRoot.Coefficients root differential)
    (attached : Attachment root.certificate.value (radicand.eval point)) : Coefficient root differential :=
  let target := (attached.owner.certificate attached.owner.parameterNonzero).value
  let denotation := source.denotation.transport target attached.equivalent.symm
  ⟨source, attached, denotation, source.denotation.transport_equivalent target attached.equivalent.symm⟩

/-- The attached coefficient agrees with the signed original differential program on that same owner.

This comparison retains the attached owner's quotient denominator and the
original reversed exponent. It relates finite operational programs without
asserting exactness of their rational samples.
-/
def differential_equivalent (owned : Coefficient root differential) :
    NamedEquivalent owned.denotation.channel.name
      (mul (exact (-1)) (Value.differentialValue
        (HyperellipticReciprocal.reversedDifferential differential) point
        (owned.attached.owner.certificate owned.attached.owner.parameterNonzero).value
        (owned.attached.owner.certificate owned.attached.owner.parameterNonzero).apart)).name := by
  let certificate := owned.attached.owner.certificate owned.attached.owner.parameterNonzero
  let numerator := -point ^ (HyperellipticReciprocal.reversedDifferential differential).exponent
  have quotient := Coherent.Division.Equivalence.coherentDiv_respects (exact numerator) (exact numerator)
    root.prepared.denominator certificate.value root.prepared.apart certificate.apart
    (Equivalence.NamedEquivalent.refl _) owned.attached.equivalent
  have signed := (Congruence.coherentMul_respects (exact (-1)) (exact (-1)) _ _
    (Equivalence.NamedEquivalent.refl _)
    (ReciprocalRootNames.differential_quotient
      (HyperellipticReciprocal.reversedDifferential differential) point certificate.value certificate.apart)).trans
    (ReciprocalRootNames.constant_mul_quotient (-1)
      (point ^ (HyperellipticReciprocal.reversedDifferential differential).exponent)
      certificate.value certificate.apart)
  have scalar : (-1 : Gaussian) * (point ^ (HyperellipticReciprocal.reversedDifferential differential).exponent) =
      numerator := by
    exact (Algebra.Ring.Multiplication.neg_mul 1 _).trans
      (congrArg Neg.neg (Data.Gaussian.Basic.one_mul _))
  rewrite [scalar] at signed
  exact owned.equivalent.trans (owned.source.quotient_equivalent.trans (quotient.trans signed.symm))

end Coefficient

/-- Read the already retained coefficient channel at the attached winding owner. -/
def coefficient (owned : Coefficient root differential) : CoherentNamed := owned.denotation.channel

/-- The retained owner comparison hands the coefficient back to its original prepared scaled root. -/
def coefficient_handoff (owned : Coefficient root differential) :
    NamedEquivalent (coefficient owned).name (ReciprocalRootNames.coefficient owned.source).name :=
  owned.equivalent

/-- The attached-owner coefficient is the inverse-coordinate multiple of the original affine integrand. -/
def coefficient_transport {genus : Nat} (differential : Differential genus) (source : Gaussian)
    (nonzero : source ≠ 0) {parameter : Gaussian} {radicand : HyperellipticReciprocal.GaussianPolynomial}
    {original : CertifiedSquareRoot.Certificate parameter}
    {root : ScaledRoot original (factor genus source) radicand source⁻¹}
    (owned : Coefficient root differential) :
    NamedEquivalent (coefficient owned).name
      (mul (exact (-(source ^ 2)))
        (Value.differentialValue differential source original.value original.apart)).name :=
  (coefficient_handoff owned).trans
    (ReciprocalRootNames.coefficient_transport differential source nonzero owned.source)

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar (Data)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalCollarTransport (Fiber)

/-- Retain both the reciprocal owner identification and the actual continued path. The supplied owner belongs to the
original affine curve; no reciprocal owner, successful ownership scan or chart-identity certificate is input. -/
def cross {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {data : Data curve} {source : Gaussian}
    (fiber : Fiber data source) (original : SquareRootContinuationChain.Owner (curve.polynomial.eval source)) :
    let root := ReciprocalRootNames.ofBoundaryOwner curve source fiber.boundary original
    (attached : SquareRootChannelOwnership.Attachment root.certificate.value
      ((HyperellipticReciprocal.polynomial curve).eval source⁻¹)) ×
      PreparedPathTrace.TracedPath fiber.route.path attached.owner :=
  let root := ReciprocalRootNames.ofBoundaryOwner curve source fiber.boundary original
  let attached := Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRootOwners.attach root
  ⟨attached, fiber.transport attached.owner⟩

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRootOwners
