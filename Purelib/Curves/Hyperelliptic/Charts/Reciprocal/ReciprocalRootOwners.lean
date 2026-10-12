module
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Purelib.Approximation.Gaussian.Name.Coherent.Power
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Value

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

/-- The winding owner is selected from the scaled original channel, with its operational identification, rather than
chosen independently at `q(w)`. -/
def attach {parameter factor target : Gaussian} {original : CertifiedSquareRoot.Certificate parameter}
    (root : ScaledRoot original factor target) :
    SquareRootChannelOwnership.Attachment root.certificate.value target :=
  SquareRootChannelOwnership.attach root.certificate

/-- The actual reciprocal owner's differential coefficient, including the orientation sign and reversed standard basis
index. -/
def coefficient {genus : Nat} (differential : Differentials.Basic.Differential genus) (source : Gaussian)
    {target : Gaussian} (owner : SquareRootContinuationChain.Owner target) : CoherentNamed :=
  let certificate := owner.certificate owner.parameterNonzero
  Coherent.CoherentNamed.mul (Coherent.CoherentNamed.Coherence.exact (-1)) (Value.differentialValue
    (HyperellipticReciprocal.reversedDifferential differential) source⁻¹ certificate.value certificate.apart)

/-- Replace the prepared scaled channel by its attached owner's actual name. The inherited comparison is essential; the
square equation alone cannot justify this replacement. -/
def coefficient_handoff {genus : Nat} (differential : Differentials.Basic.Differential genus) (source : Gaussian)
    {parameter target : Gaussian} {original : CertifiedSquareRoot.Certificate parameter}
    (root : ScaledRoot original (factor genus source) target)
    (attached : SquareRootChannelOwnership.Attachment root.certificate.value target) :
    NamedEquivalent (Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRootOwners.coefficient differential source
      attached.owner).name
      (ReciprocalRootNames.coefficient differential source root).name := by
  let numerator := Coherent.Power.namedPower (Coherent.CoherentNamed.Coherence.exact source⁻¹)
    (HyperellipticReciprocal.reversedDifferential differential).exponent
  let certificate := attached.owner.certificate attached.owner.parameterNonzero
  exact Coherent.Arithmetic.Product.Congruence.coherentMul_respects (Coherent.CoherentNamed.Coherence.exact (-1))
    (Coherent.CoherentNamed.Coherence.exact (-1)) _ _
    (Equivalence.NamedEquivalent.refl _)
    (Purelib.Approximation.Gaussian.Name.Coherent.Division.Equivalence.coherentDiv_respects numerator numerator
      certificate.value
      root.prepared.denominator
      certificate.apart root.prepared.apart (Equivalence.NamedEquivalent.refl _) attached.equivalent.symm)

/-- The actual attached-owner integrand is the inverse-coordinate multiple of the original integrand, for every
differential index and genus. -/
def coefficient_transport {genus : Nat} (differential : Differentials.Basic.Differential genus) (source : Gaussian)
    (nonzero : source ≠ 0) {parameter target : Gaussian}
    {original : CertifiedSquareRoot.Certificate parameter}
    (root : ScaledRoot original (factor genus source) target)
    (attached : SquareRootChannelOwnership.Attachment root.certificate.value target) :
    NamedEquivalent (Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRootOwners.coefficient differential source
      attached.owner).name
      (Coherent.CoherentNamed.mul (Coherent.CoherentNamed.Coherence.exact (-(source ^ 2)))
        (Value.differentialValue differential source original.value original.apart)).name :=
  (Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRootOwners.coefficient_handoff differential source root
    attached).trans
    (ReciprocalRootNames.coefficient_transport differential source nonzero root)

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
