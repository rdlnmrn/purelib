module

public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.DifferentialTransport
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Laws
import Purelib.Approximation.Gaussian.Name.Coherent.Exact.Arithmetic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRootNames
import Purelib.Riemann.RootContinuation.SquareRootChannelOwnership
import Purelib.Data.Gaussian.Field
import Purelib.Tactic.Ring

/-! # Numerator transport at the same retained reciprocal root pair

The prepared quotient coordinate and both original root certificates supply
signed cancellation for any numerator channel. Unit and inverse-coordinate
numerators give the two genus-one value cases without changing the curve's
holomorphic differential index. These are coefficient identities; the
actual parity and oriented primitive endpoint comparison remain separate.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates.Overlap

open Purelib
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Riemann.Topology

/-- Cancel the same quotient coordinate against the reciprocal root for any original numerator channel.

The factor is the original prepared quotient v/r, whose reconstruction law
retains its sign relative to both root channels. Multiplication by 2t and
the original reciprocal minus sign yield the coefficient -2N/r. Neither
root, numerator, Point nor observation is acquired or resampled.
-/
def numeratorTransport {genus : Nat} {curve : HyperellipticCurve genus}
    {collar : ReciprocalExteriorCollar.Data curve} {cap : ReciprocalInnerInverse.Data curve collar}
    {point : Canonical}
    {owner : SquareRootContinuationChain.Owner ((HyperellipticReciprocal.polynomial curve).eval point)}
    (overlap : Overlap cap point owner) (numerator : CoherentNamed) :
    NamedEquivalent
      (CoherentNamed.mul (CoherentNamed.mul (Coherence.exact 2) overlap.coordinate.prepared.denominator)
        (CoherentNamed.mul (Coherence.exact (-1))
          (CoherentNamed.div numerator overlap.reciprocal.value overlap.reciprocal.apart))).name
      (CoherentNamed.mul (Coherence.exact (-2))
        (CoherentNamed.div numerator overlap.regularRoot.value overlap.regularRoot.apart)).name := by
  let factor := overlap.coordinate.prepared.denominator
  let quotient := CoherentNamed.div numerator overlap.reciprocal.value overlap.reciprocal.apart
  let regular := CoherentNamed.div numerator overlap.regularRoot.value overlap.regularRoot.apart
  exact (Laws.coherentMul_assoc (Coherence.exact 2) factor
    (CoherentNamed.mul (Coherence.exact (-1)) quotient)).trans
    ((Congruence.coherentMul_respects (Coherence.exact 2) (Coherence.exact 2)
      (CoherentNamed.mul factor (CoherentNamed.mul (Coherence.exact (-1)) quotient))
      (CoherentNamed.mul (Coherence.exact (-1)) (CoherentNamed.mul factor quotient))
      (NamedEquivalent.refl _) (move_constant (-1) factor quotient)).trans
      ((Laws.coherentMul_assoc (Coherence.exact 2) (Coherence.exact (-1))
        (CoherentNamed.mul factor quotient)).symm.trans
        (Congruence.coherentMul_respects
          (CoherentNamed.mul (Coherence.exact 2) (Coherence.exact (-1))) (Coherence.exact (-2))
          (CoherentNamed.mul factor quotient) regular
          (by simpa only [show (2 : Canonical) * (-1) = -2 by ring1] using
            Exact.Arithmetic.exact_mul (2 : Canonical) (-1))
          (overlap.coordinate.cancel_quotient numerator))))

/-- The same retained roots transport the actual unit numerator used by the genus-one ordinary value channel. -/
def unitTransport {genus : Nat} {curve : HyperellipticCurve genus}
    {collar : ReciprocalExteriorCollar.Data curve} {cap : ReciprocalInnerInverse.Data curve collar}
    {point : Canonical}
    {owner : SquareRootContinuationChain.Owner ((HyperellipticReciprocal.polynomial curve).eval point)}
    (overlap : Overlap cap point owner) :
    NamedEquivalent
      (CoherentNamed.mul (CoherentNamed.mul (Coherence.exact 2) overlap.coordinate.prepared.denominator)
        (CoherentNamed.mul (Coherence.exact (-1))
          (CoherentNamed.div (Coherence.exact 1) overlap.reciprocal.value overlap.reciprocal.apart))).name
      (CoherentNamed.mul (Coherence.exact (-2))
        (CoherentNamed.div (Coherence.exact 1) overlap.regularRoot.value overlap.regularRoot.apart)).name :=
  overlap.numeratorTransport (Coherence.exact 1)

/-- The same retained roots transport the inverse-coordinate numerator of the genus-one weighted value channel.

The coefficient identity uses the total exact scalar inverse. Its
interpretation as x dx/y additionally uses the original nonzero overlap
coordinate; it is not a regular differential at the cap origin.
-/
def coordinateTransport {genus : Nat} {curve : HyperellipticCurve genus}
    {collar : ReciprocalExteriorCollar.Data curve} {cap : ReciprocalInnerInverse.Data curve collar}
    {point : Canonical}
    {owner : SquareRootContinuationChain.Owner ((HyperellipticReciprocal.polynomial curve).eval point)}
    (overlap : Overlap cap point owner) :
    NamedEquivalent
      (CoherentNamed.mul (CoherentNamed.mul (Coherence.exact 2) overlap.coordinate.prepared.denominator)
        (CoherentNamed.mul (Coherence.exact (-1))
          (CoherentNamed.div (Coherence.exact point⁻¹) overlap.reciprocal.value overlap.reciprocal.apart))).name
      (CoherentNamed.mul (Coherence.exact (-2))
        (CoherentNamed.div (Coherence.exact point⁻¹)
          overlap.regularRoot.value overlap.regularRoot.apart)).name :=
  overlap.numeratorTransport (Coherence.exact point⁻¹)

/-- The actual ramified overlap retains a nonzero reciprocal coordinate, before interpreting its inverse. -/
private theorem packaged_point_nonzero {genus : Nat} {curve : HyperellipticCurve genus}
    {collar : ReciprocalExteriorCollar.Data curve} {cap : ReciprocalInnerInverse.Data curve collar}
    {point : Canonical}
    {owner : SquareRootContinuationChain.Owner ((HyperellipticReciprocal.polynomial curve).eval point)}
    (overlap : Overlap cap point owner) (branch : HyperellipticReciprocal.originOrder curve = 1) : point ≠ 0 := by
  have nonzero := Riemann.RootContinuation.SquareRootChannelOwnership.parameter_nonzero
    overlap.coordinate.certificate
  rewrite [branch, pow_one] at nonzero
  exact nonzero

/-- The actual ramified overlap retains a nonzero reciprocal coordinate, before interpreting its inverse. -/
theorem point_nonzero {genus : Nat} {curve : HyperellipticCurve genus}
    {collar : ReciprocalExteriorCollar.Data curve} {cap : ReciprocalInnerInverse.Data curve collar}
    {point : Canonical}
    {owner : SquareRootContinuationChain.Owner ((HyperellipticReciprocal.polynomial curve).eval point)}
    (overlap : Overlap cap point owner) (branch : HyperellipticReciprocal.originOrder curve = 1) : point ≠ 0 :=
  packaged_point_nonzero overlap branch

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates.Overlap

end
