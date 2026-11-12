module

public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRootNames
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Gaussian.Field
import Purelib.Tactic.Ring

/-! # The two value numerators at one retained genus-one reciprocal root

The original scaled root cache supplies its exact source root and prepared
reciprocal denominator. Scalar cancellation derives both value pullbacks;
the weighted numerator does not use a holomorphic Fin1 differential index.
No root, Point, coefficient model or possible observation is reacquired.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRootNames

open Purelib
open Purelib.Algebra.Field (ExplicitField)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Riemann.RootContinuation

/-- The actual genus-one root scale cancels the original inverse-coordinate Jacobian on the unit numerator. -/
private theorem unit_scale (source : Canonical) (nonzero : source ≠ 0) :
    factor 1 source * (-(source ^ 2) * 1) = -1 := by
  change source⁻¹ ^ 2 * (-(source ^ 2) * 1) = -1
  calc
    _ = -((source⁻¹ * source) ^ 2) := by ring1
    _ = -1 := by rewrite [Data.Gaussian.Basic.Canonical.inv_mul_cancel source nonzero]; ring1

/-- The actual genus-one root scale cancels the Jacobian on the retained coordinate numerator. -/
private theorem coordinate_scale (source : Canonical) (nonzero : source ≠ 0) :
    factor 1 source * (-(source ^ 2) * source) = -source := by
  change source⁻¹ ^ 2 * (-(source ^ 2) * source) = -source
  calc
    _ = -((source⁻¹ * source) ^ 2 * source) := by ring1
    _ = -source := by rewrite [Data.Gaussian.Basic.Canonical.inv_mul_cancel source nonzero]; ring1

/-- The retained reciprocal unit numerator has the original dx/y pullback, including its Jacobian sign. -/
def unit_pullback {parameter source : Canonical}
    {radicand : HyperellipticReciprocal.GaussianPolynomial}
    {original : CertifiedSquareRoot.Certificate parameter}
    (root : ScaledRoot original (factor 1 source) radicand source⁻¹) (nonzero : source ≠ 0) :
    NamedEquivalent
      (CoherentNamed.div (Coherence.exact (-1)) root.prepared.denominator root.prepared.apart).name
      (CoherentNamed.mul (Coherence.exact (-(source ^ 2)))
        (CoherentNamed.div (Coherence.exact 1) original.value original.apart)).name :=
  (quotient_scaled original.value original.apart (factor 1 source) (-1) (-(source ^ 2) * 1)
    root.prepared (unit_scale source nonzero)).trans
    (constant_mul_quotient (-(source ^ 2)) 1 original.value original.apart).symm

/-- The same retained reciprocal root carries the actual x dx/y numerator, without a holomorphic index surrogate. -/
def coordinate_pullback {parameter source : Canonical}
    {radicand : HyperellipticReciprocal.GaussianPolynomial}
    {original : CertifiedSquareRoot.Certificate parameter}
    (root : ScaledRoot original (factor 1 source) radicand source⁻¹) (nonzero : source ≠ 0) :
    NamedEquivalent
      (CoherentNamed.div (Coherence.exact (-source)) root.prepared.denominator root.prepared.apart).name
      (CoherentNamed.mul (Coherence.exact (-(source ^ 2)))
        (CoherentNamed.div (Coherence.exact source) original.value original.apart)).name :=
  (quotient_scaled original.value original.apart (factor 1 source) (-source) (-(source ^ 2) * source)
    root.prepared (coordinate_scale source nonzero)).trans
    (constant_mul_quotient (-(source ^ 2)) source original.value original.apart).symm

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRootNames

end
