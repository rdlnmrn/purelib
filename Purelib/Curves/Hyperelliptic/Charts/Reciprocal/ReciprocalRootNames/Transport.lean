module

public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRootNames
import Purelib.Approximation.Gaussian.Division.Prepared.Equivalence
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence

/-! # The same scaled-root cache at an operationally identified original source

Only the source comparison of the existing denominator preparation changes.
The target radicand, denominator, apartness, square equation, algebraic
coefficient cache and inverse remain the actual retained input data.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRootNames.ScaledRoot

open Purelib.Riemann.RootContinuation
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence (coherentMul_respects)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)

variable {parameter factor point : Gaussian} {radicand : HyperellipticReciprocal.GaussianPolynomial}

/-- Reparent an actual scaled root along a comparison of its two original source certificates.

The original prepared-denominator transport retains its entire denominator
and apartness presentation. All remaining cached fields are the supplied
scaled root's actual fields; no polynomial evaluation or root producer runs.
-/
def transport {first second : CertifiedSquareRoot.Certificate parameter}
    (root : ScaledRoot first factor radicand point)
    (equivalent : NamedEquivalent first.value.name second.value.name) :
    ScaledRoot second factor radicand point :=
  let scaled := coherentMul_respects (Coherence.exact factor) (Coherence.exact factor)
    first.value second.value (NamedEquivalent.refl _) equivalent
  ⟨root.targetValue, root.targetValue_eq, root.radicand_eq,
    root.prepared.transport scaled, root.square, root.algebraic,
    root.inverse, root.inverse_eq, root.inverse_equivalent⟩

/-- Source transport retains the complete actual target root certificate, including its same denominator and guard. -/
theorem transport_certificate {first second : CertifiedSquareRoot.Certificate parameter}
    (root : ScaledRoot first factor radicand point)
    (equivalent : NamedEquivalent first.value.name second.value.name) :
    (root.transport equivalent).certificate = root.certificate := (rfl)

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRootNames.ScaledRoot

end
