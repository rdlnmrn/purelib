module
import Purelib.Polynomial.Dense.Gaussian.Basic

public import Purelib.Riemann.Readings.PreparedPrimitiveSamples
public import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Ordinary

/-! # One interpretation for legacy and ordinary-polynomial numerator requests

No choice uses the original differential numerator and legacy request route.
A given certified ordinary specification uses its actual scaled polynomial,
while retaining that same original specification for common-model requests.
-/

public section

namespace Purelib.Riemann.Readings.PreparedPrimitiveSamples

open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic.OddPowerDifferential (Ordinary)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)

/-- Interpret the original differential context or the supplied genuine ordinary polynomial specification. -/
@[expose] def numerator (radicand : CoefficientPolynomial) {genus : Nat} (differential : Differential genus)
    (polynomial : Option (Ordinary radicand) := none) : CoefficientPolynomial :=
  match polynomial with
  | none => differentialNumerator differential
  | some ordinary => ordinary.numerator

/-- The default interpretation is exactly the original retained holomorphic numerator. -/
theorem numerator_none (radicand : CoefficientPolynomial) {genus : Nat} (differential : Differential genus) :
    numerator radicand differential none = differentialNumerator differential := by rfl

/-- A supplied ordinary specification retains its actual scaled polynomial without a Fin-genus relabeling. -/
theorem numerator_some {radicand : CoefficientPolynomial} {genus : Nat}
    (differential : Differential genus) (ordinary : Ordinary radicand) :
    numerator radicand differential (some ordinary) = ordinary.val.numerator.scale ordinary.val.scale := by rfl

end Purelib.Riemann.Readings.PreparedPrimitiveSamples
