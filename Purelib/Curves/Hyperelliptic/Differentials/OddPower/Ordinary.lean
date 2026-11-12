module
import Purelib.Polynomial.Dense.Gaussian.Basic

public import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic

/-! # Original ordinary polynomial differential specifications

The original differential and its coefficient reduction are retained whole.
The subtype certifies denominator power one; it introduces no new integrand,
source owner or coefficient cache.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic.OddPowerDifferential

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)

/-- A GIVEN original odd-power differential with its actual ordinary-denominator certificate. -/
abbrev Ordinary (radicand : CoefficientPolynomial) :=
  {differential : OddPowerDifferential radicand // differential.denominatorPairs = 0}

namespace Ordinary

/-- Construct the original coefficient specification with denominator pair count zero and retain that exact count. -/
def ofNumerator (radicand numerator : CoefficientPolynomial) (scale : Canonical) : Ordinary radicand :=
  ⟨OddPowerDifferential.ofCoefficients radicand numerator 0 scale, rfl⟩

/-- Read the actual scaled numerator of the SAME original certified ordinary differential. -/
@[expose] def numerator {radicand : CoefficientPolynomial} (differential : Ordinary radicand) : CoefficientPolynomial :=
  differential.val.numerator.scale differential.val.scale

/-- The selected ordinary numerator retains the original polynomial and scalar exactly. -/
theorem numerator_eq {radicand : CoefficientPolynomial} (differential : Ordinary radicand) :
    differential.numerator = differential.val.numerator.scale differential.val.scale := by rfl

end Ordinary

end Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic.OddPowerDifferential
