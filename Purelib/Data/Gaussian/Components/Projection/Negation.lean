module

public import Purelib.Data.Gaussian.Components.Projection

/-!
# Negation of the original embedded Gaussian coordinate projections

Both embedded projections preserve the sign of the original retained reading.
The equalities compare their exact coordinates, without constructing a new
owner or changing the original Gaussian carrier.
-/

public section

namespace Purelib.Data.Gaussian.Components.Projection

open Purelib.Data.Gaussian.Basic (Canonical ext)
open Purelib.Data.Rat

/-- Negation commutes with the original embedded real projection. -/
theorem realPart_neg (value : Canonical) : realPart (-value) = -realPart value := by
  apply ext
  · rfl
  · change (0 : Fraction.Rational) = -0
    decide +kernel

/-- Negation commutes with the original embedded imaginary projection. -/
theorem imaginaryPart_neg (value : Canonical) : imaginaryPart (-value) = -imaginaryPart value := by
  apply ext
  · change (0 : Fraction.Rational) = -0
    decide +kernel
  · rfl

end Purelib.Data.Gaussian.Components.Projection
