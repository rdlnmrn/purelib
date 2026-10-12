module
public import Purelib.Polynomial.Dense.Rational.Bounds.Quadratic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Dense.Basic

open Purelib.Polynomial.Dense.Rational.Bounds

section
@[expose] public section

/-!
# Executable quadratic separation proposals

Completing the square supplies a global coordinate floor when interval Horner
evaluation loses the dependency between occurrences of the parameter.  A zero
proposal is not a root certificate.  Constants and linear polynomials retain
their interval bounds in the caller; no division is attempted for a zero
quadratic coefficient.  All arithmetic uses the existing finite coefficient
and ordered-fraction dependency route of `PolynomialEnclosures`.
-/

namespace Test.Polynomial.QuadraticBounds

/-- Exact completing-square proposals recognize positive and negative definite quadratics and retain inconclusive zero
floors for the other displayed degrees. -/
theorem quadratic_regressions :
    (Quadratic.prepare ⟨[16, -16, 5]⟩).coordinateFloor = 1 ∧
      (Quadratic.prepare ⟨[-16, 16, -5]⟩).coordinateFloor = 1 ∧
      (Quadratic.prepare ⟨[0, 16, -16, 5]⟩).coordinateFloor = 1 ∧
      (Quadratic.prepare ⟨[1, 0, -1]⟩).coordinateFloor = 0 ∧
      (Quadratic.prepare ⟨[0, 1, 1]⟩).coordinateFloor = 0 ∧
      (Quadratic.prepare ⟨[2]⟩).coordinateFloor = 0 := by
  decide +kernel

end Test.Polynomial.QuadraticBounds

end
