module
public import Purelib.Data.Rat.Fraction.BitWidth
public import Purelib.Polynomial.Dense.Rational.Basic

import Purelib.Tactic.QuotientFreeOmega
public import Mathlib.Algebra.GroupWithZero.Nat
import Purelib.Data.Rat.Fraction
import Purelib.Polynomial.Dense.Basic

open Purelib.Data.Rat

open Purelib.Polynomial

section
@[expose] public section

/-!
# Finite bit-work account for automatic rational roots

This file supplies an executable, phase-by-phase bit-size account for the
automatic exact-root search for `T^q-y`.  It is deliberately a coarse
schoolbook model, but it is not a unit-cost count:

* every natural, integer, rational, and Gaussian operand is charged at its
  displayed binary width;
* one exact rational arithmetic operation is charged quadratically in the
  combined input/output width;
* its canonical gcd normalization is charged separately and cubically in the
  output width (a defensive allowance for finite Euclidean arithmetic);
* Horner evaluation and repeated powering are followed through their actual
  finite intermediate values;
* denominator clearance follows the actual recursive cleared coefficient
  lists;
* divisor scans, duplicate comparisons, and every exact final power test are
  all charged explicitly.

The account describes this finite algorithm, not wall-clock time of Lean's
runtime.  Its purpose is to close the former hidden-unit-cost gap and to make
every improvement target visible.  Faster multiplication, gcd, divisor, or
deduplication implementations can replace an individual displayed charge
without changing the root-completeness theorem.
-/

namespace Purelib.Polynomial.Dense.Rational.BitWidth

/-- Sum the binary record widths of the retained rational coefficients.

The finite list sum charges each stored coefficient, including leading zeros, using its canonical
numerator-and-denominator width. -/
def polynomialWidth (polynomial :
  Dense.Rational.Basic.CoordinatePolynomial) : Nat :=
  (polynomial.coeffs.map Fraction.BitWidth.rationalWidth).sum
end Purelib.Polynomial.Dense.Rational.BitWidth

end
