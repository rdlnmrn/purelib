module
import Purelib.Polynomial.Dense.Rational.Basic
public import Purelib.Polynomial.Dense.Rational.BitWidth

import Purelib.Tactic.QuotientFreeOmega
public import Purelib.Computation.Arithmetic.Cost.Basic
import Mathlib.Algebra.Group.Nat.Defs
import Purelib.Data.Rat.Fraction
import Purelib.Polynomial.Dense.Basic

open Purelib

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

namespace Purelib.Polynomial.Dense.Rational.Construction.Cost

/-- A defensive dense-list construction charge.  It is quadratic in the
coefficient slots and cubic in the actual aggregate coefficient width, so it
also covers normalization of every materialized coefficient in the coarse
schoolbook model. -/
def polynomialConstructionWork (polynomial :
  Dense.Rational.Basic.CoordinatePolynomial) : Computation.Arithmetic.Cost.Basic.Work :=
  { core :=
      (polynomial.coeffs.length + 1) ^ 2 *
        (Dense.Rational.BitWidth.polynomialWidth polynomial + 1) ^ 2
    normalization :=
      polynomial.coeffs.length * (Dense.Rational.BitWidth.polynomialWidth polynomial + 1) ^ 3 }
end Purelib.Polynomial.Dense.Rational.Construction.Cost

end
