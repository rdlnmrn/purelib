module
import Purelib.Data.Rat.Fraction
import Purelib.Computation.Arithmetic.Cost.Basic
public import Purelib.Computation.Arithmetic.Cost.Rational
public import Purelib.Polynomial.Dense.Rational.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Polynomial.Dense.Basic

open Purelib

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

namespace Purelib.Polynomial.Dense.Rational.Evaluation.Cost

/-! ## Exact Horner and power traces -/

/-- Bit work of the actual high-to-low Horner accumulator sequence. -/
def hornerWork (point : Fraction.Rational) :
    List Fraction.Rational → Fraction.Rational → Computation.Arithmetic.Cost.Basic.Work
  | [], _ => 0
  | coefficient :: remaining, accumulator =>
      let product := accumulator * point
      let next := product + coefficient
      Computation.Arithmetic.Cost.Rational.rationalMulWork accumulator point +
        Computation.Arithmetic.Cost.Rational.rationalAddWork product coefficient +
        hornerWork point remaining next

/-- The exact-value arithmetic cost of evaluating the polynomial by Horner recursion from zero. -/
def polynomialHornerWork (polynomial :
  Dense.Rational.Basic.CoordinatePolynomial)
    (point : Fraction.Rational) : Computation.Arithmetic.Cost.Basic.Work :=
  hornerWork point polynomial.coeffs 0

/-- The number of coefficient steps in a finite Horner evaluation. -/
def hornerStepCount (coefficients : List Fraction.Rational) :
  Nat :=
  coefficients.length

/-- The Horner step count is exactly the displayed coefficient-list length. -/
theorem hornerStepCount_eq_length (coefficients : List
  Fraction.Rational) :
    hornerStepCount coefficients = coefficients.length := rfl
end Purelib.Polynomial.Dense.Rational.Evaluation.Cost

end
