module
import Purelib.Data.Rat.Fraction
public import Purelib.Computation.Arithmetic.Cost.Integer
public import Purelib.Computation.Arithmetic.Cost.Natural
public import Purelib.Computation.Arithmetic.Cost.Rational
import Purelib.Data.Rat.Fraction.Basic
public import Purelib.Polynomial.Dense.Rational.Denominator

import Purelib.Tactic.QuotientFreeOmega
public import Mathlib.Algebra.GroupWithZero.Nat
import Purelib.Computation.Arithmetic.Cost.Basic

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

namespace Purelib.Polynomial.Dense.Rational.Clearance.Cost

/-- Core work of the exact structural denominator-clearance recursion. -/
def clearanceCoreCost : List Fraction.Rational → Nat
  | [] => 0
  | coefficient :: remaining =>
      let head := Fraction.Basic.representative coefficient
      let tail := Dense.Rational.Denominator.clear remaining
      clearanceCoreCost remaining +
        Computation.Arithmetic.Cost.Natural.natMultiplicationCost head.den tail.denominator +
        Computation.Arithmetic.Cost.Integer.intMultiplicationCost head.num (tail.denominator : Int) +
        (tail.coefficients.map
          (fun value => Computation.Arithmetic.Cost.Integer.intMultiplicationCost (head.den : Int) value)).sum

/-- Separate the core and normalization charges of rational denominator clearing.

The core follows the exact recursive cleared coefficient lists; normalization is charged for each original rational
coefficient. -/
def clearanceWork (coefficients : List Fraction.Rational) :
  Computation.Arithmetic.Cost.Basic.Work :=
  { core := clearanceCoreCost coefficients
    normalization :=
      (coefficients.map (fun value => Computation.Arithmetic.Cost.Rational.normalizationCharge value)).sum }
end Purelib.Polynomial.Dense.Rational.Clearance.Cost

end
