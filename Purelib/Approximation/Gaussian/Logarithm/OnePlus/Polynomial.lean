module
public import Purelib.Approximation.Gaussian.Logarithm.OnePlus.Coefficient
import Purelib.Data.Rat.Alternating
import Purelib.Polynomial.Ascending.Rational.Basic
import Purelib.Polynomial.Ascending.Rational.Coefficientwise
public import Purelib.Polynomial.Ascending.Rational.Derivative
import Purelib.Polynomial.Ascending.Rational.Monomial

import Purelib.Tactic.QuotientFreeOmega
import Init.Prelude
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic

open Purelib

open Purelib.Approximation.Gaussian.Logarithm.OnePlus

open Purelib.Polynomial.Ascending.Rational

section
@[expose] public section

/-!
# Executable, limit-free differential laws for the logarithm

This module works with the finite local coordinate `log(1+u)`, on the
displayed rational disk `normSq u ≤ 1/4`.  Its relative forms and derivative
are finite alternating sums.  The reciprocal derivative law is expressed by
an exact finite geometric remainder and then by finite-request operational
equivalence.  No infinitesimal, limit, infinite series, or global logarithm
branch is introduced.
-/

namespace Purelib.Approximation.Gaussian.Logarithm.OnePlus.Polynomial

/-- The actual finite polynomial whose value is the local `log(1+u)` sample. -/
def log1pPolynomial : Nat →
  Purelib.Polynomial.Ascending.Rational.Basic.CoefficientPolynomial
  | 0 => Purelib.Polynomial.Ascending.Rational.Monomial.monomial 1 1
  | index + 1 =>
      Purelib.Polynomial.Ascending.Rational.Basic.add
        (log1pPolynomial index)
        (Purelib.Polynomial.Ascending.Rational.Monomial.monomial (index + 2)
          (Purelib.Approximation.Gaussian.Logarithm.OnePlus.Coefficient.alternatingCoefficient (index + 1)))

/-- The formal derivative target, a finite alternating geometric polynomial. -/
def log1pGeometricPolynomial : Nat →
  Purelib.Polynomial.Ascending.Rational.Basic.CoefficientPolynomial
  | 0 => Purelib.Polynomial.Ascending.Rational.Basic.constant 1
  | index + 1 =>
      Purelib.Polynomial.Ascending.Rational.Basic.add
        (log1pGeometricPolynomial index)
        (Purelib.Polynomial.Ascending.Rational.Monomial.monomial (index + 1)
          (Purelib.Data.Rat.Alternating.alternatingSign (index + 1)))

/-- The formal derivative of each finite one-plus logarithm polynomial is coefficientwise equal to the matching
alternating geometric polynomial. -/
theorem derivative_log1pPolynomial : ∀ index,
    Coefficientwise.CoefficientwiseEqual (Derivative.derivative
      (log1pPolynomial index))
      (log1pGeometricPolynomial index)
  | 0 => by
      exact Coefficientwise.coefficientwise_trans
        (Derivative.derivative_monomial_succ 0 1)
        (Coefficientwise.coefficientwise_trans
          (Monomial.coefficientwise_monomial_value 0
            (Coefficient.degree_mul_alternatingCoefficient 0))
          (Monomial.coefficientwise_monomial_zero 1))
  | index + 1 => by
      exact Coefficientwise.coefficientwise_trans
        (Derivative.derivative_add _ _)
        (Coefficientwise.coefficientwise_trans
          (Coefficientwise.coefficientwise_add
            (derivative_log1pPolynomial index)
            (Derivative.derivative_monomial_succ (index + 1)
              (Coefficient.alternatingCoefficient (index + 1))))
          (Coefficientwise.coefficientwise_add (Coefficientwise.coefficientwise_refl _)
            (Monomial.coefficientwise_monomial_value (index + 1)
              (Coefficient.degree_mul_alternatingCoefficient (index + 1)))))
end Purelib.Approximation.Gaussian.Logarithm.OnePlus.Polynomial

end
