module
import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Ascending.Rational.Derivative
import Purelib.Polynomial.Ascending.Rational.GaussianEvaluation
public import Purelib.Polynomial.Ascending.Rational.Secant
public import Purelib.RationalFunctions.Ascending.Rational.Basic

import Purelib.Tactic.QuotientFreeOmega

open Purelib.Data.Gaussian.Basic (Canonical)

section
@[expose] public section

/-!
# Finite divided differences and limit-free algebraic calculus

The derivative in this module is obtained by constructing a secant kernel
before putting its two displayed arguments equal.  No quotient by `x-y`,
limit, infinitesimal, or completed function graph is used.  Ordinary finite
polynomials, signed powers, and finite Laurent term lists are all evaluated by
structural recursion.
-/

namespace Purelib.RationalFunctions.Ascending.Rational.Basic
namespace RationalPolynomial

open Purelib.Data
open Purelib.Polynomial
open Purelib.RationalFunctions
/-- Evaluate the ascending numerator and denominator and take their Gaussian field quotient.

This uses the total field division operation; cancellation identities separately require denominator nonzeroness. -/
def eval (expression :
  Ascending.Rational.Basic.RationalPolynomial) (x : Canonical) : Canonical :=
  Ascending.Rational.GaussianEvaluation.eval expression.numerator x /
    Ascending.Rational.GaussianEvaluation.eval expression.denominator x

/-- Compute the two-point rational secant kernel from the numerator and denominator polynomial kernels.

The numerator combines the two polynomial divided differences by the quotient rule. Its denominator is the product of
the denominator evaluations at the two supplied points. -/
def kernel (expression :
  Ascending.Rational.Basic.RationalPolynomial) (x y : Canonical) : Canonical :=
  let numeratorY :=
    Ascending.Rational.GaussianEvaluation.eval expression.numerator y
  let denominatorX :=
    Ascending.Rational.GaussianEvaluation.eval expression.denominator x
  let denominatorY :=
    Ascending.Rational.GaussianEvaluation.eval expression.denominator y
  (Ascending.Rational.Secant.polynomialKernel expression.numerator x y * denominatorY -
      numeratorY * Ascending.Rational.Secant.polynomialKernel expression.denominator x y) /
    (denominatorX * denominatorY)

/-- Evaluate the formal quotient-rule expression at one Gaussian point.

The numerator combines the evaluated formal derivatives, and the denominator is the square of the evaluated denominator.
The expression uses total Gaussian division. -/
def derivativeEval (expression :
  Ascending.Rational.Basic.RationalPolynomial) (x : Canonical) :
    Canonical :=
  let numerator :=
    Ascending.Rational.GaussianEvaluation.eval expression.numerator x
  let denominator :=
    Ascending.Rational.GaussianEvaluation.eval expression.denominator x
  let numeratorDerivative :=
    Ascending.Rational.GaussianEvaluation.eval
      (Ascending.Rational.Derivative.derivative expression.numerator) x
  let denominatorDerivative :=
    Ascending.Rational.GaussianEvaluation.eval
      (Ascending.Rational.Derivative.derivative expression.denominator) x
  (numeratorDerivative * denominator - numerator * denominatorDerivative) /
    (denominator * denominator)
end RationalPolynomial

end Purelib.RationalFunctions.Ascending.Rational.Basic

end
