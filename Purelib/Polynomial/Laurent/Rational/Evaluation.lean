module
public import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Gaussian.Basic
public import Purelib.Algebra.Power.Gaussian.Signed.Secant
import Purelib.Data.Gaussian.Scale
public import Purelib.Polynomial.Laurent.Rational.Basic

import Purelib.Tactic.QuotientFreeOmega

open Purelib

open Purelib.Data

open Purelib.Polynomial

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

namespace Purelib.Polynomial.Laurent.Rational.Basic

/-- Evaluate the term's signed power at the displayed Gaussian input and scale by its rational coefficient. -/
def LaurentTerm.eval (term : Laurent.Rational.Basic.LaurentTerm) (x :
  Gaussian.Basic.Canonical) : Gaussian.Basic.Canonical :=
  Gaussian.Scale.scale term.coefficient
    (Algebra.Power.Gaussian.Signed.Secant.signedPower x term.exponent)

/-- Scale the finite signed-power secant kernel by the term's rational coefficient. -/
def LaurentTerm.kernel (term : Laurent.Rational.Basic.LaurentTerm) (x y
  : Gaussian.Basic.Canonical) : Gaussian.Basic.Canonical :=
  Gaussian.Scale.scale term.coefficient
    (Algebra.Power.Gaussian.Signed.Secant.signedPowerKernel x y term.exponent)

/-- Scale the signed-power derivative value by the term's rational coefficient. -/
def LaurentTerm.derivativeEval (term :
  Laurent.Rational.Basic.LaurentTerm) (x : Gaussian.Basic.Canonical) : Gaussian.Basic.Canonical :=
  Gaussian.Scale.scale term.coefficient
    (Algebra.Power.Gaussian.Signed.Secant.signedPowerDerivative x term.exponent)

/-- Evaluate and sum the finite displayed Laurent term list. -/
def LaurentPolynomial.eval (polynomial :
  Laurent.Rational.Basic.LaurentPolynomial)
    (x : Gaussian.Basic.Canonical) : Gaussian.Basic.Canonical :=
  Gaussian.Norm.Sum.Basic.DividedDifference.sumGaussian (polynomial.terms.map fun term => term.eval x)

/-- Sum the finite termwise secant kernels at the two displayed Gaussian inputs. -/
def LaurentPolynomial.kernel (polynomial :
  Laurent.Rational.Basic.LaurentPolynomial)
    (x y : Gaussian.Basic.Canonical) : Gaussian.Basic.Canonical :=
  Gaussian.Norm.Sum.Basic.DividedDifference.sumGaussian (polynomial.terms.map fun term => term.kernel x y)

/-- Sum the finite termwise derivative evaluations at the displayed input. -/
def LaurentPolynomial.derivativeEval (polynomial :
  Laurent.Rational.Basic.LaurentPolynomial)
    (x : Gaussian.Basic.Canonical) : Gaussian.Basic.Canonical :=
  Gaussian.Norm.Sum.Basic.DividedDifference.sumGaussian (polynomial.terms.map fun term => term.derivativeEval x)

end Purelib.Polynomial.Laurent.Rational.Basic

end
