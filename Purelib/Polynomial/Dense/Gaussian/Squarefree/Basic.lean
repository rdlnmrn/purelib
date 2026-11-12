module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Coprime.Basic
import Purelib.Polynomial.Dense.Gaussian.GCD
import Purelib.Polynomial.Dense.Derivative
import Purelib.Polynomial.Dense.Arithmetic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Polynomial.Dense.Evaluation

open Purelib.Data

open Purelib.Polynomial

section
@[expose] public section

/-!
# Finite coprimality and squarefree certificates

A certificate records that the output of executable extended Euclid is one
displayed nonzero constant.  Rescaling its returned Bézout coefficients gives
an identity equal to `1` at every queried point.  No root set, coefficient
extensionality over an infinite carrier, or sparse polynomial is used.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic

/-- Squarefreeness is the finite coprimality certificate for a polynomial
and its automatic derivative. -/
abbrev SquarefreeCertificate (p :
  Basic.CanonicalCoefficients.CoefficientPolynomial) :=
  Dense.Gaussian.Coprime.Basic.CoprimeCertificate p (Dense.Gaussian.GCD.derivative p)

/-- A squarefree certificate excludes the represented zero curve polynomial.

A zero coefficient table and its original finite derivative both vanish.
The same retained Bézout identity would then equate scalar one with zero. -/
theorem polynomial_nonzero {p : Basic.CanonicalCoefficients.CoefficientPolynomial}
    (certificate : SquarefreeCertificate p) : p.isZero = false := by
  cases zero : p.isZero with
  | false => rfl
  | true =>
      have derivativeZero : Dense.Gaussian.GCD.derivative p = 0 := by
        change Dense.Derivative.derivative p = 0
        rewrite [← Dense.Derivative.derivative_normalize p,
          Dense.Basic.DensePolynomial.normalize_eq_zero_of_isZero zero, Dense.Derivative.derivative_zero]
        rfl
      have derivativeValue : (Dense.Gaussian.GCD.derivative p).eval (0 : Gaussian.Basic.Canonical) = 0 :=
        (congrArg (fun value : Basic.CanonicalCoefficients.CoefficientPolynomial =>
          value.eval (0 : Gaussian.Basic.Canonical)) derivativeZero).trans
            (Dense.Basic.DensePolynomial.eval_zero _)
      have identity := certificate.identity (0 : Gaussian.Basic.Canonical)
      rewrite [Dense.Basic.DensePolynomial.eval_eq_zero_of_isZero zero, derivativeValue,
        Gaussian.Basic.mul_zero, Gaussian.Basic.mul_zero, Gaussian.Basic.zero_add] at identity
      exact False.elim ((by decide +kernel : (1 : Gaussian.Basic.Canonical) ≠ 0) identity)

/-- A squarefree certificate makes the polynomial value or its derivative value nonzero at every Gaussian point. -/
theorem value_or_derivative_ne_zero {p :
  Basic.CanonicalCoefficients.CoefficientPolynomial}
    (certificate : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p) (z : Gaussian.Basic.Canonical) :
    p.eval z ≠ 0 ∨ (Dense.Gaussian.GCD.derivative p).eval z ≠ 0 :=
  certificate.eval_ne_zero z

end Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic

end
