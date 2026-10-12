module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Coprime.Basic
import Purelib.Polynomial.Dense.Gaussian.GCD

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

/-- A squarefree certificate makes the polynomial value or its derivative value nonzero at every Gaussian point. -/
theorem value_or_derivative_ne_zero {p :
  Basic.CanonicalCoefficients.CoefficientPolynomial}
    (certificate : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p) (z : Gaussian.Basic.Canonical) :
    p.eval z ≠ 0 ∨ (Dense.Gaussian.GCD.derivative p).eval z ≠ 0 :=
  certificate.eval_ne_zero z

end Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic

end
