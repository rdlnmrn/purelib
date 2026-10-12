module
import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Derivative
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Coprime.Basic
public import Purelib.Polynomial.Dense.Gaussian.Coprime.Operations
import Purelib.Polynomial.Dense.Gaussian.GCD
public import Purelib.Polynomial.Dense.Gaussian.Linear.Translated
public import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.Polynomial.Dense.Multiplication

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Gaussian.Field

open Purelib.Data

open Purelib.Polynomial

/-! Derivative, nonzero and squarefree certificates for the same retained translated coordinate. -/

public section

namespace Purelib.Polynomial.Dense.Gaussian.Linear.Translated.Squarefree

/-- The derivative of the translated coordinate polynomial is the constant polynomial one. -/
theorem translatedCoordinate_derivative (point :
  Gaussian.Basic.Canonical) :
    Dense.Gaussian.GCD.derivative (Dense.Gaussian.Linear.Translated.translatedCoordinate point) =
      Dense.Basic.DensePolynomial.constant 1 := by
  apply Dense.Basic.DensePolynomial.ext
  simp only [Dense.Gaussian.GCD.derivative, Dense.Derivative.derivative,
    Dense.Derivative.derivativeState,
    Dense.Gaussian.Linear.Translated.translatedCoordinate,
    -eq_self, -iff_self]
  rfl

/-- The translated coordinate polynomial is nonzero for every displayed Gaussian translation. -/
theorem translatedCoordinate_nonzero (point :
  Gaussian.Basic.Canonical) :
    (Dense.Gaussian.Linear.Translated.translatedCoordinate point).isZero = false := by
  change (⟨[1, -point]⟩ : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial).isZero = false
  rw [Dense.Basic.DensePolynomial.isZero, Dense.Basic.DensePolynomial.normalize_linear_of_leading_ne_zero one_ne_zero]
  rfl

/-- Construct a squarefree certificate for the translated coordinate polynomial.

Its derivative is one, so the original nonzero polynomial has the explicit constant-right coprimality certificate. -/
@[expose] def certificate (point :
  Gaussian.Basic.Canonical) :
    Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate
      (Dense.Gaussian.Linear.Translated.translatedCoordinate point) := by
  change Dense.Gaussian.Coprime.Basic.CoprimeCertificate (Dense.Gaussian.Linear.Translated.translatedCoordinate
    point)
    (Dense.Gaussian.GCD.derivative (Dense.Gaussian.Linear.Translated.translatedCoordinate point))
  rw [translatedCoordinate_derivative]
  exact Dense.Gaussian.Coprime.Operations.CoprimeCertificate.constantRight
    (translatedCoordinate_nonzero point)

end Purelib.Polynomial.Dense.Gaussian.Linear.Translated.Squarefree
