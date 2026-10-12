module
import Purelib.Polynomial.Dense.Basic
import Purelib.Data.Gaussian.Field
public import Purelib.Polynomial.Dense.Gaussian.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Gaussian.Basic

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)

open Purelib.Data

open Purelib.Polynomial

section
@[expose] public section

/-!
# Choice-free global winding on a finite constructive square

This module develops the coefficient-computed large-square theorem entirely
over the explicit constructive fraction and Gaussian representations.  Its
first layer computes the winding of the coordinate polynomial symbolically;
later layers transfer that value to a general positive-degree polynomial.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Coefficients.Tail

/-- Normalized finite coefficient tail, containing exactly the slots below
the displayed leading term. -/
def lowerCoefficients (p :
  CoefficientPolynomial) : List Gaussian.Basic.Canonical :=
  p.normalize.coeffs.tail

/-- For a nonzero polynomial, the number of coefficients below the leading term equals its degree. -/
theorem lowerCoefficients_length {p :
  CoefficientPolynomial}
    (nonzero : p.isZero = false) :
    (lowerCoefficients p).length = p.natDegree := by
  obtain ⟨tail, coefficients, length⟩ := Dense.Basic.DensePolynomial.normalized_coeffs_shape nonzero
  unfold lowerCoefficients
  rw [coefficients]
  exact length

/-- Executable polynomial consisting of exactly the normalized coefficient
slots below the leading term. -/
def lowerTermsPolynomial (p :
  CoefficientPolynomial) : (Dense.Basic.DensePolynomial
    Gaussian.Basic.Canonical) :=
  ⟨lowerCoefficients p⟩
end Purelib.Polynomial.Dense.Gaussian.Coefficients.Tail

end
