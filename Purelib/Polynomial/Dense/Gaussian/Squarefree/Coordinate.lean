module
import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Derivative
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Coefficients.Constants
import Purelib.Polynomial.Dense.Gaussian.Coprime.Basic
public import Purelib.Polynomial.Dense.Gaussian.Coprime.CoordinatePower
import Purelib.Polynomial.Dense.Gaussian.Coprime.Evaluation
import Purelib.Polynomial.Dense.Gaussian.GCD
import Purelib.Polynomial.Dense.Gaussian.Reciprocal
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
public import Purelib.Polynomial.Dense.Gaussian.Squarefree.Product
public import Purelib.Polynomial.Dense.Gaussian.Squarefree.Transport
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Multiplication
import Purelib.Tactic.Ring

open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic (SquarefreeCertificate)

open Purelib.Data

open Purelib.Polynomial

section
/-!
# Executable squarefreeness under finite coefficient reversal

Clear the reciprocal denominators in the original finite Bézout identity.
This gives a power of the coordinate in the ideal of the reversed polynomial
and its derivative. The reversed constant coefficient is the original
nonzero leading coefficient; a finite recursive Bézout calculation removes
that coordinate power. No root enumeration or nonzero affine constant term
is assumed.
-/

@[expose] public section

namespace Purelib.Polynomial.Dense.Gaussian.Squarefree.Coordinate

/-- Construct the squarefree certificate of the coordinate polynomial.

Its derivative evaluates to one, yielding an explicit constant Bézout cofactor. -/
def coordinateSquarefree :
  SquarefreeCertificate Dense.Gaussian.Coefficients.Constants.coordinate :=
  by
  apply Dense.Gaussian.Coprime.Evaluation.coprimeCertificateOfIdentity Dense.Gaussian.Coefficients.Constants.coordinate
    (Dense.Gaussian.GCD.derivative Dense.Gaussian.Coefficients.Constants.coordinate)
    (Or.inl (by decide)) 0 (DensePolynomial.constant 1)
  intro point
  have derivativeValue :
      (Dense.Gaussian.GCD.derivative Dense.Gaussian.Coefficients.Constants.coordinate).eval point = 1 := by
    rw [Dense.Gaussian.GCD.derivative,
      Dense.Derivative.eval_derivative]
    simp only [Dense.Gaussian.Coefficients.Constants.coordinate, Dense.Derivative.evalDerivativeCoeffs,
      List.foldl_cons, List.foldl_nil,
      Dense.Derivative.evalDerivativeStep,
      Gaussian.Basic.zero_mul, Gaussian.Basic.zero_add, Gaussian.Basic.one_mul, Gaussian.Basic.add_zero, -eq_self,
        -iff_self]
    rfl
  rw [DensePolynomial.eval_zero, DensePolynomial.eval_constant, derivativeValue]
  ring1

/-- Adjoin exactly one simple coordinate factor to a squarefree polynomial
which is nonzero at the origin.

The retained origin witness supplies the original coprime coordinate factor, and the same shifted polynomial receives
the resulting squarefree certificate. -/
def shiftOneSquarefree (polynomial :
  Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (nonzero : polynomial.isZero = false)
    (squarefree : SquarefreeCertificate polynomial) (originNonzero :
      polynomial.eval 0 ≠ 0) :
    SquarefreeCertificate (DensePolynomial.shift 1 polynomial)
      := by
  have coordinateValue (point : Gaussian.Basic.Canonical) : Dense.Gaussian.Coefficients.Constants.coordinate.eval point
    = point := by
    simp only [Dense.Gaussian.Coefficients.Constants.coordinate, DensePolynomial.eval,
      DensePolynomial.evalCoeffs, List.foldl_cons, List.foldl_nil,
      Gaussian.Basic.zero_mul, Gaussian.Basic.zero_add, Gaussian.Basic.one_mul, Gaussian.Basic.add_zero, -eq_self,
        -iff_self]
    rfl
  let power := Dense.Gaussian.Coprime.CoordinatePower.ofOrigin polynomial originNonzero 1
  let coprime : Dense.Gaussian.Coprime.Basic.CoprimeCertificate polynomial
    Dense.Gaussian.Coefficients.Constants.coordinate :=
    Dense.Gaussian.Coprime.Evaluation.coprimeCertificateOfIdentity polynomial
      Dense.Gaussian.Coefficients.Constants.coordinate (Or.inl nonzero)
      power.left power.right (by intro point; rw [coordinateValue]; simpa only [pow_one] using power.identity point)
  let product := Dense.Gaussian.Squarefree.Product.product nonzero (show
    Dense.Gaussian.Coefficients.Constants.coordinate.isZero = false by decide)
    squarefree coordinateSquarefree coprime
  exact Dense.Gaussian.Squarefree.Transport.ofSameValues (polynomial * Dense.Gaussian.Coefficients.Constants.coordinate)
    (DensePolynomial.shift 1 polynomial) (Dense.Gaussian.Reciprocal.shifted_nonzero polynomial nonzero 1)
    product (by
        intro point;
        rw [DensePolynomial.eval_mul, coordinateValue, DensePolynomial.eval_shift, pow_one])

end Purelib.Polynomial.Dense.Gaussian.Squarefree.Coordinate

end
