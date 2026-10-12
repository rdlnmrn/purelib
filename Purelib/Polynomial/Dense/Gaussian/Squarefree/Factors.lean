module
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Derivative
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Coprime.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Factorization.Identity
import Purelib.Polynomial.Dense.Gaussian.GCD
public import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.Polynomial.Dense.Multiplication

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Coprime.Basic
import Purelib.Tactic.Ring

open Purelib.Polynomial.Dense.Gaussian.Factorization.Identity (ProductIdentity)
open Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic (SquarefreeCertificate)

open Purelib.Polynomial

section
@[expose] public section

/-!
# Squarefreeness inherited by finite displayed factors

An explicit Bézout identity is converted back into the executable Euclidean
coprimality certificate by checking only the finite candidate list of one
coefficient difference.  The direct derivative product rule then transports
a squarefree certificate through either side of a displayed factorization.

This is the algebraic bridge needed to split overlapping squarefree
occurrences while retaining proof-bearing inputs for the numerical RFAP.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Squarefree.Factors

/-- Every displayed nonzero left factor of a squarefree polynomial is
squarefree. -/
def leftFactorSquarefree
    {p left right : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    (squarefree : SquarefreeCertificate p)
    (leftNonzero : left.isZero = false)
    (factorization : ProductIdentity p left right) :
    SquarefreeCertificate left := by
  let leftCoefficient :=
    squarefree.left * right +
      squarefree.right * Dense.Gaussian.GCD.derivative right
  let derivativeCoefficient := squarefree.right * right
  apply Dense.Gaussian.Coprime.Evaluation.coprimeCertificateOfIdentity left
    (Dense.Gaussian.GCD.derivative left) (Or.inl leftNonzero)
      leftCoefficient derivativeCoefficient
  intro point
  have valueIdentity := Dense.Gaussian.Factorization.Identity.eval_factorization factorization point
  have derivativeIdentity :=
    Dense.Gaussian.Factorization.Identity.eval_derivative_factorization factorization point
  have original := squarefree.identity point
  rw [valueIdentity, derivativeIdentity] at original
  simp only [Dense.Gaussian.GCD.derivative] at original
  rw [Dense.Derivative.eval_derivative_mul] at original
  dsimp only [leftCoefficient, derivativeCoefficient]
  simp only [Dense.Basic.DensePolynomial.eval_add, Dense.Basic.DensePolynomial.eval_mul]
  calc
    1 = squarefree.left.eval point *
          (left.eval point * right.eval point) +
        squarefree.right.eval point *
          ((Dense.Gaussian.GCD.derivative left).eval point *
              right.eval point +
            left.eval point *
              (Dense.Gaussian.GCD.derivative right).eval point) := original
    _ = (squarefree.left.eval point * right.eval point +
          squarefree.right.eval point *
            (Dense.Gaussian.GCD.derivative right).eval point) *
            left.eval point +
        (squarefree.right.eval point * right.eval point) *
          (Dense.Gaussian.GCD.derivative left).eval point := by ring1

/-- Every displayed nonzero right factor of a squarefree polynomial is
squarefree. -/
def rightFactorSquarefree
    {p left right : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    (squarefree : SquarefreeCertificate p)
    (rightNonzero : right.isZero = false)
    (factorization : ProductIdentity p left right) :
    SquarefreeCertificate right := by
  have swapped : ProductIdentity p right left := by
    exact Dense.Gaussian.Factorization.Identity.factorization_swap factorization
  exact leftFactorSquarefree squarefree rightNonzero swapped

end Purelib.Polynomial.Dense.Gaussian.Squarefree.Factors

end
