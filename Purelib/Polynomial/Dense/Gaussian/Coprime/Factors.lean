module
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Derivative
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Coprime.Basic
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
import Purelib.Tactic.Ring

open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Dense.Gaussian.Coprime.Basic (CoprimeCertificate)
open Purelib.Polynomial.Dense.Gaussian.Factorization.Identity (ProductIdentity)

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

namespace Purelib.Polynomial.Dense.Gaussian.Coprime.Factors

/-- The two nonzero displayed factors of a squarefree product are coprime. -/
def factorsCoprime
    {p left right : CoefficientPolynomial}
    (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p)
    (leftNonzero : left.isZero = false)
    (factorization : ProductIdentity p left right) :
    CoprimeCertificate left right := by
  let leftCoefficient :=
    squarefree.left * right +
      squarefree.right * Dense.Gaussian.GCD.derivative right
  let rightCoefficient :=
    squarefree.right * Dense.Gaussian.GCD.derivative left
  apply Dense.Gaussian.Coprime.Evaluation.coprimeCertificateOfIdentity left right (Or.inl leftNonzero)
    leftCoefficient rightCoefficient
  intro point
  have valueIdentity := Dense.Gaussian.Factorization.Identity.eval_factorization factorization point
  have derivativeIdentity :=
    Dense.Gaussian.Factorization.Identity.eval_derivative_factorization factorization point
  have original := squarefree.identity point
  rw [valueIdentity, derivativeIdentity] at original
  simp only [Dense.Gaussian.GCD.derivative] at original
  rw [Dense.Derivative.eval_derivative_mul] at original
  dsimp only [leftCoefficient, rightCoefficient]
  simp only [DensePolynomial.eval_add, DensePolynomial.eval_mul]
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
        (squarefree.right.eval point *
            (Dense.Gaussian.GCD.derivative left).eval point) *
          right.eval point := by ring1

/-- A displayed nonzero left divisor inherits coprimality with the other
polynomial. -/
def coprimeLeftFactor
    {p q left right : CoefficientPolynomial}
    (coprime : CoprimeCertificate p q)
    (leftNonzero : left.isZero = false)
    (factorization : ProductIdentity p left right) :
    CoprimeCertificate left q := by
  let leftCoefficient := coprime.left * right
  apply Dense.Gaussian.Coprime.Evaluation.coprimeCertificateOfIdentity left q (Or.inl leftNonzero)
    leftCoefficient coprime.right
  intro point
  have original := coprime.identity point
  rw [Dense.Gaussian.Factorization.Identity.eval_factorization factorization point] at original
  dsimp only [leftCoefficient]
  simp only [DensePolynomial.eval_mul]
  calc
    1 = coprime.left.eval point *
          (left.eval point * right.eval point) +
        coprime.right.eval point * q.eval point := original
    _ = (coprime.left.eval point * right.eval point) *
          left.eval point + coprime.right.eval point * q.eval point := by
      ring1

/-- A displayed nonzero right divisor inherits coprimality with the other
polynomial. -/
def coprimeRightFactor
    {p q left right : CoefficientPolynomial}
    (coprime : CoprimeCertificate p q)
    (rightNonzero : right.isZero = false)
    (factorization : ProductIdentity p left right) :
    CoprimeCertificate right q :=
  coprimeLeftFactor coprime rightNonzero
    (Dense.Gaussian.Factorization.Identity.factorization_swap factorization)
end Purelib.Polynomial.Dense.Gaussian.Coprime.Factors

end
