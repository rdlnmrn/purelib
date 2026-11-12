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
import Purelib.Polynomial.Dense.Leading

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
  have valueIdentity := Factorization.Identity.eval_factorization factorization point
  have derivativeIdentity :=
    Factorization.Identity.eval_derivative_factorization factorization point
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
  rw [Factorization.Identity.eval_factorization factorization point] at original
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
    (Factorization.Identity.factorization_swap factorization)

/-- A polynomial coprime to one of its displayed multiples has degree zero.

Substituting the retained factorization in the original Bézout identity gives
an exact polynomial inverse for the divisor. The existing finite product-degree
certificate for the constant one then forces the divisor's degree to be zero.
-/
theorem natDegree_eq_zero_of_divides
    {p q cofactor : CoefficientPolynomial}
    (coprime : CoprimeCertificate p q) (nonzero : p.isZero = false)
    (factorization : ProductIdentity q p cofactor) :
    p.natDegree = 0 := by
  let inverse := coprime.left + coprime.right * cofactor
  have oneLeading := Dense.Leading.LeadingTerm.constant (K := Data.Gaussian.Basic.Canonical) one_ne_zero
  have unitIdentity : ProductIdentity (DensePolynomial.constant 1) p inverse := by
    apply Factorization.Identity.factorizationOfCandidateEvals
    intro point _
    have identity := coprime.identity point
    rewrite [Factorization.Identity.eval_factorization factorization point] at identity
    simp only [DensePolynomial.eval_constant]
    change 1 = p.eval point * (coprime.left + coprime.right * cofactor).eval point
    rewrite [DensePolynomial.eval_add, DensePolynomial.eval_mul]
    calc
      1 = coprime.left.eval point * p.eval point +
          coprime.right.eval point * (p.eval point * cofactor.eval point) := identity
      _ = _ := by ring1
  have inverseNonzero := Factorization.Identity.right_isZero_false
    oneLeading.nonzero oneLeading.normalized unitIdentity
  have degrees := Factorization.Identity.factor_natDegree_add
    oneLeading.nonzero oneLeading.normalized nonzero inverseNonzero unitIdentity
  rewrite [oneLeading.degree_eq] at degrees
  exact Nat.eq_zero_of_le_zero ((Nat.le_add_right p.natDegree inverse.natDegree).trans_eq degrees)

end Purelib.Polynomial.Dense.Gaussian.Coprime.Factors

end
