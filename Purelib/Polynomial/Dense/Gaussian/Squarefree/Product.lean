module
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Derivative
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Coprime.Basic
import Purelib.Polynomial.Dense.Gaussian.Coprime.Evaluation
public import Purelib.Polynomial.Dense.Gaussian.Coprime.Operations
import Purelib.Polynomial.Dense.Gaussian.GCD
public import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.Polynomial.Dense.Multiplication
import Mathlib.Algebra.Ring.Defs
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.Ring

open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense.Gaussian.Coprime.Basic (CoprimeCertificate)
open Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic (SquarefreeCertificate)

open Purelib.Polynomial

section
@[expose] public section

/-!
# Constructive squarefreeness of coprime products

The certificates below use only finite dense polynomial arithmetic, the
derivative product rule and displayed Bézout identities.  Their conversion
back to the executable Euclidean certificate uses the existing bounded
coefficient-candidate test, not extensionality over an infinite carrier.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Squarefree.Product

/-- Multiplication preserves squarefreeness when the two nonzero factors
are coprime.  No irreducible factorization or root enumeration is required. -/
def product {p q :
  Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    (pNonzero : p.isZero = false) (qNonzero : q.isZero = false)
    (pSquarefree : SquarefreeCertificate p)
    (qSquarefree : SquarefreeCertificate q)
    (coprime : CoprimeCertificate p q) :
    SquarefreeCertificate (p * q) := by
  let derivative := Dense.Gaussian.GCD.derivative (p * q)
  let leftProduct := Dense.Gaussian.Coprime.Operations.CoprimeCertificate.mulRight pNonzero pSquarefree coprime
  let rightProduct := Dense.Gaussian.Coprime.Operations.CoprimeCertificate.mulRight qNonzero
    (Dense.Gaussian.Coprime.Operations.CoprimeCertificate.symm coprime) qSquarefree
  let leftCertificate : CoprimeCertificate p derivative := by
    apply Dense.Gaussian.Coprime.Evaluation.coprimeCertificateOfIdentity p derivative (Or.inl pNonzero)
      (leftProduct.left - leftProduct.right * Dense.Gaussian.GCD.derivative q)
      leftProduct.right
    intro point
    have identity := leftProduct.identity point
    dsimp only [derivative]
    simp only [DensePolynomial.eval_sub, DensePolynomial.eval_mul,
      Dense.Gaussian.GCD.derivative,
      Dense.Derivative.eval_derivative_mul] at identity ⊢
    calc
      1 = _ := identity
      _ = _ := by ring1
  let rightCertificate : CoprimeCertificate q derivative := by
    apply Dense.Gaussian.Coprime.Evaluation.coprimeCertificateOfIdentity q derivative (Or.inl qNonzero)
      (rightProduct.left - rightProduct.right * Dense.Gaussian.GCD.derivative p)
      rightProduct.right
    intro point
    have identity := rightProduct.identity point
    dsimp only [derivative]
    simp only [DensePolynomial.eval_sub, DensePolynomial.eval_mul,
      Dense.Gaussian.GCD.derivative,
      Dense.Derivative.eval_derivative_mul] at identity ⊢
    calc
      1 = _ := identity
      _ = _ := by ring1
  apply Dense.Gaussian.Coprime.Evaluation.coprimeCertificateOfIdentity (p * q) derivative
    (Or.inl (DensePolynomial.isZero_mul_eq_false pNonzero qNonzero))
    (leftCertificate.left * rightCertificate.left)
    (leftCertificate.left * p * rightCertificate.right +
      leftCertificate.right * rightCertificate.left * q +
      leftCertificate.right * rightCertificate.right * derivative)
  intro point
  have leftIdentity := leftCertificate.identity point
  have rightIdentity := rightCertificate.identity point
  simp only [DensePolynomial.eval_add, DensePolynomial.eval_mul]
  calc
    1 = 1 * 1 := by ring1
    _ = (leftCertificate.left.eval point * p.eval point +
          leftCertificate.right.eval point * derivative.eval point) *
        (rightCertificate.left.eval point * q.eval point +
          rightCertificate.right.eval point * derivative.eval point) := by
      rw [← leftIdentity, ← rightIdentity]
    _ = _ := by ring1

end Purelib.Polynomial.Dense.Gaussian.Squarefree.Product

end
