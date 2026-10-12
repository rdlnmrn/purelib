module
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Coprime.Basic
public import Purelib.Polynomial.Dense.Gaussian.Coprime.Evaluation
import Purelib.Polynomial.Dense.Multiplication

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Gaussian.Field
import Purelib.Tactic.Ring
import Purelib.Data.Bool.Decide

/-!
# Operations on retained coprimality certificates

Swapping inputs exchanges the original Bezout coefficients. Nonzero constants
supply inverse-scalar unit identities, and multiplying two displayed identities
retains the three-term coefficient polynomial and ordered right-coefficient product.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Coprime.Operations.CoprimeCertificate

open Purelib.Polynomial.Dense.Basic
open _root_.Purelib.Polynomial.Dense.Basic renaming CoefficientPolynomial -> Dense
open Purelib.Polynomial.Dense.Gaussian
open Purelib.Polynomial.Dense.Gaussian.Basic
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Bool

/-- Swap the retained coprime inputs and their ordered Bezout coefficients.

The same displayed coefficients certify the reversed scalar identity. Both
inputs cannot be zero, so the original unit identity supplies the nonzero branch. -/
@[expose] public def symm
    {p q : Basic.CanonicalCoefficients.CoefficientPolynomial} (coprime : Basic.CoprimeCertificate p q) :
    Basic.CoprimeCertificate q p := by
  have someNonzero : q.isZero = false ∨ p.isZero = false := by
    by_cases pZero : p.isZero = true
    · by_cases qZero : q.isZero = true
      · have pEvalZero := DensePolynomial.eval_eq_zero_of_isZero pZero (0 : Canonical)
        have qEvalZero := DensePolynomial.eval_eq_zero_of_isZero qZero (0 : Canonical)
        have impossible := coprime.identity (0 : Canonical)
        simp only [pEvalZero, qEvalZero, mul_zero, zero_add] at impossible
        exact (one_ne_zero impossible).elim
      · exact Or.inl (Decide.bool_eq_false_of_not_eq_true _ qZero)
    · exact Or.inr (Decide.bool_eq_false_of_not_eq_true _ pZero)
  apply Evaluation.coprimeCertificateOfIdentity q p someNonzero
    coprime.right coprime.left
  intro point
  have original := coprime.identity point
  calc
    1 = coprime.left.eval point * p.eval point +
        coprime.right.eval point * q.eval point := original
    _ = coprime.right.eval point * q.eval point +
        coprime.left.eval point * p.eval point :=
      Purelib.Data.Gaussian.Basic.add_comm _ _

/-- A nonzero polynomial and a nonzero displayed constant are coprime.

The zero left coefficient and the same inverse-scalar right coefficient
supply their unit identity through the original retained Euclidean constructor. -/
@[expose] public def constantRightOfNe
    {p : Basic.CanonicalCoefficients.CoefficientPolynomial} (pNonzero : p.isZero = false)
    (value : Canonical) (valueNonzero : value ≠ 0) :
    Basic.CoprimeCertificate p (DensePolynomial.constant value) := open Purelib.Algebra.Field in by
  apply Evaluation.coprimeCertificateOfIdentity p (DensePolynomial.constant value) (Or.inl pNonzero)
    0 (DensePolynomial.constant value⁻¹)
  intro point
  simp only [DensePolynomial.eval_zero, zero_mul, DensePolynomial.eval_constant, zero_add]
  rw [Purelib.Data.Gaussian.Basic.mul_comm]
  exact (ExplicitField.mul_inv_cancel value valueNonzero).symm

/-- Every displayed nonzero polynomial is coprime to the constant one. -/
@[expose] public def constantRight
    {p : Basic.CanonicalCoefficients.CoefficientPolynomial} (pNonzero : p.isZero = false) :
    Basic.CoprimeCertificate p (DensePolynomial.constant 1) :=
  constantRightOfNe pNonzero 1 one_ne_zero

/-- Multiply the right factors in two retained coprimality certificates.

The same three-term left coefficient and product right coefficient arise from
the two original scalar identities. Their retained Euclidean certificate
concerns the original left input and the ordered product of the right inputs. -/
@[expose] public def mulRight
    {p q r : Basic.CanonicalCoefficients.CoefficientPolynomial} (pNonzero : p.isZero = false)
    (leftCoprime : Basic.CoprimeCertificate p q)
    (rightCoprime : Basic.CoprimeCertificate p r) :
    Basic.CoprimeCertificate p (q * r) := by
  let leftCoefficient :=
    leftCoprime.left * rightCoprime.left * p +
      leftCoprime.left * rightCoprime.right * r +
      leftCoprime.right * rightCoprime.left * q
  let rightCoefficient := leftCoprime.right * rightCoprime.right
  apply Evaluation.coprimeCertificateOfIdentity p (q * r) (Or.inl pNonzero)
    leftCoefficient rightCoefficient
  intro point
  have leftIdentity := leftCoprime.identity point
  have rightIdentity := rightCoprime.identity point
  dsimp only [leftCoefficient, rightCoefficient]
  simp only [DensePolynomial.eval_add, DensePolynomial.eval_mul]
  calc
    1 = 1 * 1 := by ring1
    _ = (leftCoprime.left.eval point * p.eval point +
          leftCoprime.right.eval point * q.eval point) *
        (rightCoprime.left.eval point * p.eval point +
          rightCoprime.right.eval point * r.eval point) := by
      rw [← leftIdentity, ← rightIdentity]
    _ = ((leftCoprime.left.eval point * rightCoprime.left.eval point *
            p.eval point +
          leftCoprime.left.eval point * rightCoprime.right.eval point *
            r.eval point +
          leftCoprime.right.eval point * rightCoprime.left.eval point *
            q.eval point) * p.eval point) +
        (leftCoprime.right.eval point * rightCoprime.right.eval point) *
          (q.eval point * r.eval point) := by ring1
end Purelib.Polynomial.Dense.Gaussian.Coprime.Operations.CoprimeCertificate
