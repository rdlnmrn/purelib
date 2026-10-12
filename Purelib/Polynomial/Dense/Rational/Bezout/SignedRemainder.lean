module
import Purelib.Polynomial.Dense.Arithmetic
public import Purelib.Polynomial.Dense.Division.Basic
public import Purelib.Polynomial.Dense.Multiplication
import Purelib.Polynomial.Dense.Rational.Basic
public import Purelib.Polynomial.Dense.Rational.Bezout.Basic
import Purelib.Polynomial.Dense.Rational.SignedRemainder.Evaluation
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.Ring

open Purelib.Polynomial.Dense.Basic (DensePolynomial)

open Purelib.Polynomial

section
@[expose] public section

/-!
# Finite clearance certificates over constructive coordinates

Two displayed dense Bézout cofactors give a pointwise identity for a pair of
coordinate polynomials.  Finite Horner bounds then turn that identity into a
positive, uniform sum-of-squares bound on a closed constructive interval.
Four such bounds combine into a quantitative box-boundary certificate.

All bounds are rational finite data.  The proofs use neither a root set nor
an infinite-field extensionality argument.
-/

namespace Purelib.Polynomial.Dense.Rational.Bezout.Basic.CoprimeCertificate
section

/-- Bézout data transported through one signed Euclidean step. -/
def signedStep {p q :
  Dense.Rational.Basic.CoordinatePolynomial}
    (certificate : Dense.Rational.Bezout.Basic.CoprimeCertificate p q) :
    Dense.Rational.Bezout.Basic.CoprimeCertificate q (-((DensePolynomial.divMod p q).remainder)) where
  left := certificate.left * (DensePolynomial.divMod p q).quotient + certificate.right
  right := -certificate.left
  identity := by
    intro x
    have step := Purelib.Polynomial.Dense.Rational.SignedRemainder.Evaluation.signedStep_eval_identity p q x
    rw [certificate.identity, step]
    simp only [DensePolynomial.eval_add, DensePolynomial.eval_mul,
      DensePolynomial.eval_neg]
    ring1
end
end Purelib.Polynomial.Dense.Rational.Bezout.Basic.CoprimeCertificate

end
