module
import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Coprime.Basic
public import Purelib.Polynomial.Dense.Gaussian.Coprime.Decision
public import Purelib.Polynomial.Dense.Gaussian.Factorization.Identity
import Purelib.Polynomial.Dense.Gaussian.GCD
public import Purelib.Polynomial.Dense.Leading
import Purelib.Polynomial.Dense.Multiplication

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.GCD
import Purelib.Tactic.Ring
import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.GroupWithZero.NeZero

/-!
# Coprimality from a retained scalar Bezout identity

The completed Euclidean result supplies its original common factor and both
cofactors. The displayed Bezout coefficients form a retained auxiliary product;
finite coefficient and degree certificates identify the computed gcd as a unit.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Coprime.Evaluation

open Purelib.Polynomial.Dense.Basic
open _root_.Purelib.Polynomial.Dense.Basic renaming CoefficientPolynomial -> Dense
open Purelib.Polynomial.Dense.Gaussian
open Purelib.Polynomial.Dense.Leading
open _root_.Purelib.Polynomial.Dense.Leading renaming CoefficientPolynomial -> Dense
open Purelib.Polynomial.Dense.Gaussian.Basic
open Purelib.Data.Gaussian.Basic (Canonical)

/-- A displayed scalar Bezout identity certifies the original Euclidean gcd as a unit.

The original completed result and its same two cofactors determine the retained
auxiliary product. Candidate evaluations and exact degree balance force that gcd
to have degree zero, supplying the existing constant-gcd constructor. -/
@[expose] public def coprimeCertificateOfIdentity
    (p q : Basic.CanonicalCoefficients.CoefficientPolynomial)
    (someNonzero : p.isZero = false ∨ q.isZero = false)
    (left right : Basic.CanonicalCoefficients.CoefficientPolynomial)
    (identity : ∀ point : Canonical,
      1 = left.eval point * p.eval point +
        right.eval point * q.eval point) :
    Basic.CoprimeCertificate p q := by
  let result := GCD.extendedGCD p q
  let cofactor := left * result.pFactor + right * result.qFactor
  have oneLeading :
      LeadingTerm (DensePolynomial.constant (1 : Canonical)) 0 1 :=
    LeadingTerm.constant one_ne_zero
  have factorization :
      Factorization.Identity.ProductIdentity (DensePolynomial.constant 1) result.gcd cofactor := by
    apply Factorization.Identity.factorizationOfCandidateEvals
    intro point _
    simp only [DensePolynomial.eval_constant]
    have original := identity point
    rw [result.pIdentity point, result.qIdentity point] at original
    dsimp only [cofactor]
    simp only [DensePolynomial.eval_add, DensePolynomial.eval_mul]
    calc
      1 = left.eval point *
            (result.gcd.eval point * result.pFactor.eval point) +
          right.eval point *
            (result.gcd.eval point * result.qFactor.eval point) := original
      _ = result.gcd.eval point *
          (left.eval point * result.pFactor.eval point +
            right.eval point * result.qFactor.eval point) := by ring1
  have gcdNonzero : result.gcd.isZero = false :=
    result.nonzero someNonzero
  have cofactorNonzero : cofactor.isZero = false :=
    Factorization.Identity.right_isZero_false
      oneLeading.nonzero oneLeading.normalized factorization
  have degreeBalance :
      result.gcd.natDegree + cofactor.natDegree =
        (DensePolynomial.constant (1 : Canonical)).natDegree :=
    Factorization.Identity.factor_natDegree_add
      oneLeading.nonzero oneLeading.normalized gcdNonzero
        cofactorNonzero factorization
  have gcdDegreeZero : result.gcd.natDegree = 0 := by
    rw [oneLeading.degree_eq] at degreeBalance
    exact Nat.eq_zero_of_le_zero
      ((Nat.le_add_right result.gcd.natDegree cofactor.natDegree).trans_eq
        degreeBalance)
  exact Decision.certificateOfConstantGCD
    p q gcdNonzero gcdDegreeZero
end Purelib.Polynomial.Dense.Gaussian.Coprime.Evaluation
