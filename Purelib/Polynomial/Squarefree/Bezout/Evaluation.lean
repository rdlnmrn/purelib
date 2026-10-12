module

import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Factorization.Identity
import Purelib.Polynomial.Dense.Gaussian.GCD
public import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
public import Purelib.Polynomial.Dense.Gaussian.Squarefree.Decision
import Purelib.Polynomial.Dense.Multiplication
import Mathlib.Algebra.Ring.Defs
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.GCD
import Purelib.Polynomial.Dense.Gaussian.Coprime.Basic
import Purelib.Polynomial.Dense.Gaussian.Coprime.Decision
import Purelib.Tactic.Ring
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.Order.IsBotOne

/-!
# Squarefree certificates from finite Bézout evaluation

A displayed evaluation identity rules out the common-divisor result of the
same executable squarefreeness decision. The returned coprimality certificate
retains the supplied polynomial and its formal derivative as its owners.
-/

namespace Purelib.Polynomial.Squarefree.Bezout.Evaluation

open Purelib.Data
open Purelib.Polynomial
open Purelib.Data.Gaussian.Basic (Canonical)

/-- A finite Bézout evaluation identity certifies squarefreeness of a nonzero polynomial.

The executable decision supplies its coprimality certificate directly. Its
alternative nonconstant divisor contradicts the constant-one factorization
checked on the finite candidate list of the displayed difference polynomial. -/
@[expose] public def squarefreeOfEvalBezout
    (polynomial : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial)
    (nonzero : polynomial.isZero = false)
    (left right : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial)
    (identity : ∀ point : Canonical,
      left.eval point * polynomial.eval point +
        right.eval point *
          (Dense.Gaussian.GCD.derivative polynomial).eval point = 1) :
    Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate polynomial := by
  match outcome : Dense.Gaussian.Squarefree.Decision.squarefreeOutcome polynomial nonzero with
  | .coprime certificate => exact certificate
  | .commonDivisor common =>
      let cofactor :=
        left * common.leftFactor + right * common.rightFactor
      have factorization : Dense.Gaussian.Factorization.Identity.ProductIdentity
          (Dense.Basic.DensePolynomial.constant 1) common.divisor cofactor := by
        apply Dense.Gaussian.Factorization.Identity.factorizationOfCandidateEvals
        intro point _member
        dsimp only [cofactor]
        rw [Dense.Basic.DensePolynomial.eval_constant, Dense.Basic.DensePolynomial.eval_add,
          Dense.Basic.DensePolynomial.eval_mul, Dense.Basic.DensePolynomial.eval_mul]
        calc
          1 = left.eval point * polynomial.eval point +
                right.eval point *
                  (Dense.Gaussian.GCD.derivative polynomial).eval point :=
            (identity point).symm
          _ = common.divisor.eval point *
                (left.eval point * common.leftFactor.eval point +
                  right.eval point * common.rightFactor.eval point) := by
            rw [common.leftIdentity point, common.rightIdentity point]
            ring1
      have oneNormalized :
          (Dense.Basic.DensePolynomial.constant (1 : Canonical)).normalize = Dense.Basic.DensePolynomial.constant 1 :=
            by
        exact Dense.Basic.DensePolynomial.normalize_constant_of_ne (by decide)
      have oneNonzero : (Dense.Basic.DensePolynomial.constant (1 : Canonical)).isZero = false := by
        change (Dense.Basic.DensePolynomial.constant (1 : Canonical)).normalize.coeffs.isEmpty = false
        rw [oneNormalized]
        rfl
      have cofactorNonzero : cofactor.isZero = false :=
        Dense.Gaussian.Factorization.Identity.right_isZero_false oneNonzero oneNormalized
          factorization
      have degreeBalance := Dense.Gaussian.Factorization.Identity.factor_natDegree_add
        oneNonzero oneNormalized common.nonzero cofactorNonzero factorization
      have degreeZero : (Dense.Basic.DensePolynomial.constant (1 : Canonical)).natDegree = 0 := by
        change (Dense.Basic.DensePolynomial.constant (1 : Canonical)).normalize.coeffs.length - 1 = 0
        rw [oneNormalized]
        rfl
      rw [degreeZero] at degreeBalance
      have commonDegreeZero : common.divisor.natDegree = 0 :=
        (Nat.eq_zero_of_add_eq_zero degreeBalance).1
      exact (Nat.ne_of_gt common.positiveDegree commonDegreeZero).elim

end Purelib.Polynomial.Squarefree.Bezout.Evaluation
