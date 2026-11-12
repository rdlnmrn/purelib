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
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.GCD
import Purelib.Polynomial.Dense.Gaussian.Coprime.Basic
import Purelib.Polynomial.Dense.Gaussian.Coprime.Decision
import Purelib.Tactic.Ring

open Purelib.Data

open Purelib.Polynomial

public section

/-!
# Finite squarefreeness from an evaluated Bezout identity

This narrow adapter converts an explicit pointwise Bezout identity into the
computed dense-polynomial squarefree certificate.  The negative branch is
eliminated by the finite candidate evaluations already exposed by RFAP.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Squarefree.Evaluation

/-- Construct squarefreeness from an evaluated Bézout identity with nonzero constant value.

The supplied polynomial is nonzero. A computed common divisor is excluded using finite candidate evaluations and the
degree balance of the retained factorization. -/
@[expose] def ofEvalBezoutUnit
    (polynomial : Basic.CanonicalCoefficients.CoefficientPolynomial)
    (nonzero : polynomial.isZero = false)
    (unit : Gaussian.Basic.Canonical) (unitNonzero : unit ≠ 0)
    (left right : Basic.CanonicalCoefficients.CoefficientPolynomial)
    (identity : forall point : Gaussian.Basic.Canonical,
      left.eval point * polynomial.eval point +
        right.eval point *
          (GCD.derivative polynomial).eval point = unit) :
    Basic.SquarefreeCertificate polynomial := by
  match outcome : Decision.squarefreeOutcome polynomial nonzero with
  | .coprime certificate => exact certificate
  | .commonDivisor common =>
      let cofactor :=
        left * common.leftFactor + right * common.rightFactor
      have factorization : Factorization.Identity.ProductIdentity
          (Basic.DensePolynomial.constant unit) common.divisor cofactor := by
        apply Factorization.Identity.factorizationOfCandidateEvals
        intro point _member
        dsimp only [cofactor]
        rw [Basic.DensePolynomial.eval_constant, Basic.DensePolynomial.eval_add,
          Basic.DensePolynomial.eval_mul, Basic.DensePolynomial.eval_mul]
        calc
          unit = left.eval point * polynomial.eval point +
                right.eval point *
                  (GCD.derivative polynomial).eval point :=
            (identity point).symm
          _ = common.divisor.eval point *
                (left.eval point * common.leftFactor.eval point +
                  right.eval point * common.rightFactor.eval point) := by
            rw [common.leftIdentity point, common.rightIdentity point]
            ring1
      have constantNormalized :
          (Basic.DensePolynomial.constant unit).normalize = Basic.DensePolynomial.constant unit :=
        Basic.DensePolynomial.normalize_constant_of_ne unitNonzero
      have constantNonzero : (Basic.DensePolynomial.constant unit).isZero = false := by
        rw [Basic.DensePolynomial.isZero, constantNormalized]
        rfl
      have cofactorNonzero : cofactor.isZero = false :=
        Factorization.Identity.right_isZero_false constantNonzero
          constantNormalized
          factorization
      have degreeBalance := Factorization.Identity.factor_natDegree_add
        constantNonzero constantNormalized common.nonzero cofactorNonzero
          factorization
      have degreeZero : (Basic.DensePolynomial.constant unit).natDegree = 0 := by
        rw [Basic.DensePolynomial.natDegree, Basic.DensePolynomial.degreeCount,
          constantNormalized]
        rfl
      rw [degreeZero] at degreeBalance
      have commonDegreeZero : common.divisor.natDegree = 0 :=
        (Nat.eq_zero_of_add_eq_zero degreeBalance).1
      exact (Nat.ne_of_gt common.positiveDegree commonDegreeZero).elim

/-- Unit-one specialization of the same finite conversion.

The same computed squarefree outcome is retained, with the displayed Bézout constant specialized to the original
Gaussian unit. -/
@[expose] def ofEvalBezout
    (polynomial : Basic.CanonicalCoefficients.CoefficientPolynomial)
    (nonzero : polynomial.isZero = false)
    (left right : Basic.CanonicalCoefficients.CoefficientPolynomial)
    (identity : forall point : Gaussian.Basic.Canonical,
      left.eval point * polynomial.eval point +
        right.eval point *
          (GCD.derivative polynomial).eval point = 1) :
    Basic.SquarefreeCertificate polynomial :=
  ofEvalBezoutUnit polynomial nonzero 1 (by decide) left right identity

end Purelib.Polynomial.Dense.Gaussian.Squarefree.Evaluation

end
