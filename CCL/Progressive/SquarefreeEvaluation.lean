import RFAP.Polynomial.Factorization

/-!
# Finite squarefreeness from an evaluated Bezout identity

This narrow adapter converts an explicit pointwise Bezout identity into the
computed dense-polynomial squarefree certificate.  The negative branch is
eliminated by the finite candidate evaluations already exposed by RFAP.
-/

namespace CCL.ProgressiveSquarefree

abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianPolynomial :=
  RFAP.ConstructivePolynomial.GaussianPolynomial

open RFAP.ComputablePolynomial.DensePolynomial

def ofEvalBezoutUnit
    (polynomial : GaussianPolynomial)
    (nonzero : polynomial.isZero = false)
    (unit : Gaussian) (unitNonzero : unit ≠ 0)
    (left right : GaussianPolynomial)
    (identity : forall point : Gaussian,
      left.eval point * polynomial.eval point +
        right.eval point *
          (RFAP.ConstructiveGCD.derivative polynomial).eval point = unit) :
    RFAP.Squarefree.SquarefreeCertificate polynomial := by
  match outcome : RFAP.Squarefree.squarefreeOutcome polynomial nonzero with
  | .coprime certificate => exact certificate
  | .commonDivisor common =>
      let cofactor :=
        left * common.leftFactor + right * common.rightFactor
      have factorization : RFAP.Factorization.ProductIdentity
          (constant unit) common.divisor cofactor := by
        apply RFAP.Factorization.factorizationOfCandidateEvals
        intro point _member
        dsimp only [cofactor]
        rw [eval_constant, eval_add, eval_mul, eval_mul]
        calc
          unit = left.eval point * polynomial.eval point +
                right.eval point *
                  (RFAP.ConstructiveGCD.derivative polynomial).eval point :=
            (identity point).symm
          _ = common.divisor.eval point *
                (left.eval point * common.leftFactor.eval point +
                  right.eval point * common.rightFactor.eval point) := by
            rw [common.leftIdentity point, common.rightIdentity point]
            ring1
      have constantNonzero : (constant unit).isZero = false := by
        simp [isZero, normalize, unitNonzero]
      have constantNormalized :
          (constant unit).normalize = constant unit :=
        normalize_constant_of_ne unitNonzero
      have cofactorNonzero : cofactor.isZero = false :=
        RFAP.Factorization.right_isZero_false constantNonzero
          constantNormalized
          factorization
      have degreeBalance := RFAP.Factorization.factor_natDegree_add
        constantNonzero constantNormalized common.nonzero cofactorNonzero
          factorization
      have degreeZero : (constant unit).natDegree = 0 := by
        simp [natDegree, degreeCount, normalize, unitNonzero]
      rw [degreeZero] at degreeBalance
      have commonDegreeZero : common.divisor.natDegree = 0 :=
        (Nat.eq_zero_of_add_eq_zero degreeBalance).1
      exact (Nat.ne_of_gt common.positiveDegree commonDegreeZero).elim

/-- Unit-one specialization of the same finite conversion. -/
def ofEvalBezout
    (polynomial : GaussianPolynomial)
    (nonzero : polynomial.isZero = false)
    (left right : GaussianPolynomial)
    (identity : forall point : Gaussian,
      left.eval point * polynomial.eval point +
        right.eval point *
          (RFAP.ConstructiveGCD.derivative polynomial).eval point = 1) :
    RFAP.Squarefree.SquarefreeCertificate polynomial :=
  ofEvalBezoutUnit polynomial nonzero 1 (by decide) left right identity

end CCL.ProgressiveSquarefree
