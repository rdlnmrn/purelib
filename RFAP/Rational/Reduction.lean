import RFAP.Polynomial.SquarefreeFactors

/-!
# Finite cancellation for displayed rational functions

The executable extended Euclidean algorithm is run on normalized numerator
and denominator coefficient lists.  Its displayed common factor and two
cofactors are retained together with pointwise factorization identities,
finite degree balances, and a coprimality certificate for the reduced pair.
-/

namespace RFAP.RationalReduction

abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianPolynomial := RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev BezoutResult (p q : GaussianPolynomial) :=
  RFAP.ComputableGCD.BezoutResult p q
abbrev CoprimeCertificate :=
  RFAP.Squarefree.CoprimeCertificate

open RFAP.ComputablePolynomial.DensePolynomial

/-- The finite output of cancelling the computed common polynomial factor.
The original denominator is required to be a displayed nonzero polynomial. -/
structure ReducedPair
    (numerator denominator : GaussianPolynomial) where
  denominatorNonzero : denominator.isZero = false
  euclid : BezoutResult numerator.normalize denominator.normalize

namespace ReducedPair

def common
    {numerator denominator : GaussianPolynomial}
    (reduced : ReducedPair numerator denominator) : GaussianPolynomial :=
  reduced.euclid.gcd

def numeratorReduced
    {numerator denominator : GaussianPolynomial}
    (reduced : ReducedPair numerator denominator) : GaussianPolynomial :=
  reduced.euclid.pFactor

def denominatorReduced
    {numerator denominator : GaussianPolynomial}
    (reduced : ReducedPair numerator denominator) : GaussianPolynomial :=
  reduced.euclid.qFactor

def numeratorCoefficient
    {numerator denominator : GaussianPolynomial}
    (reduced : ReducedPair numerator denominator) : GaussianPolynomial :=
  reduced.euclid.factorLeft

def denominatorCoefficient
    {numerator denominator : GaussianPolynomial}
    (reduced : ReducedPair numerator denominator) : GaussianPolynomial :=
  reduced.euclid.factorRight

theorem common_normalized
    {numerator denominator : GaussianPolynomial}
    (reduced : ReducedPair numerator denominator) :
    reduced.common.normalize = reduced.common :=
  reduced.euclid.normalized

theorem numeratorReduced_normalized
    {numerator denominator : GaussianPolynomial}
    (reduced : ReducedPair numerator denominator) :
    reduced.numeratorReduced.normalize = reduced.numeratorReduced :=
  reduced.euclid.pFactorNormalized

theorem denominatorReduced_normalized
    {numerator denominator : GaussianPolynomial}
    (reduced : ReducedPair numerator denominator) :
    reduced.denominatorReduced.normalize = reduced.denominatorReduced :=
  reduced.euclid.qFactorNormalized

/-- Exact cancellation identity for the original numerator at every
displayed Gaussian-rational point. -/
theorem numerator_eval
    {numerator denominator : GaussianPolynomial}
    (reduced : ReducedPair numerator denominator) (point : Gaussian) :
    numerator.eval point =
      reduced.common.eval point * reduced.numeratorReduced.eval point := by
  rw [← eval_normalize numerator point]
  exact reduced.euclid.pIdentity point

/-- Exact cancellation identity for the original denominator. -/
theorem denominator_eval
    {numerator denominator : GaussianPolynomial}
    (reduced : ReducedPair numerator denominator) (point : Gaussian) :
    denominator.eval point =
      reduced.common.eval point * reduced.denominatorReduced.eval point := by
  rw [← eval_normalize denominator point]
  exact reduced.euclid.qIdentity point

/-- The two reduced cofactors carry a displayed Bézout identity equal to
one, before conversion to the standard coprimality certificate. -/
theorem reduced_identity
    {numerator denominator : GaussianPolynomial}
    (reduced : ReducedPair numerator denominator) (point : Gaussian) :
    1 = reduced.numeratorCoefficient.eval point *
          reduced.numeratorReduced.eval point +
        reduced.denominatorCoefficient.eval point *
          reduced.denominatorReduced.eval point :=
  reduced.euclid.factorIdentity point

theorem common_nonzero
    {numerator denominator : GaussianPolynomial}
    (reduced : ReducedPair numerator denominator) :
    reduced.common.isZero = false :=
  reduced.euclid.nonzero (Or.inr (by
    simpa only [isZero_normalize] using reduced.denominatorNonzero))

private theorem numerator_factorization
    {numerator denominator : GaussianPolynomial}
    (reduced : ReducedPair numerator denominator) :
    RFAP.Factorization.ProductIdentity numerator.normalize
      reduced.common reduced.numeratorReduced := by
  apply RFAP.Factorization.factorizationOfCandidateEvals
  intro point _
  exact reduced.euclid.pIdentity point

private theorem denominator_factorization
    {numerator denominator : GaussianPolynomial}
    (reduced : ReducedPair numerator denominator) :
    RFAP.Factorization.ProductIdentity denominator.normalize
      reduced.common reduced.denominatorReduced := by
  apply RFAP.Factorization.factorizationOfCandidateEvals
  intro point _
  exact reduced.euclid.qIdentity point

theorem denominatorReduced_nonzero
    {numerator denominator : GaussianPolynomial}
    (reduced : ReducedPair numerator denominator) :
    reduced.denominatorReduced.isZero = false := by
  apply RFAP.Factorization.right_isZero_false
    (p := denominator.normalize) (left := reduced.common)
  · simpa only [isZero_normalize] using reduced.denominatorNonzero
  · exact normalize_normalize denominator
  · exact reduced.denominator_factorization

theorem numeratorReduced_nonzero
    {numerator denominator : GaussianPolynomial}
    (reduced : ReducedPair numerator denominator)
    (numeratorNonzero : numerator.isZero = false) :
    reduced.numeratorReduced.isZero = false := by
  apply RFAP.Factorization.right_isZero_false
    (p := numerator.normalize) (left := reduced.common)
  · simpa only [isZero_normalize] using numeratorNonzero
  · exact normalize_normalize numerator
  · exact reduced.numerator_factorization

/-- Exact numerator degree removed by cancellation. -/
theorem numerator_degree_balance
    {numerator denominator : GaussianPolynomial}
    (reduced : ReducedPair numerator denominator)
    (numeratorNonzero : numerator.isZero = false) :
    reduced.common.natDegree + reduced.numeratorReduced.natDegree =
      numerator.natDegree := by
  have balance := RFAP.Factorization.factor_natDegree_add
    (p := numerator.normalize) (left := reduced.common)
    (right := reduced.numeratorReduced)
    (by simpa only [isZero_normalize] using numeratorNonzero)
    (normalize_normalize numerator) reduced.common_nonzero
    (reduced.numeratorReduced_nonzero numeratorNonzero)
    reduced.numerator_factorization
  simpa only [natDegree_normalize] using balance

/-- Exact denominator degree removed by cancellation. -/
theorem denominator_degree_balance
    {numerator denominator : GaussianPolynomial}
    (reduced : ReducedPair numerator denominator) :
    reduced.common.natDegree + reduced.denominatorReduced.natDegree =
      denominator.natDegree := by
  have balance := RFAP.Factorization.factor_natDegree_add
    (p := denominator.normalize) (left := reduced.common)
    (right := reduced.denominatorReduced)
    (by simpa only [isZero_normalize] using reduced.denominatorNonzero)
    (normalize_normalize denominator) reduced.common_nonzero
    reduced.denominatorReduced_nonzero reduced.denominator_factorization
  simpa only [natDegree_normalize] using balance

/-- The reduced numerator and denominator are constructively coprime. -/
def coprime
    {numerator denominator : GaussianPolynomial}
    (reduced : ReducedPair numerator denominator) :
    CoprimeCertificate reduced.numeratorReduced reduced.denominatorReduced :=
  RFAP.SquarefreeFactors.coprimeCertificateOfIdentity
    reduced.numeratorReduced reduced.denominatorReduced
    (Or.inr reduced.denominatorReduced_nonzero)
    reduced.numeratorCoefficient reduced.denominatorCoefficient
    reduced.reduced_identity

/-- At a displayed point where the original denominator is nonzero,
cancellation preserves the exact rational-function value. -/
theorem quotient_eval_eq_reduced
    {numerator denominator : GaussianPolynomial}
    (reduced : ReducedPair numerator denominator) (point : Gaussian)
    (denominatorAtPoint : denominator.eval point ≠ 0) :
    numerator.eval point * (denominator.eval point)⁻¹ =
      reduced.numeratorReduced.eval point *
        (reduced.denominatorReduced.eval point)⁻¹ := by
  have commonAtPoint : reduced.common.eval point ≠ 0 := by
    intro commonZero
    apply denominatorAtPoint
    rw [reduced.denominator_eval point, commonZero, zero_mul]
  have reducedDenominatorAtPoint :
      reduced.denominatorReduced.eval point ≠ 0 := by
    intro reducedZero
    apply denominatorAtPoint
    rw [reduced.denominator_eval point, reducedZero, mul_zero]
  rw [reduced.numerator_eval point, reduced.denominator_eval point]
  let commonValue := reduced.common.eval point
  let numeratorValue := reduced.numeratorReduced.eval point
  let denominatorValue := reduced.denominatorReduced.eval point
  have productNonzero : commonValue * denominatorValue ≠ 0 :=
    RFAP.ConstructiveGaussian.Gaussian.mul_ne_zero_direct
      commonAtPoint reducedDenominatorAtPoint
  apply RFAP.ConstructiveGaussian.Gaussian.mul_right_cancel_of_ne productNonzero
  have leftCancel :
      (commonValue * numeratorValue *
          (commonValue * denominatorValue)⁻¹) *
          (commonValue * denominatorValue) =
        commonValue * numeratorValue := by
    have inverseProduct :
        (commonValue * denominatorValue)⁻¹ *
            (commonValue * denominatorValue) = 1 := by
      simpa only [RFAP.ConstructiveGaussian.Gaussian.inv_eq] using
        RFAP.ConstructiveGaussian.Gaussian.inv_mul
          (commonValue * denominatorValue) productNonzero
    rw [RFAP.ConstructiveGaussian.Gaussian.mul_assoc, inverseProduct,
      RFAP.ConstructiveGaussian.Gaussian.mul_one]
  have rightCancel :
      (numeratorValue * denominatorValue⁻¹) *
          (commonValue * denominatorValue) =
        commonValue * numeratorValue := by
    calc
      (numeratorValue * denominatorValue⁻¹) *
          (commonValue * denominatorValue) =
          (numeratorValue * denominatorValue⁻¹ * commonValue) *
            denominatorValue :=
        (RFAP.ConstructiveGaussian.Gaussian.mul_assoc _ _ _).symm
      _ = (commonValue *
          (numeratorValue * denominatorValue⁻¹)) * denominatorValue := by
        rw [RFAP.ConstructiveGaussian.Gaussian.mul_comm
          (numeratorValue * denominatorValue⁻¹) commonValue]
      _ = (commonValue * numeratorValue * denominatorValue⁻¹) *
          denominatorValue := by
        rw [← RFAP.ConstructiveGaussian.Gaussian.mul_assoc]
      _ = commonValue * numeratorValue *
          (denominatorValue⁻¹ * denominatorValue) :=
        RFAP.ConstructiveGaussian.Gaussian.mul_assoc _ _ _
      _ = commonValue * numeratorValue := by
        have inverseDenominator :
            denominatorValue⁻¹ * denominatorValue = 1 := by
          simpa only [RFAP.ConstructiveGaussian.Gaussian.inv_eq] using
            RFAP.ConstructiveGaussian.Gaussian.inv_mul denominatorValue
              reducedDenominatorAtPoint
        rw [inverseDenominator,
          RFAP.ConstructiveGaussian.Gaussian.mul_one]
  exact leftCancel.trans rightCancel.symm

end ReducedPair

/-- Execute finite gcd cancellation on the normalized displayed inputs. -/
def reduce
    (numerator denominator : GaussianPolynomial)
    (denominatorNonzero : denominator.isZero = false) :
    ReducedPair numerator denominator where
  denominatorNonzero := denominatorNonzero
  euclid := RFAP.ComputableGCD.extendedGCD
    numerator.normalize denominator.normalize

/-- A rational-function value is exposed only with an exact proof that its
displayed denominator evaluation is nonzero. -/
structure ValueAt
    (numerator denominator : GaussianPolynomial) (point : Gaussian) where
  denominatorNonzero : denominator.eval point ≠ 0

def ValueAt.value
    {numerator denominator : GaussianPolynomial} {point : Gaussian}
    (_defined : ValueAt numerator denominator point) : Gaussian :=
  numerator.eval point * (denominator.eval point)⁻¹

end RFAP.RationalReduction
