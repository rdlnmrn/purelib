import mathlib.Tactic.QuotientFreeRing
import RFAP.Approximation.BestApproximation

/-!
# Universal finite Dirichlet-window bounds

This file strengthens the source-dependent consecutive-window certificate to
a universal rational constant.  The proof normalizes one consecutive pair,
rounds its displayed error ratio to the nearest Gaussian integer, and applies
the already proved empty-cylinder alternative to that one finite candidate.
No completed source, compactness argument, or infinite lattice is used.
-/

namespace RFAP.DirichletWindow

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianInt := RFAP.ConstructiveGaussianHeight.GaussianInt
abbrev Pair := RFAP.HurwitzRational.ConvergentPair

open RFAP.ConstructiveGaussian.Gaussian
open RFAP.ConstructiveGaussianHeight.GaussianInt
open RFAP.BestApproximation
open RFAP.HurwitzApproximation

/-- Integer-scaled weighted two-leg estimate.  Its slack is exactly the
quadrance of `leftWeight * left - rightWeight * right`, written
coordinatewise so no square root or completed norm is introduced. -/
theorem weighted_normSq_add_le (left right : Gaussian)
    (leftWeight rightWeight : Coordinate) :
    leftWeight * rightWeight * normSq (left + right) ≤
      leftWeight * (leftWeight + rightWeight) * normSq left +
        rightWeight * (leftWeight + rightWeight) * normSq right := by
  apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
  have squareSumNonnegative :
      0 ≤
        (leftWeight * left.re - rightWeight * right.re) ^ 2 +
          (leftWeight * left.im - rightWeight * right.im) ^ 2 :=
    add_nonneg
      (RFAP.ConstructiveFraction.sq_nonneg_direct _)
      (RFAP.ConstructiveFraction.sq_nonneg_direct _)
  calc
    0 ≤ (leftWeight * left.re - rightWeight * right.re) ^ 2 +
        (leftWeight * left.im - rightWeight * right.im) ^ 2 :=
      squareSumNonnegative
    _ =
        (leftWeight * (leftWeight + rightWeight) * normSq left +
            rightWeight * (leftWeight + rightWeight) * normSq right) -
          leftWeight * rightWeight * normSq (left + right) := by
      simp only [normSq, RFAP.ConstructiveGaussian.Gaussian.add_re,
        RFAP.ConstructiveGaussian.Gaussian.add_im]
      ring1

private theorem weighted_sum_lt_one
    {left right : Gaussian}
    (leftWeight rightWeight threshold : Coordinate)
    (leftWeightPositive : 0 < leftWeight)
    (rightWeightPositive : 0 < rightWeight)
    (budget :
      leftWeight * (leftWeight + rightWeight) * threshold +
          rightWeight * (leftWeight + rightWeight) * (1 / 2 : Coordinate) =
        leftWeight * rightWeight)
    (leftSmall : normSq left < threshold)
    (rightSmall : normSq right < (1 / 2 : Coordinate)) :
    normSq (left + right) < 1 := by
  have sumPositive : 0 < leftWeight + rightWeight := by
    have added := RFAP.ConstructiveFraction.add_lt_add_direct
      leftWeightPositive rightWeightPositive
    simpa only [RFAP.ConstructiveFraction.zero_add] using added
  have leftCoefficientPositive :
      0 < leftWeight * (leftWeight + rightWeight) :=
    RFAP.ConstructiveFraction.mul_pos_direct leftWeightPositive sumPositive
  have rightCoefficientPositive :
      0 < rightWeight * (leftWeight + rightWeight) :=
    RFAP.ConstructiveFraction.mul_pos_direct rightWeightPositive sumPositive
  have productPositive : 0 < leftWeight * rightWeight :=
    RFAP.ConstructiveFraction.mul_pos_direct leftWeightPositive
      rightWeightPositive
  have leftScaled :=
    RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
      leftCoefficientPositive leftSmall
  have rightScaled :=
    RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
      rightCoefficientPositive rightSmall
  have scaledBound :
      leftWeight * rightWeight * normSq (left + right) <
        leftWeight * rightWeight := by
    calc
      leftWeight * rightWeight * normSq (left + right) ≤
          leftWeight * (leftWeight + rightWeight) * normSq left +
            rightWeight * (leftWeight + rightWeight) * normSq right :=
        weighted_normSq_add_le left right leftWeight rightWeight
      _ < leftWeight * (leftWeight + rightWeight) * threshold +
          rightWeight * (leftWeight + rightWeight) * (1 / 2 : Coordinate) :=
        RFAP.ConstructiveFraction.add_lt_add_direct leftScaled rightScaled
      _ = leftWeight * rightWeight := budget
  apply RFAP.ConstructiveFraction.lt_of_mul_lt_mul_right_direct
    (c := leftWeight * rightWeight)
  · calc
      normSq (left + right) * (leftWeight * rightWeight) =
          leftWeight * rightWeight * normSq (left + right) := by ring1
      _ < leftWeight * rightWeight := scaledBound
      _ = (1 : Coordinate) * (leftWeight * rightWeight) := by ring1
  · exact productPositive

private theorem normSq_mul_lt_half_of_left_lt_one_of_right_le_half
    {left right : Gaussian}
    (leftInside : normSq left < 1)
    (rightBound : normSq right ≤ (1 / 2 : Coordinate)) :
    normSq (left * right) < 1 / 2 := by
  rw [normSq_mul]
  calc
    normSq left * normSq right ≤
        normSq left * (1 / 2 : Coordinate) :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct rightBound
        (normSq_nonneg left)
    _ < (1 : Coordinate) * (1 / 2 : Coordinate) :=
      RFAP.ConstructiveFraction.mul_lt_mul_of_pos_right_direct leftInside
        (by decide)
    _ = 1 / 2 := by ring1

/-- Square-root-free boundary behind the weighted estimates.  If two
displayed Gaussian legs both have quadrance below one half but their sum has
quadrance at least one, the first leg's quadrance lies inside the rational
quadratic band `g^2 - 3*g + 1/4 < 0`. -/
theorem quadraticGap_neg_of_sumExterior
    {left right : Gaussian}
    (leftSmall : normSq left < (1 / 2 : Coordinate))
    (rightSmall : normSq right < (1 / 2 : Coordinate))
    (sumExterior : (1 : Coordinate) ≤ normSq (left + right)) :
    normSq left ^ 2 - 3 * normSq left + 1 / 4 < 0 := by
  let leftNorm := normSq left
  let rightNorm := normSq right
  let dot := left.re * right.re + left.im * right.im
  let margin := 1 - leftNorm - rightNorm
  have leftNonnegative : 0 ≤ leftNorm := by
    dsimp only [leftNorm]
    exact normSq_nonneg left
  have rightNonnegative : 0 ≤ rightNorm := by
    dsimp only [rightNorm]
    exact normSq_nonneg right
  have normsBelowOne : leftNorm + rightNorm < 1 := by
    calc
      leftNorm + rightNorm <
          (1 / 2 : Coordinate) + (1 / 2 : Coordinate) :=
        RFAP.ConstructiveFraction.add_lt_add_direct leftSmall rightSmall
      _ = 1 := by decide
  have marginPositive : 0 < margin := by
    have differencePositive :=
      RFAP.ConstructiveFraction.sub_pos_direct normsBelowOne
    calc
      (0 : Coordinate) < 1 - (leftNorm + rightNorm) := differencePositive
      _ = margin := by dsimp only [margin]; ring1
  have sumExpansion :
      normSq (left + right) = leftNorm + rightNorm + 2 * dot := by
    dsimp only [leftNorm, rightNorm, dot]
    simp only [normSq, RFAP.ConstructiveGaussian.Gaussian.add_re,
      RFAP.ConstructiveGaussian.Gaussian.add_im]
    ring1
  have marginLeTwiceDot : margin ≤ 2 * dot := by
    have shifted := RFAP.ConstructiveFraction.sub_le_sub_right_direct
      sumExterior (leftNorm + rightNorm)
    calc
      margin = 1 - (leftNorm + rightNorm) := by
        dsimp only [margin]
        ring1
      _ ≤ normSq (left + right) - (leftNorm + rightNorm) := shifted
      _ = 2 * dot := by rw [sumExpansion]; ring1
  have marginSquareLe : margin ^ 2 ≤ (2 * dot) ^ 2 :=
    RFAP.ConstructiveFraction.pow_le_pow_direct marginPositive.le
      marginLeTwiceDot 2
  have dotCauchy : dot ^ 2 ≤ leftNorm * rightNorm := by
    apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
    calc
      0 ≤ (left.re * right.im - left.im * right.re) ^ 2 :=
        RFAP.ConstructiveFraction.sq_nonneg_direct _
      _ = leftNorm * rightNorm - dot ^ 2 := by
        dsimp only [leftNorm, rightNorm, dot, normSq]
        ring1
  have marginSquareLeFourProduct :
      margin ^ 2 ≤ 4 * (leftNorm * rightNorm) := by
    calc
      margin ^ 2 ≤ (2 * dot) ^ 2 := marginSquareLe
      _ = 4 * dot ^ 2 := by ring1
      _ ≤ 4 * (leftNorm * rightNorm) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct dotCauchy
          (by decide)
  have finiteValueNonpositive :
      margin ^ 2 - 4 * leftNorm * rightNorm ≤ 0 := by
    have shifted := RFAP.ConstructiveFraction.sub_le_sub_right_direct
      marginSquareLeFourProduct (4 * (leftNorm * rightNorm))
    calc
      margin ^ 2 - 4 * leftNorm * rightNorm =
          margin ^ 2 - 4 * (leftNorm * rightNorm) := by ring1
      _ ≤ 4 * (leftNorm * rightNorm) -
          4 * (leftNorm * rightNorm) := shifted
      _ = 0 := by ring1
  let delta := (1 / 2 : Coordinate) - rightNorm
  have halfPlusHalf :
      (1 / 2 : Coordinate) + (1 / 2 : Coordinate) = 1 := by decide
  have twiceHalf : (2 : Coordinate) * (1 / 2 : Coordinate) = 1 := by
    decide
  have fourHalf : (4 : Coordinate) * (1 / 2 : Coordinate) = 2 := by
    decide
  have halfSquare : ((1 / 2 : Coordinate) ^ 2) = 1 / 4 := by
    decide
  have deltaPositive : 0 < delta := by
    dsimp only [delta]
    exact RFAP.ConstructiveFraction.sub_pos_direct rightSmall
  have twiceLeftNonnegative : 0 ≤ 2 * leftNorm :=
    RFAP.ConstructiveFraction.mul_nonneg_direct (by decide) leftNonnegative
  have tailNonnegative : 0 ≤ 2 * leftNorm + delta :=
    add_nonneg twiceLeftNonnegative deltaPositive.le
  have factorPositive :
      0 < 2 * (1 / 2 : Coordinate) + 2 * leftNorm + delta := by
    calc
      (0 : Coordinate) < 2 * (1 / 2 : Coordinate) := by decide
      _ ≤ 2 * (1 / 2 : Coordinate) + (2 * leftNorm + delta) :=
        le_add_of_nonneg_right tailNonnegative
      _ = 2 * (1 / 2 : Coordinate) + 2 * leftNorm + delta := by ring1
  have correctionPositive :
      0 < delta *
        (2 * (1 / 2 : Coordinate) + 2 * leftNorm + delta) :=
    RFAP.ConstructiveFraction.mul_pos_direct deltaPositive factorPositive
  have marginIdentity :
      margin = ((1 / 2 : Coordinate) - leftNorm) + delta := by
    dsimp only [margin, delta]
    calc
      (1 : Coordinate) - leftNorm - rightNorm =
          ((1 / 2 : Coordinate) + (1 / 2 : Coordinate)) -
            leftNorm - rightNorm := by rw [halfPlusHalf]
      _ = ((1 / 2 : Coordinate) - leftNorm) +
          ((1 / 2 : Coordinate) - rightNorm) := by ring1
  have rightNormIdentity :
      rightNorm = (1 / 2 : Coordinate) - delta := by
    dsimp only [delta]
    ring1
  have finiteValueIdentity :
      margin ^ 2 - 4 * leftNorm * rightNorm =
        ((1 / 2 : Coordinate) - leftNorm) ^ 2 -
          4 * (1 / 2 : Coordinate) * leftNorm +
          delta *
            (2 * (1 / 2 : Coordinate) + 2 * leftNorm + delta) := by
    rw [marginIdentity, rightNormIdentity]
    ring1
  have halfValueLtFiniteValue :
      ((1 / 2 : Coordinate) - leftNorm) ^ 2 -
          4 * (1 / 2 : Coordinate) * leftNorm <
        margin ^ 2 - 4 * leftNorm * rightNorm := by
    calc
      ((1 / 2 : Coordinate) - leftNorm) ^ 2 -
            4 * (1 / 2 : Coordinate) * leftNorm =
          (((1 / 2 : Coordinate) - leftNorm) ^ 2 -
            4 * (1 / 2 : Coordinate) * leftNorm) + 0 := by
        ring1
      _ < (((1 / 2 : Coordinate) - leftNorm) ^ 2 -
            4 * (1 / 2 : Coordinate) * leftNorm) +
          delta *
            (2 * (1 / 2 : Coordinate) + 2 * leftNorm + delta) :=
        RFAP.ConstructiveFraction.add_lt_add_left_direct correctionPositive _
      _ = margin ^ 2 - 4 * leftNorm * rightNorm :=
        finiteValueIdentity.symm
  have simplifiedHalfValueLtFiniteValue :
      ((1 / 2 : Coordinate) - leftNorm) ^ 2 - 2 * leftNorm <
        margin ^ 2 - 4 * leftNorm * rightNorm := by
    calc
      ((1 / 2 : Coordinate) - leftNorm) ^ 2 - 2 * leftNorm =
          ((1 / 2 : Coordinate) - leftNorm) ^ 2 -
            4 * (1 / 2 : Coordinate) * leftNorm := by rw [fourHalf]
      _ < margin ^ 2 - 4 * leftNorm * rightNorm :=
        halfValueLtFiniteValue
  have quadraticIdentity :
      ((1 / 2 : Coordinate) - leftNorm) ^ 2 - 2 * leftNorm =
        leftNorm ^ 2 - 3 * leftNorm + 1 / 4 := by
    calc
      ((1 / 2 : Coordinate) - leftNorm) ^ 2 - 2 * leftNorm =
          (1 / 2 : Coordinate) ^ 2 -
            (2 * (1 / 2 : Coordinate)) * leftNorm +
              leftNorm ^ 2 - 2 * leftNorm := by ring1
      _ = (1 / 2 : Coordinate) ^ 2 - 1 * leftNorm +
          leftNorm ^ 2 - 2 * leftNorm := by rw [twiceHalf]
      _ = leftNorm ^ 2 - 3 * leftNorm +
          (1 / 2 : Coordinate) ^ 2 := by ring1
      _ = leftNorm ^ 2 - 3 * leftNorm + 1 / 4 := by rw [halfSquare]
  calc
    normSq left ^ 2 - 3 * normSq left + 1 / 4 =
        ((1 / 2 : Coordinate) - leftNorm) ^ 2 - 2 * leftNorm := by
      dsimp only [leftNorm]
      exact quadraticIdentity.symm
    _ < margin ^ 2 - 4 * leftNorm * rightNorm :=
      simplifiedHalfValueLtFiniteValue
    _ ≤ 0 := finiteValueNonpositive

/-- Turn the root-free quadratic alternative into a lower bound for any
displayed rational threshold on the nonnegative half interval. -/
theorem threshold_le_of_quadraticBoundary
    {gap threshold : Coordinate}
    (thresholdLtHalf : threshold < (1 / 2 : Coordinate))
    (thresholdPolynomialNonnegative :
      0 ≤ threshold ^ 2 - 3 * threshold + 1 / 4)
    (boundary :
      (1 / 2 : Coordinate) ≤ gap ∨
        gap ^ 2 - 3 * gap + 1 / 4 < 0) :
    threshold ≤ gap := by
  apply le_of_not_gt
  intro gapLtThreshold
  rcases boundary with halfLeGap | gapPolynomialNegative
  · have gapLtHalf := gapLtThreshold.trans thresholdLtHalf
    exact (not_lt_of_ge halfLeGap gapLtHalf).elim
  · have gapLtHalf := gapLtThreshold.trans thresholdLtHalf
    have sumLtOne : gap + threshold < 1 := by
      calc
        gap + threshold < threshold + threshold :=
          RFAP.ConstructiveFraction.add_lt_add_right_direct gapLtThreshold
            threshold
        _ < (1 / 2 : Coordinate) + (1 / 2 : Coordinate) :=
          RFAP.ConstructiveFraction.add_lt_add_direct thresholdLtHalf
            thresholdLtHalf
        _ = 1 := by decide
    have sumLtThree : gap + threshold < 3 :=
      sumLtOne.trans (show (1 : Coordinate) < 3 by decide)
    have differencePositive : 0 < threshold - gap :=
      RFAP.ConstructiveFraction.sub_pos_direct gapLtThreshold
    have factorPositive : 0 < 3 - gap - threshold := by
      have positive := RFAP.ConstructiveFraction.sub_pos_direct sumLtThree
      calc
        (0 : Coordinate) < 3 - (gap + threshold) := positive
        _ = 3 - gap - threshold := by ring1
    have correctionPositive :
        0 < (threshold - gap) * (3 - gap - threshold) :=
      RFAP.ConstructiveFraction.mul_pos_direct differencePositive
        factorPositive
    have thresholdPolynomialLtGapPolynomial :
        threshold ^ 2 - 3 * threshold + 1 / 4 <
          gap ^ 2 - 3 * gap + 1 / 4 := by
      calc
        threshold ^ 2 - 3 * threshold + 1 / 4 =
            (threshold ^ 2 - 3 * threshold + 1 / 4) + 0 := by ring1
        _ < (threshold ^ 2 - 3 * threshold + 1 / 4) +
            (threshold - gap) * (3 - gap - threshold) :=
          RFAP.ConstructiveFraction.add_lt_add_left_direct correctionPositive _
        _ = gap ^ 2 - 3 * gap + 1 / 4 := by ring1
    have gapPolynomialPositive :
        0 < gap ^ 2 - 3 * gap + 1 / 4 :=
      thresholdPolynomialNonnegative.trans_lt
        thresholdPolynomialLtGapPolynomial
    exact (not_lt_of_ge gapPolynomialPositive.le gapPolynomialNegative).elim

/-- A finite rational certificate for one weighted nearest-coefficient gap.
The budget equation is the exact arithmetic condition needed by the
two-leg estimate. -/
structure WeightCertificate where
  leftWeight : Coordinate
  rightWeight : Coordinate
  threshold : Coordinate
  leftWeightPositive : 0 < leftWeight
  rightWeightPositive : 0 < rightWeight
  budget :
    leftWeight * (leftWeight + rightWeight) * threshold +
        rightWeight * (leftWeight + rightWeight) * (1 / 2 : Coordinate) =
      leftWeight * rightWeight

/-- Nearest-Gaussian-integer reduction turns a normalized exterior
alternative into any rational gap certified by two positive displayed
weights and the exact half-square budget equation. -/
theorem weightedThreshold_le_determinantGap
    (errorRatio denominatorRatio : Gaussian)
    (leftWeight rightWeight threshold : Coordinate)
    (leftWeightPositive : 0 < leftWeight)
    (rightWeightPositive : 0 < rightWeight)
    (budget :
      leftWeight * (leftWeight + rightWeight) * threshold +
          rightWeight * (leftWeight + rightWeight) * (1 / 2 : Coordinate) =
        leftWeight * rightWeight)
    (denominatorInside : normSq denominatorRatio < 1)
    (coefficientExterior : ∀ coefficient : GaussianInt,
      (1 : Coordinate) ≤
          normSq (errorRatio - toGaussian coefficient) ∨
        1 ≤ normSq
          (1 - toGaussian coefficient * denominatorRatio)) :
    threshold ≤
      normSq (1 - denominatorRatio * errorRatio) := by
  apply le_of_not_gt
  intro gapSmall
  let coefficient := RFAP.HurwitzNearest.nearest errorRatio
  let remainder := RFAP.HurwitzNearest.remainder errorRatio
  have remainderBound : normSq remainder ≤ (1 / 2 : Coordinate) := by
    dsimp only [remainder]
    exact RFAP.HurwitzNearest.remainder_normSq_le_half errorRatio
  by_cases coefficientZero : coefficient = 0
  · have remainderIdentity : remainder = errorRatio := by
      change errorRatio -
          toGaussian (RFAP.HurwitzNearest.nearest errorRatio) = errorRatio
      change RFAP.HurwitzNearest.nearest errorRatio = 0 at coefficientZero
      rw [coefficientZero, toGaussian_zero]
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
          RFAP.ConstructiveGaussian.Gaussian.sub_im,
          RFAP.ConstructiveGaussian.Gaussian.zero_re,
          RFAP.ConstructiveGaussian.Gaussian.zero_im] <;>
        ring1
    have productSmall :
        normSq (denominatorRatio * errorRatio) < 1 / 2 := by
      apply normSq_mul_lt_half_of_left_lt_one_of_right_le_half
        denominatorInside
      rw [← remainderIdentity]
      exact remainderBound
    have sumIdentity :
        (1 - denominatorRatio * errorRatio) +
            denominatorRatio * errorRatio = 1 := by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
          RFAP.ConstructiveGaussian.Gaussian.sub_im,
          RFAP.ConstructiveGaussian.Gaussian.add_re,
          RFAP.ConstructiveGaussian.Gaussian.add_im,
          RFAP.ConstructiveGaussian.Gaussian.mul_re,
          RFAP.ConstructiveGaussian.Gaussian.mul_im,
          RFAP.ConstructiveGaussian.Gaussian.one_re,
          RFAP.ConstructiveGaussian.Gaussian.one_im] <;>
        ring1
    have impossible := weighted_sum_lt_one leftWeight rightWeight threshold
      leftWeightPositive rightWeightPositive budget gapSmall productSmall
    rw [sumIdentity, normSq_one] at impossible
    exact (lt_irrefl 1 impossible).elim
  · have exterior := coefficientExterior coefficient
    have remainderIdentity :
        remainder = errorRatio - toGaussian coefficient := rfl
    rcases exterior with errorExterior | denominatorExterior
    · have oneLeHalf : (1 : Coordinate) ≤ 1 / 2 :=
        errorExterior.trans (by
          rw [← remainderIdentity]
          exact remainderBound)
      exact (not_le_of_gt (show (1 / 2 : Coordinate) < 1 by decide)
        oneLeHalf).elim
    · have remainderProductSmall :
          normSq (denominatorRatio * remainder) < 1 / 2 :=
        normSq_mul_lt_half_of_left_lt_one_of_right_le_half
          denominatorInside remainderBound
      have denominatorIdentity :
          1 - toGaussian coefficient * denominatorRatio =
            (1 - denominatorRatio * errorRatio) +
              denominatorRatio * remainder := by
        dsimp only [remainder, coefficient, RFAP.HurwitzNearest.remainder]
        apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
          simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
            RFAP.ConstructiveGaussian.Gaussian.sub_im,
            RFAP.ConstructiveGaussian.Gaussian.add_re,
            RFAP.ConstructiveGaussian.Gaussian.add_im,
            RFAP.ConstructiveGaussian.Gaussian.mul_re,
            RFAP.ConstructiveGaussian.Gaussian.mul_im,
            RFAP.ConstructiveGaussian.Gaussian.one_re,
            RFAP.ConstructiveGaussian.Gaussian.one_im] <;>
          ring1
      have denominatorSmall := weighted_sum_lt_one leftWeight rightWeight
        threshold leftWeightPositive rightWeightPositive budget gapSmall
        remainderProductSmall
      rw [← denominatorIdentity] at denominatorSmall
      exact (not_lt_of_ge denominatorExterior denominatorSmall).elim

/-- Apply a displayed weight certificate to a normalized exterior
alternative. -/
theorem WeightCertificate.threshold_le_determinantGap
    (certificate : WeightCertificate)
    (errorRatio denominatorRatio : Gaussian)
    (denominatorInside : normSq denominatorRatio < 1)
    (coefficientExterior : ∀ coefficient : GaussianInt,
      (1 : Coordinate) ≤
          normSq (errorRatio - toGaussian coefficient) ∨
        1 ≤ normSq
          (1 - toGaussian coefficient * denominatorRatio)) :
    certificate.threshold ≤
      normSq (1 - denominatorRatio * errorRatio) := by
  exact weightedThreshold_le_determinantGap errorRatio denominatorRatio
    certificate.leftWeight certificate.rightWeight certificate.threshold
    certificate.leftWeightPositive certificate.rightWeightPositive
    certificate.budget denominatorInside coefficientExterior

/-- The small weights `2,1` give the simple gap `1/12`. -/
theorem one_twelfth_le_determinantGap
    (errorRatio denominatorRatio : Gaussian)
    (denominatorInside : normSq denominatorRatio < 1)
    (coefficientExterior : ∀ coefficient : GaussianInt,
      (1 : Coordinate) ≤
          normSq (errorRatio - toGaussian coefficient) ∨
        1 ≤ normSq
          (1 - toGaussian coefficient * denominatorRatio)) :
    (1 / 12 : Coordinate) ≤
      normSq (1 - denominatorRatio * errorRatio) := by
  exact weightedThreshold_le_determinantGap errorRatio denominatorRatio
    2 1 (1 / 12) (by decide) (by decide) (by decide) denominatorInside
    coefficientExterior

/-! ## Normalizing one consecutive pair -/

/-- Upper error divided by lower error for a consecutive best pair. -/
def errorRatio (source : Gaussian) (lower upper : Pair) : Gaussian :=
  error source upper *
    RFAP.ConstructiveGaussian.Gaussian.inv (error source lower)

/-- Lower denominator divided by upper denominator for a consecutive best
pair. -/
def denominatorRatio (lower upper : Pair) : Gaussian :=
  toGaussian lower.denominator *
    RFAP.ConstructiveGaussian.Gaussian.inv (toGaussian upper.denominator)

private theorem mul_inv_mul_cancel (left right : Gaussian)
    (rightNonzero : right ≠ 0) :
    (left * RFAP.ConstructiveGaussian.Gaussian.inv right) * right = left := by
  calc
    (left * RFAP.ConstructiveGaussian.Gaussian.inv right) * right =
        left * (RFAP.ConstructiveGaussian.Gaussian.inv right * right) :=
      RFAP.ConstructiveGaussian.Gaussian.mul_assoc _ _ _
    _ = left * 1 := by
      rw [RFAP.ConstructiveGaussian.Gaussian.inv_mul right rightNonzero]
    _ = left := RFAP.ConstructiveGaussian.Gaussian.mul_one _

theorem AreConsecutiveBest.lowerError_nonzero
    {source : RFAP.HurwitzRational.Fraction} {lower upper : Pair}
    (consecutive : AreConsecutiveBest source.value lower upper) :
    error source.value lower ≠ 0 := by
  intro lowerErrorZero
  have lowerQuadranceZero := congrArg normSq lowerErrorZero
  rw [normSq_zero] at lowerQuadranceZero
  have errorOrdered :
      errorQuadrance source.value upper <
        errorQuadrance source.value lower :=
    consecutive.2.1.2.1 lower consecutive.1.1 consecutive.2.2.1
  change normSq (error source.value upper) <
    normSq (error source.value lower) at errorOrdered
  rw [lowerQuadranceZero] at errorOrdered
  exact (not_lt_of_ge (normSq_nonneg (error source.value upper))
    errorOrdered).elim

theorem AreConsecutiveBest.upperDenominatorGaussianNonzero
    {source : RFAP.HurwitzRational.Fraction} {lower upper : Pair}
    (consecutive : AreConsecutiveBest source.value lower upper) :
    toGaussian upper.denominator ≠ 0 := by
  intro embeddedZero
  exact consecutive.2.1.1 (toGaussian_eq_zero.mp embeddedZero)

theorem AreConsecutiveBest.errorRatio_mul_lowerError
    {source : RFAP.HurwitzRational.Fraction} {lower upper : Pair}
    (consecutive : AreConsecutiveBest source.value lower upper) :
    errorRatio source.value lower upper * error source.value lower =
      error source.value upper := by
  exact mul_inv_mul_cancel _ _
    (lowerError_nonzero consecutive)

theorem AreConsecutiveBest.denominatorRatio_mul_upperDenominator
    {source : RFAP.HurwitzRational.Fraction} {lower upper : Pair}
    (consecutive : AreConsecutiveBest source.value lower upper) :
    denominatorRatio lower upper * toGaussian upper.denominator =
      toGaussian lower.denominator := by
  exact mul_inv_mul_cancel _ _
    (upperDenominatorGaussianNonzero consecutive)

theorem AreConsecutiveBest.denominatorRatio_normSq_lt_one
    {source : RFAP.HurwitzRational.Fraction} {lower upper : Pair}
    (consecutive : AreConsecutiveBest source.value lower upper) :
    normSq (denominatorRatio lower upper) < 1 := by
  have upperPositive :
    0 < normSq (toGaussian upper.denominator) :=
    normSq_pos (upperDenominatorGaussianNonzero consecutive)
  unfold denominatorRatio
  rw [normSq_mul,
    RFAP.ConstructiveGaussian.Gaussian.normSq_inv _
      (upperDenominatorGaussianNonzero consecutive)]
  change normSq (toGaussian lower.denominator) /
      normSq (toGaussian upper.denominator) < 1
  apply (RFAP.ConstructiveFraction.div_lt_iff_pos upperPositive).mpr
  rw [RFAP.ConstructiveFraction.one_mul, normSq_toGaussian,
    normSq_toGaussian]
  exact RFAP.ConstructiveFraction.natCast_lt_direct consecutive.2.2.1

/-- Every integral coefficient gives a normalized exterior alternative. -/
theorem AreConsecutiveBest.normalizedCoefficientExterior
    {source : RFAP.HurwitzRational.Fraction} {lower upper : Pair}
    (consecutive : AreConsecutiveBest source.value lower upper)
    (coefficient : GaussianInt) :
    (1 : Coordinate) ≤
        normSq (errorRatio source.value lower upper -
          toGaussian coefficient) ∨
      1 ≤ normSq
        (1 - toGaussian coefficient * denominatorRatio lower upper) := by
  let candidate := linearCombination lower upper (-coefficient) 1
  have outside := consecutive.linearCombination_outside_mixedCylinder
    (-coefficient) 1 (Or.inr (by decide))
  have lowerErrorPositive :
      0 < errorQuadrance source.value lower :=
    normSq_pos (lowerError_nonzero consecutive)
  have upperDenominatorPositive :
      (0 : Coordinate) < denominatorQuadrance upper :=
    RFAP.ConstructiveFraction.natCast_pos_direct
      (normNat_pos consecutive.2.1.1)
  have errorIdentity :
      error source.value candidate =
        (errorRatio source.value lower upper - toGaussian coefficient) *
          error source.value lower := by
    dsimp only [candidate]
    rw [error_linearCombination_negUnit_one]
    have ratioCancel :=
      errorRatio_mul_lowerError consecutive
    calc
      error source.value upper -
            toGaussian coefficient * error source.value lower =
          errorRatio source.value lower upper * error source.value lower -
            toGaussian coefficient * error source.value lower := by
        rw [ratioCancel]
      _ =
          (errorRatio source.value lower upper - toGaussian coefficient) *
            error source.value lower := by
        apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
          simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
            RFAP.ConstructiveGaussian.Gaussian.sub_im,
            RFAP.ConstructiveGaussian.Gaussian.mul_re,
            RFAP.ConstructiveGaussian.Gaussian.mul_im] <;>
          ring1
  have denominatorIdentity :
      toGaussian candidate.denominator =
        (1 - toGaussian coefficient * denominatorRatio lower upper) *
          toGaussian upper.denominator := by
    dsimp only [candidate]
    rw [toGaussian_denominator_linearCombination_negUnit_one]
    have ratioCancel :=
      denominatorRatio_mul_upperDenominator consecutive
    calc
      toGaussian upper.denominator -
            toGaussian coefficient * toGaussian lower.denominator =
          toGaussian upper.denominator -
            toGaussian coefficient *
              (denominatorRatio lower upper *
                toGaussian upper.denominator) := by
        rw [ratioCancel]
      _ =
          (1 - toGaussian coefficient * denominatorRatio lower upper) *
            toGaussian upper.denominator := by
        apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
          simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
            RFAP.ConstructiveGaussian.Gaussian.sub_im,
            RFAP.ConstructiveGaussian.Gaussian.mul_re,
            RFAP.ConstructiveGaussian.Gaussian.mul_im,
            RFAP.ConstructiveGaussian.Gaussian.one_re,
            RFAP.ConstructiveGaussian.Gaussian.one_im] <;>
          ring1
  rcases outside with errorOutside | denominatorOutside
  · left
    apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct
      (c := errorQuadrance source.value lower)
    · calc
        (1 : Coordinate) * errorQuadrance source.value lower =
            errorQuadrance source.value lower := by ring1
        _ ≤ errorQuadrance source.value candidate := errorOutside
        _ =
            normSq (errorRatio source.value lower upper -
                toGaussian coefficient) *
              errorQuadrance source.value lower := by
          unfold errorQuadrance
          rw [errorIdentity, normSq_mul]
    · exact lowerErrorPositive
  · right
    have castOutside :=
      RFAP.ConstructiveFraction.natCast_le_direct denominatorOutside
    apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct
      (c := (denominatorQuadrance upper : Coordinate))
    · calc
        (1 : Coordinate) * (denominatorQuadrance upper : Coordinate) =
            (denominatorQuadrance upper : Coordinate) := by ring1
        _ ≤ (denominatorQuadrance candidate : Coordinate) := castOutside
        _ = normSq (toGaussian candidate.denominator) :=
          (normSq_toGaussian _).symm
        _ =
            normSq
                (1 - toGaussian coefficient *
                  denominatorRatio lower upper) *
              (denominatorQuadrance upper : Coordinate) := by
          rw [denominatorIdentity, normSq_mul, normSq_toGaussian]
          rfl
    · exact upperDenominatorPositive

/-- Every nontrivial integral linear combination gives a normalized exterior
alternative.  Unlike `normalizedCoefficientExterior`, which fixes the upper
coefficient to one, this form retains both coefficients.  The norm-two
leading combinations needed by the sharp index-one chamber cannot in general
be divided to the one-coefficient form inside `ℤ[i]`. -/
theorem AreConsecutiveBest.normalizedLinearCombinationExterior
    {source : RFAP.HurwitzRational.Fraction} {lower upper : Pair}
    (consecutive : AreConsecutiveBest source.value lower upper)
    (leftCoefficient rightCoefficient : GaussianInt)
    (coefficientNonzero :
      leftCoefficient ≠ 0 ∨ rightCoefficient ≠ 0) :
    (1 : Coordinate) ≤
        normSq
          (toGaussian leftCoefficient +
            toGaussian rightCoefficient *
              errorRatio source.value lower upper) ∨
      1 ≤
        normSq
          (toGaussian leftCoefficient * denominatorRatio lower upper +
            toGaussian rightCoefficient) := by
  let candidate := linearCombination lower upper
    leftCoefficient rightCoefficient
  have outside := consecutive.linearCombination_outside_mixedCylinder
    leftCoefficient rightCoefficient coefficientNonzero
  have lowerErrorPositive :
      0 < errorQuadrance source.value lower :=
    normSq_pos (lowerError_nonzero consecutive)
  have upperDenominatorPositive :
      (0 : Coordinate) < denominatorQuadrance upper :=
    RFAP.ConstructiveFraction.natCast_pos_direct
      (normNat_pos consecutive.2.1.1)
  have errorIdentity :
      error source.value candidate =
        (toGaussian leftCoefficient +
            toGaussian rightCoefficient *
              errorRatio source.value lower upper) *
          error source.value lower := by
    dsimp only [candidate]
    rw [RFAP.BestApproximation.error_linearCombination]
    have ratioCancel := errorRatio_mul_lowerError consecutive
    calc
      toGaussian leftCoefficient * error source.value lower +
            toGaussian rightCoefficient * error source.value upper =
          toGaussian leftCoefficient * error source.value lower +
            toGaussian rightCoefficient *
              (errorRatio source.value lower upper *
                error source.value lower) := by
        rw [ratioCancel]
      _ =
          (toGaussian leftCoefficient +
              toGaussian rightCoefficient *
                errorRatio source.value lower upper) *
            error source.value lower := by
        apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
          simp only [RFAP.ConstructiveGaussian.Gaussian.add_re,
            RFAP.ConstructiveGaussian.Gaussian.add_im,
            RFAP.ConstructiveGaussian.Gaussian.mul_re,
            RFAP.ConstructiveGaussian.Gaussian.mul_im] <;>
          ring1
  have denominatorIdentity :
      toGaussian candidate.denominator =
        (toGaussian leftCoefficient * denominatorRatio lower upper +
            toGaussian rightCoefficient) *
          toGaussian upper.denominator := by
    dsimp only [candidate, linearCombination]
    rw [toGaussian_add, toGaussian_mul, toGaussian_mul]
    have ratioCancel := denominatorRatio_mul_upperDenominator consecutive
    calc
      toGaussian leftCoefficient * toGaussian lower.denominator +
            toGaussian rightCoefficient * toGaussian upper.denominator =
          toGaussian leftCoefficient *
              (denominatorRatio lower upper *
                toGaussian upper.denominator) +
            toGaussian rightCoefficient * toGaussian upper.denominator := by
        rw [ratioCancel]
      _ =
          (toGaussian leftCoefficient * denominatorRatio lower upper +
              toGaussian rightCoefficient) *
            toGaussian upper.denominator := by
        apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
          simp only [RFAP.ConstructiveGaussian.Gaussian.add_re,
            RFAP.ConstructiveGaussian.Gaussian.add_im,
            RFAP.ConstructiveGaussian.Gaussian.mul_re,
            RFAP.ConstructiveGaussian.Gaussian.mul_im] <;>
          ring1
  rcases outside with errorOutside | denominatorOutside
  · left
    apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct
      (c := errorQuadrance source.value lower)
    · calc
        (1 : Coordinate) * errorQuadrance source.value lower =
            errorQuadrance source.value lower := by ring1
        _ ≤ errorQuadrance source.value candidate := errorOutside
        _ =
            normSq
                (toGaussian leftCoefficient +
                  toGaussian rightCoefficient *
                    errorRatio source.value lower upper) *
              errorQuadrance source.value lower := by
          unfold errorQuadrance
          rw [errorIdentity, normSq_mul]
    · exact lowerErrorPositive
  · right
    have castOutside :=
      RFAP.ConstructiveFraction.natCast_le_direct denominatorOutside
    apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct
      (c := (denominatorQuadrance upper : Coordinate))
    · calc
        (1 : Coordinate) * (denominatorQuadrance upper : Coordinate) =
            (denominatorQuadrance upper : Coordinate) := by ring1
        _ ≤ (denominatorQuadrance candidate : Coordinate) := castOutside
        _ = normSq (toGaussian candidate.denominator) :=
          (normSq_toGaussian _).symm
        _ =
            normSq
                (toGaussian leftCoefficient *
                    denominatorRatio lower upper +
                  toGaussian rightCoefficient) *
              (denominatorQuadrance upper : Coordinate) := by
          rw [denominatorIdentity, normSq_mul, normSq_toGaussian]
          rfl
    · exact upperDenominatorPositive

/-- Below the trivial half-gap branch, a consecutive normalized determinant
gap satisfies the exact square-root-free quadratic constraint. -/
theorem AreConsecutiveBest.normalizedDeterminantGap_quadratic_neg_of_lt_half
    {source : RFAP.HurwitzRational.Fraction} {lower upper : Pair}
    (consecutive : AreConsecutiveBest source.value lower upper)
    (gapSmall :
      normSq
        (1 - denominatorRatio lower upper *
          errorRatio source.value lower upper) < (1 / 2 : Coordinate)) :
    normSq
          (1 - denominatorRatio lower upper *
            errorRatio source.value lower upper) ^ 2 -
        3 * normSq
          (1 - denominatorRatio lower upper *
            errorRatio source.value lower upper) +
      1 / 4 < 0 := by
  let coefficient := RFAP.HurwitzNearest.nearest
    (errorRatio source.value lower upper)
  let remainder := RFAP.HurwitzNearest.remainder
    (errorRatio source.value lower upper)
  let gap := 1 - denominatorRatio lower upper *
    errorRatio source.value lower upper
  let remainderProduct := denominatorRatio lower upper * remainder
  have remainderBound : normSq remainder ≤ (1 / 2 : Coordinate) := by
    dsimp only [remainder]
    exact RFAP.HurwitzNearest.remainder_normSq_le_half
      (errorRatio source.value lower upper)
  have remainderProductSmall :
      normSq remainderProduct < (1 / 2 : Coordinate) := by
    dsimp only [remainderProduct]
    exact normSq_mul_lt_half_of_left_lt_one_of_right_le_half
      (denominatorRatio_normSq_lt_one consecutive) remainderBound
  have sumExterior : (1 : Coordinate) ≤ normSq (gap + remainderProduct) := by
    by_cases coefficientZero : coefficient = 0
    · have remainderIdentity :
          remainder = errorRatio source.value lower upper := by
        change errorRatio source.value lower upper -
            toGaussian
              (RFAP.HurwitzNearest.nearest
                (errorRatio source.value lower upper)) =
          errorRatio source.value lower upper
        change RFAP.HurwitzNearest.nearest
          (errorRatio source.value lower upper) = 0 at coefficientZero
        rw [coefficientZero, toGaussian_zero]
        apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
          simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
            RFAP.ConstructiveGaussian.Gaussian.sub_im,
            RFAP.ConstructiveGaussian.Gaussian.zero_re,
            RFAP.ConstructiveGaussian.Gaussian.zero_im] <;>
          ring1
      have sumIdentity : gap + remainderProduct = 1 := by
        dsimp only [gap, remainderProduct]
        rw [remainderIdentity]
        apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
          simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
            RFAP.ConstructiveGaussian.Gaussian.sub_im,
            RFAP.ConstructiveGaussian.Gaussian.add_re,
            RFAP.ConstructiveGaussian.Gaussian.add_im,
            RFAP.ConstructiveGaussian.Gaussian.mul_re,
            RFAP.ConstructiveGaussian.Gaussian.mul_im,
            RFAP.ConstructiveGaussian.Gaussian.one_re,
            RFAP.ConstructiveGaussian.Gaussian.one_im] <;>
          ring1
      rw [sumIdentity, normSq_one]
    · have exterior := normalizedCoefficientExterior consecutive coefficient
      have remainderIdentity :
          remainder = errorRatio source.value lower upper -
            toGaussian coefficient := rfl
      rcases exterior with errorExterior | denominatorExterior
      · have oneLeHalf : (1 : Coordinate) ≤ 1 / 2 :=
          errorExterior.trans (by
            rw [← remainderIdentity]
            exact remainderBound)
        exact ((not_le_of_gt (show (1 / 2 : Coordinate) < 1 by decide))
          oneLeHalf).elim
      · have denominatorIdentity :
            1 - toGaussian coefficient * denominatorRatio lower upper =
              gap + remainderProduct := by
          dsimp only [gap, remainderProduct, remainder, coefficient,
            RFAP.HurwitzNearest.remainder]
          apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
            simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
              RFAP.ConstructiveGaussian.Gaussian.sub_im,
              RFAP.ConstructiveGaussian.Gaussian.add_re,
              RFAP.ConstructiveGaussian.Gaussian.add_im,
              RFAP.ConstructiveGaussian.Gaussian.mul_re,
              RFAP.ConstructiveGaussian.Gaussian.mul_im,
              RFAP.ConstructiveGaussian.Gaussian.one_re,
              RFAP.ConstructiveGaussian.Gaussian.one_im] <;>
            ring1
        rw [← denominatorIdentity]
        exact denominatorExterior
  apply quadraticGap_neg_of_sumExterior
  · exact gapSmall
  · exact remainderProductSmall
  · exact sumExterior

/-- Root-free algebraic boundary supplied by the nearest-coefficient argument:
the normalized gap is at least one half, or it lies in the displayed rational
quadratic band. -/
theorem AreConsecutiveBest.normalizedDeterminantGap_boundary
    {source : RFAP.HurwitzRational.Fraction} {lower upper : Pair}
    (consecutive : AreConsecutiveBest source.value lower upper) :
    (1 / 2 : Coordinate) ≤
        normSq
          (1 - denominatorRatio lower upper *
            errorRatio source.value lower upper) ∨
      normSq
            (1 - denominatorRatio lower upper *
              errorRatio source.value lower upper) ^ 2 -
          3 * normSq
            (1 - denominatorRatio lower upper *
              errorRatio source.value lower upper) +
        1 / 4 < 0 := by
  by_cases gapSmall :
      normSq
        (1 - denominatorRatio lower upper *
          errorRatio source.value lower upper) < (1 / 2 : Coordinate)
  · exact Or.inr
      (normalizedDeterminantGap_quadratic_neg_of_lt_half consecutive gapSmall)
  · exact Or.inl (le_of_not_gt gapSmall)

/-- Any displayed rational below one half whose boundary polynomial is
nonnegative is a certified lower normalized gap for consecutive best pairs. -/
theorem AreConsecutiveBest.threshold_le_normalizedDeterminantGap_of_quadratic
    {source : RFAP.HurwitzRational.Fraction} {lower upper : Pair}
    (consecutive : AreConsecutiveBest source.value lower upper)
    (threshold : Coordinate)
    (thresholdLtHalf : threshold < (1 / 2 : Coordinate))
    (thresholdPolynomialNonnegative :
      0 ≤ threshold ^ 2 - 3 * threshold + 1 / 4) :
    threshold ≤
      normSq
        (1 - denominatorRatio lower upper *
          errorRatio source.value lower upper) := by
  exact threshold_le_of_quadraticBoundary thresholdLtHalf
    thresholdPolynomialNonnegative
    (normalizedDeterminantGap_boundary consecutive)

/-- Any displayed positive weights satisfying the half-square budget equation
give a certified normalized determinant gap for consecutive best pairs. -/
theorem AreConsecutiveBest.weightedThreshold_le_normalizedDeterminantGap
    {source : RFAP.HurwitzRational.Fraction} {lower upper : Pair}
    (consecutive : AreConsecutiveBest source.value lower upper)
    (leftWeight rightWeight threshold : Coordinate)
    (leftWeightPositive : 0 < leftWeight)
    (rightWeightPositive : 0 < rightWeight)
    (budget :
      leftWeight * (leftWeight + rightWeight) * threshold +
          rightWeight * (leftWeight + rightWeight) * (1 / 2 : Coordinate) =
        leftWeight * rightWeight) :
    threshold ≤
      normSq
        (1 - denominatorRatio lower upper *
          errorRatio source.value lower upper) := by
  exact weightedThreshold_le_determinantGap _ _ leftWeight rightWeight
    threshold leftWeightPositive rightWeightPositive budget
    (denominatorRatio_normSq_lt_one consecutive)
    (normalizedCoefficientExterior consecutive)

/-- Consecutive best pairs have the simple universal normalized gap
`1/12`. -/
theorem AreConsecutiveBest.one_twelfth_le_normalizedDeterminantGap
    {source : RFAP.HurwitzRational.Fraction} {lower upper : Pair}
    (consecutive : AreConsecutiveBest source.value lower upper) :
    (1 / 12 : Coordinate) ≤
      normSq
        (1 - denominatorRatio lower upper *
          errorRatio source.value lower upper) := by
  exact weightedThreshold_le_normalizedDeterminantGap consecutive
    2 1 (1 / 12) (by decide) (by decide) (by decide)

/-- Shallow displayed record for the rational threshold `35/408`. -/
def refinedGapThreshold : Coordinate :=
  RFAP.ConstructiveFraction.ofFraction ⟨35, 408, by decide⟩

/-- Shallow displayed record for the reciprocal factor `408/35`. -/
def refinedIndexFactor : Coordinate :=
  RFAP.ConstructiveFraction.ofFraction ⟨408, 35, by decide⟩

/-- Shallow displayed record for the universal bound `816/35`. -/
def refinedUniversalWindowBound : Coordinate :=
  RFAP.ConstructiveFraction.ofFraction ⟨816, 35, by decide⟩

/-- Shallow displayed record for the sharper quadratic threshold `102/1189`. -/
def quadraticGapThreshold : Coordinate :=
  RFAP.ConstructiveFraction.ofFraction ⟨102, 1189, by decide⟩

/-- Exact reciprocal `1189/102` of `quadraticGapThreshold`. -/
def quadraticIndexFactor : Coordinate :=
  RFAP.ConstructiveFraction.ofFraction ⟨1189, 102, by decide⟩

/-- Universal index-two bound `1189/51` furnished by the quadratic
threshold. -/
def quadraticUniversalWindowBound : Coordinate :=
  RFAP.ConstructiveFraction.ofFraction ⟨1189, 51, by decide⟩

theorem refinedGapThreshold_lt_half :
    refinedGapThreshold < (1 / 2 : Coordinate) := by
  unfold refinedGapThreshold
  decide

theorem refinedGapThreshold_quadratic_nonnegative :
    0 ≤ refinedGapThreshold ^ 2 - 3 * refinedGapThreshold + 1 / 4 := by
  unfold refinedGapThreshold
  decide

theorem quadraticGapThreshold_lt_half :
    quadraticGapThreshold < (1 / 2 : Coordinate) := by
  unfold quadraticGapThreshold
  decide

theorem quadraticGapThreshold_quadratic_nonnegative :
    0 ≤ quadraticGapThreshold ^ 2 - 3 * quadraticGapThreshold + 1 / 4 := by
  unfold quadraticGapThreshold
  decide

theorem quadraticGapThreshold_integerCertificate :
    (4 * 102 ^ 2 - 12 * 102 * 1189 + 1189 ^ 2 : Int) = 1 := by
  decide

theorem quadraticIndexFactor_nonneg :
    (0 : Coordinate) ≤ quadraticIndexFactor := by
  unfold quadraticIndexFactor
  decide

theorem quadraticGapThreshold_mul_quadraticIndexFactor :
    quadraticGapThreshold * quadraticIndexFactor = 1 := by
  unfold quadraticGapThreshold quadraticIndexFactor
  rw [RFAP.ConstructiveFraction.ofFraction_mulFraction]
  calc
    _ = RFAP.ConstructiveFraction.ofFraction ⟨1, 1, by decide⟩ := by
      apply RFAP.ConstructiveFraction.ofFraction_eq_of_equivalent
      change (102 * 1189 : Int) * 1 = 1 * (1189 * 102)
      ring1
    _ = 1 := (RFAP.ConstructiveFraction.natCast_eq_fraction 1).symm

theorem quadraticIndexFactor_mul_two :
    quadraticIndexFactor * 2 = quadraticUniversalWindowBound := by
  unfold quadraticIndexFactor quadraticUniversalWindowBound
  calc
    RFAP.ConstructiveFraction.ofFraction ⟨1189, 102, by decide⟩ * 2 =
        RFAP.ConstructiveFraction.ofFraction ⟨1189, 102, by decide⟩ *
          RFAP.ConstructiveFraction.ofFraction ⟨2, 1, by decide⟩ :=
      congrArg
        (fun value : Coordinate =>
          RFAP.ConstructiveFraction.ofFraction ⟨1189, 102, by decide⟩ * value)
        (RFAP.ConstructiveFraction.natCast_eq_fraction 2)
    _ = RFAP.ConstructiveFraction.ofFraction
        (RFAP.ConstructiveFraction.mulFraction
          ⟨1189, 102, by decide⟩ ⟨2, 1, by decide⟩) :=
      RFAP.ConstructiveFraction.ofFraction_mulFraction _ _
    _ = RFAP.ConstructiveFraction.ofFraction ⟨1189, 51, by decide⟩ := by
      apply RFAP.ConstructiveFraction.ofFraction_eq_of_equivalent
      change (1189 * 2 : Int) * 51 = 1189 * (102 * 1)
      ring1

theorem quadraticUniversalWindowBound_mul_denominator :
    quadraticUniversalWindowBound * 51 = 1189 := by
  unfold quadraticUniversalWindowBound
  have clearance := RFAP.ConstructiveFraction.ofFraction_mul_den
    ({ num := 1189, den := 51, den_pos := by decide } :
      RFAP.ConstructiveFraction.Fraction)
  simpa only [Int.cast_ofNat] using clearance

theorem quadraticUniversalWindowBound_lt_refinedUniversalWindowBound :
    quadraticUniversalWindowBound < refinedUniversalWindowBound := by
  unfold quadraticUniversalWindowBound refinedUniversalWindowBound
  decide

theorem refinedIndexFactor_nonneg : (0 : Coordinate) ≤ refinedIndexFactor := by
  unfold refinedIndexFactor
  decide

theorem refinedGapThreshold_mul_refinedIndexFactor :
    refinedGapThreshold * refinedIndexFactor = 1 := by
  unfold refinedGapThreshold refinedIndexFactor
  rw [RFAP.ConstructiveFraction.ofFraction_mulFraction]
  calc
    _ = RFAP.ConstructiveFraction.ofFraction ⟨1, 1, by decide⟩ := by
      apply RFAP.ConstructiveFraction.ofFraction_eq_of_equivalent
      change (35 * 408 : Int) * 1 = 1 * (408 * 35)
      ring1
    _ = 1 := (RFAP.ConstructiveFraction.natCast_eq_fraction 1).symm

theorem refinedIndexFactor_mul_two :
    refinedIndexFactor * 2 = refinedUniversalWindowBound := by
  unfold refinedIndexFactor refinedUniversalWindowBound
  calc
    RFAP.ConstructiveFraction.ofFraction ⟨408, 35, by decide⟩ * 2 =
        RFAP.ConstructiveFraction.ofFraction ⟨408, 35, by decide⟩ *
          RFAP.ConstructiveFraction.ofFraction ⟨2, 1, by decide⟩ :=
      congrArg
        (fun value : Coordinate =>
          RFAP.ConstructiveFraction.ofFraction ⟨408, 35, by decide⟩ * value)
        (RFAP.ConstructiveFraction.natCast_eq_fraction 2)
    _ = RFAP.ConstructiveFraction.ofFraction
        (RFAP.ConstructiveFraction.mulFraction
          ⟨408, 35, by decide⟩ ⟨2, 1, by decide⟩) :=
      RFAP.ConstructiveFraction.ofFraction_mulFraction _ _
    _ = RFAP.ConstructiveFraction.ofFraction ⟨816, 35, by decide⟩ := by
      apply RFAP.ConstructiveFraction.ofFraction_eq_of_equivalent
      change (408 * 2 : Int) * 35 = 816 * (35 * 1)
      ring1

theorem refinedIndexFactor_mul_denominator :
    refinedIndexFactor * 35 = 408 := by
  unfold refinedIndexFactor
  have clearance := RFAP.ConstructiveFraction.ofFraction_mul_den
    ({ num := 408, den := 35, den_pos := by decide } :
      RFAP.ConstructiveFraction.Fraction)
  simpa only [Int.cast_ofNat] using clearance

theorem refinedUniversalWindowBound_mul_denominator :
    refinedUniversalWindowBound * 35 = 816 := by
  unfold refinedUniversalWindowBound
  have clearance := RFAP.ConstructiveFraction.ofFraction_mul_den
    ({ num := 816, den := 35, den_pos := by decide } :
      RFAP.ConstructiveFraction.Fraction)
  simpa only [Int.cast_ofNat] using clearance

theorem refinedGapThreshold_mul_denominator :
    refinedGapThreshold * 408 = 35 := by
  unfold refinedGapThreshold
  have clearance := RFAP.ConstructiveFraction.ofFraction_mul_den
    ({ num := 35, den := 408, den_pos := by decide } :
      RFAP.ConstructiveFraction.Fraction)
  simpa only [Int.cast_ofNat] using clearance

theorem refinedGapThreshold_budget :
    (12 : Coordinate) * (12 + 5) * refinedGapThreshold +
          5 * (12 + 5) * (1 / 2) =
        12 * 5 := by
  have cancel2 : ((1 : Coordinate) / 2) * 2 = 1 :=
    RFAP.ConstructiveFraction.div_mul_cancel_of_ne 1 2
      (show (2 : Coordinate) ≠ 0 by decide)
  apply RFAP.ConstructiveFraction.mul_right_cancel_of_ne
    (show (2 : Coordinate) ≠ 0 by decide)
  calc
    ((12 : Coordinate) * (12 + 5) * refinedGapThreshold +
          5 * (12 + 5) * (1 / 2)) * 2 =
        refinedGapThreshold * 408 + ((1 / 2) * 2) * 85 := by
      ring1
    _ = 35 + ((1 / 2) * 2) * 85 :=
      congrArg (fun value : Coordinate =>
        value + ((1 / 2) * 2) * 85)
        refinedGapThreshold_mul_denominator
    _ = 35 + 1 * 85 :=
      congrArg (fun value : Coordinate => 35 + value * 85) cancel2
    _ = (12 * 5 : Coordinate) * 2 := by ring1

/-- The explicit weights `12,5` sharpen the normalized consecutive gap to
the displayed rational `35/408`. -/
theorem AreConsecutiveBest.refinedGap_le_normalizedDeterminantGap
    {source : RFAP.HurwitzRational.Fraction} {lower upper : Pair}
    (consecutive : AreConsecutiveBest source.value lower upper) :
    refinedGapThreshold ≤
      normSq
        (1 - denominatorRatio lower upper *
          errorRatio source.value lower upper) := by
  exact weightedThreshold_le_normalizedDeterminantGap consecutive
    12 5 refinedGapThreshold (by decide) (by decide)
    refinedGapThreshold_budget

/-- The exact consecutive-window product times its normalized determinant
gap is the displayed coefficient-index quadrance. -/
theorem AreConsecutiveBest.dirichletWindow_mul_normalizedGap_eq_index
    {source : RFAP.HurwitzRational.Fraction} {lower upper : Pair}
    (consecutive : AreConsecutiveBest source.value lower upper) :
    dirichletWindowQuadrance source.value lower upper *
          normSq
            (1 - denominatorRatio lower upper *
              errorRatio source.value lower upper) =
      (coefficientIndexQuadrance lower upper : Coordinate) := by
  have errorCancel := errorRatio_mul_lowerError consecutive
  have denominatorCancel :=
    denominatorRatio_mul_upperDenominator consecutive
  have factorIdentity :
      toGaussian (coefficientDeterminant lower upper) =
        -((toGaussian upper.denominator * error source.value lower) *
          (1 - denominatorRatio lower upper *
            errorRatio source.value lower upper)) := by
    rw [toGaussian_coefficientDeterminant]
    calc
      toGaussian lower.denominator * error source.value upper -
            toGaussian upper.denominator * error source.value lower =
          (denominatorRatio lower upper * toGaussian upper.denominator) *
                (errorRatio source.value lower upper *
                  error source.value lower) -
            toGaussian upper.denominator * error source.value lower := by
        rw [errorCancel, denominatorCancel]
      _ =
          -((toGaussian upper.denominator * error source.value lower) *
            (1 - denominatorRatio lower upper *
              errorRatio source.value lower upper)) := by
        apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
          simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
            RFAP.ConstructiveGaussian.Gaussian.sub_im,
            RFAP.ConstructiveGaussian.Gaussian.mul_re,
            RFAP.ConstructiveGaussian.Gaussian.mul_im,
            RFAP.ConstructiveGaussian.Gaussian.neg_re,
            RFAP.ConstructiveGaussian.Gaussian.neg_im,
            RFAP.ConstructiveGaussian.Gaussian.one_re,
            RFAP.ConstructiveGaussian.Gaussian.one_im] <;>
          ring1
  unfold dirichletWindowQuadrance errorQuadrance denominatorQuadrance
  change
    ((normNat upper.denominator : Coordinate) *
        normSq (error source.value lower)) *
          normSq
            (1 - denominatorRatio lower upper *
              errorRatio source.value lower upper) =
      (normNat (coefficientDeterminant lower upper) : Coordinate)
  symm
  calc
    (normNat (coefficientDeterminant lower upper) : Coordinate) =
        normSq (toGaussian (coefficientDeterminant lower upper)) :=
      (normSq_toGaussian _).symm
    _ = normSq
        (-((toGaussian upper.denominator * error source.value lower) *
          (1 - denominatorRatio lower upper *
            errorRatio source.value lower upper))) :=
      congrArg normSq factorIdentity
    _ =
        ((normNat upper.denominator : Coordinate) *
          normSq (error source.value lower)) *
            normSq
              (1 - denominatorRatio lower upper *
                errorRatio source.value lower upper) := by
      rw [normSq_neg, normSq_mul, normSq_mul, normSq_toGaussian]

/-- Any certified normalized gap gives a division-free upper constraint on
the exact consecutive-window product. -/
theorem AreConsecutiveBest.threshold_mul_dirichletWindow_le_index
    {source : RFAP.HurwitzRational.Fraction} {lower upper : Pair}
    (consecutive : AreConsecutiveBest source.value lower upper)
    (threshold : Coordinate)
    (gapLower : threshold ≤
      normSq
        (1 - denominatorRatio lower upper *
          errorRatio source.value lower upper)) :
    threshold * dirichletWindowQuadrance source.value lower upper ≤
      (coefficientIndexQuadrance lower upper : Coordinate) := by
  have windowNonnegative :
      0 ≤ dirichletWindowQuadrance source.value lower upper := by
    unfold dirichletWindowQuadrance
    exact RFAP.ConstructiveFraction.mul_nonneg_direct
      (RFAP.ConstructiveFraction.natCast_le_direct (Nat.zero_le _))
      (normSq_nonneg (error source.value lower))
  calc
    threshold * dirichletWindowQuadrance source.value lower upper =
        dirichletWindowQuadrance source.value lower upper * threshold := by
      ring1
    _ ≤ dirichletWindowQuadrance source.value lower upper *
          normSq
            (1 - denominatorRatio lower upper *
              errorRatio source.value lower upper) :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct gapLower
        windowNonnegative
    _ = (coefficientIndexQuadrance lower upper : Coordinate) :=
      dirichletWindow_mul_normalizedGap_eq_index consecutive

/-- A displayed rational passing the quadratic boundary test gives a direct
division-free consecutive-window bound. -/
theorem AreConsecutiveBest.quadraticThreshold_mul_dirichletWindow_le_index
    {source : RFAP.HurwitzRational.Fraction} {lower upper : Pair}
    (consecutive : AreConsecutiveBest source.value lower upper)
    (threshold : Coordinate)
    (thresholdLtHalf : threshold < (1 / 2 : Coordinate))
    (thresholdPolynomialNonnegative :
      0 ≤ threshold ^ 2 - 3 * threshold + 1 / 4) :
    threshold * dirichletWindowQuadrance source.value lower upper ≤
      (coefficientIndexQuadrance lower upper : Coordinate) := by
  exact threshold_mul_dirichletWindow_le_index consecutive threshold
    (threshold_le_normalizedDeterminantGap_of_quadratic consecutive threshold
      thresholdLtHalf thresholdPolynomialNonnegative)

/-- The coefficient-index dichotomy turns every passing quadratic threshold
into the universal division-free bound `threshold * window ≤ 2`. -/
theorem AreConsecutiveBest.quadraticThreshold_mul_dirichletWindow_le_two
    {source : RFAP.HurwitzRational.Fraction} {lower upper : Pair}
    (consecutive : AreConsecutiveBest source.value lower upper)
    (threshold : Coordinate)
    (thresholdLtHalf : threshold < (1 / 2 : Coordinate))
    (thresholdPolynomialNonnegative :
      0 ≤ threshold ^ 2 - 3 * threshold + 1 / 4) :
    threshold * dirichletWindowQuadrance source.value lower upper ≤ 2 := by
  have indexBound : coefficientIndexQuadrance lower upper ≤ 2 :=
    consecutive.coefficientIndexQuadrance_le_two
  have castIndexBound :
      (coefficientIndexQuadrance lower upper : Coordinate) ≤ 2 :=
    RFAP.ConstructiveFraction.natCast_le_direct indexBound
  exact (quadraticThreshold_mul_dirichletWindow_le_index consecutive threshold
    thresholdLtHalf thresholdPolynomialNonnegative).trans castIndexBound

/-- Turn any quadratic-certified rational threshold and displayed reciprocal
factor into an unscaled window bound. -/
theorem AreConsecutiveBest.dirichletWindowQuadrance_le_factor_mul_index_of_quadraticThreshold
    {source : RFAP.HurwitzRational.Fraction} {lower upper : Pair}
    (consecutive : AreConsecutiveBest source.value lower upper)
    (threshold factor : Coordinate)
    (thresholdLtHalf : threshold < (1 / 2 : Coordinate))
    (thresholdPolynomialNonnegative :
      0 ≤ threshold ^ 2 - 3 * threshold + 1 / 4)
    (thresholdMulFactor : threshold * factor = 1)
    (factorNonnegative : 0 ≤ factor) :
    dirichletWindowQuadrance source.value lower upper ≤
      factor * (coefficientIndexQuadrance lower upper : Coordinate) := by
  have thresholdBound :=
    quadraticThreshold_mul_dirichletWindow_le_index consecutive threshold
      thresholdLtHalf thresholdPolynomialNonnegative
  have scaledBound :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
      thresholdBound factorNonnegative
  calc
    dirichletWindowQuadrance source.value lower upper =
        (threshold *
          dirichletWindowQuadrance source.value lower upper) * factor := by
      calc
        dirichletWindowQuadrance source.value lower upper =
            1 * dirichletWindowQuadrance source.value lower upper := by
          ring1
        _ = (threshold * factor) *
            dirichletWindowQuadrance source.value lower upper := by
          rw [thresholdMulFactor]
        _ = (threshold *
            dirichletWindowQuadrance source.value lower upper) * factor := by
          ring1
    _ ≤ (coefficientIndexQuadrance lower upper : Coordinate) * factor :=
      scaledBound
    _ = factor *
        (coefficientIndexQuadrance lower upper : Coordinate) := by
      ring1

/-- Universal index-two consequence of a quadratic-certified threshold and
its displayed reciprocal factor. -/
theorem AreConsecutiveBest.dirichletWindowQuadrance_le_factor_mul_two_of_quadraticThreshold
    {source : RFAP.HurwitzRational.Fraction} {lower upper : Pair}
    (consecutive : AreConsecutiveBest source.value lower upper)
    (threshold factor : Coordinate)
    (thresholdLtHalf : threshold < (1 / 2 : Coordinate))
    (thresholdPolynomialNonnegative :
      0 ≤ threshold ^ 2 - 3 * threshold + 1 / 4)
    (thresholdMulFactor : threshold * factor = 1)
    (factorNonnegative : 0 ≤ factor) :
    dirichletWindowQuadrance source.value lower upper ≤ factor * 2 := by
  have indexBound : coefficientIndexQuadrance lower upper ≤ 2 :=
    consecutive.coefficientIndexQuadrance_le_two
  have castIndexBound :
      (coefficientIndexQuadrance lower upper : Coordinate) ≤ 2 :=
    RFAP.ConstructiveFraction.natCast_le_direct indexBound
  have scaledIndexBound :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct castIndexBound
      factorNonnegative
  exact
    (dirichletWindowQuadrance_le_factor_mul_index_of_quadraticThreshold
      consecutive threshold factor thresholdLtHalf
        thresholdPolynomialNonnegative thresholdMulFactor factorNonnegative).trans
      scaledIndexBound

/-- The refined `12,5` certificate bounds a consecutive squared window by
`408/35` times its coefficient-index quadrance. -/
theorem AreConsecutiveBest.dirichletWindowQuadrance_le_refinedIndexFactor
    {source : RFAP.HurwitzRational.Fraction} {lower upper : Pair}
    (consecutive : AreConsecutiveBest source.value lower upper) :
    dirichletWindowQuadrance source.value lower upper ≤
      refinedIndexFactor *
        (coefficientIndexQuadrance lower upper : Coordinate) := by
  exact
    dirichletWindowQuadrance_le_factor_mul_index_of_quadraticThreshold
      consecutive refinedGapThreshold refinedIndexFactor
        refinedGapThreshold_lt_half
        refinedGapThreshold_quadratic_nonnegative
        refinedGapThreshold_mul_refinedIndexFactor refinedIndexFactor_nonneg

/-- Refined universal source-independent bound `816/35` for every
consecutive squared Dirichlet-window product. -/
theorem AreConsecutiveBest.dirichletWindowQuadrance_le_refinedUniversalBound
    {source : RFAP.HurwitzRational.Fraction} {lower upper : Pair}
    (consecutive : AreConsecutiveBest source.value lower upper) :
    dirichletWindowQuadrance source.value lower upper ≤
      refinedUniversalWindowBound := by
  have indexBound : coefficientIndexQuadrance lower upper ≤ 2 :=
    consecutive.coefficientIndexQuadrance_le_two
  have castIndexBound :
      (coefficientIndexQuadrance lower upper : Coordinate) ≤ 2 :=
    RFAP.ConstructiveFraction.natCast_le_direct indexBound
  have scaledIndexBound :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct castIndexBound
      refinedIndexFactor_nonneg
  calc
    dirichletWindowQuadrance source.value lower upper ≤
        refinedIndexFactor *
          (coefficientIndexQuadrance lower upper : Coordinate) :=
      dirichletWindowQuadrance_le_refinedIndexFactor consecutive
    _ ≤ refinedIndexFactor * 2 := scaledIndexBound
    _ = refinedUniversalWindowBound := refinedIndexFactor_mul_two

/-- The quadratic certificate `102/1189` bounds a consecutive squared window
by `1189/102` times its coefficient-index quadrance. -/
theorem AreConsecutiveBest.dirichletWindowQuadrance_le_quadraticIndexFactor
    {source : RFAP.HurwitzRational.Fraction} {lower upper : Pair}
    (consecutive : AreConsecutiveBest source.value lower upper) :
    dirichletWindowQuadrance source.value lower upper ≤
      quadraticIndexFactor *
        (coefficientIndexQuadrance lower upper : Coordinate) :=
  dirichletWindowQuadrance_le_factor_mul_index_of_quadraticThreshold
    consecutive quadraticGapThreshold quadraticIndexFactor
      quadraticGapThreshold_lt_half
      quadraticGapThreshold_quadratic_nonnegative
      quadraticGapThreshold_mul_quadraticIndexFactor
      quadraticIndexFactor_nonneg

/-- Sharper universal source-independent bound `1189/51` for every
consecutive squared Dirichlet-window product. -/
theorem AreConsecutiveBest.dirichletWindowQuadrance_le_quadraticUniversalBound
    {source : RFAP.HurwitzRational.Fraction} {lower upper : Pair}
    (consecutive : AreConsecutiveBest source.value lower upper) :
    dirichletWindowQuadrance source.value lower upper ≤
      quadraticUniversalWindowBound := by
  calc
    dirichletWindowQuadrance source.value lower upper ≤
        quadraticIndexFactor * 2 :=
      dirichletWindowQuadrance_le_factor_mul_two_of_quadraticThreshold
        consecutive quadraticGapThreshold quadraticIndexFactor
          quadraticGapThreshold_lt_half
          quadraticGapThreshold_quadratic_nonnegative
          quadraticGapThreshold_mul_quadraticIndexFactor
          quadraticIndexFactor_nonneg
    _ = quadraticUniversalWindowBound := quadraticIndexFactor_mul_two

/-- The squared Dirichlet-window product is at most twelve times the
coefficient-index quadrance. -/
theorem AreConsecutiveBest.dirichletWindowQuadrance_le_twelve_mul_index
    {source : RFAP.HurwitzRational.Fraction} {lower upper : Pair}
    (consecutive : AreConsecutiveBest source.value lower upper) :
    dirichletWindowQuadrance source.value lower upper ≤
      12 * (coefficientIndexQuadrance lower upper : Coordinate) := by
  let window := dirichletWindowQuadrance source.value lower upper
  let gap := normSq
    (1 - denominatorRatio lower upper *
      errorRatio source.value lower upper)
  have windowNonnegative : 0 ≤ window := by
    dsimp only [window, dirichletWindowQuadrance]
    exact RFAP.ConstructiveFraction.mul_nonneg_direct
      (RFAP.ConstructiveFraction.natCast_le_direct (Nat.zero_le _))
      (normSq_nonneg (error source.value lower))
  have gapLower : (1 / 12 : Coordinate) ≤ gap := by
    dsimp only [gap]
    exact one_twelfth_le_normalizedDeterminantGap consecutive
  have productIdentity :
      window * gap =
        (coefficientIndexQuadrance lower upper : Coordinate) := by
    dsimp only [window, gap]
    exact dirichletWindow_mul_normalizedGap_eq_index consecutive
  have dividedBound :
      window * (1 / 12 : Coordinate) ≤
        (coefficientIndexQuadrance lower upper : Coordinate) := by
    calc
      window * (1 / 12 : Coordinate) ≤ window * gap :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct gapLower
          windowNonnegative
      _ = (coefficientIndexQuadrance lower upper : Coordinate) :=
        productIdentity
  have scaledBound :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct dividedBound
      (show (0 : Coordinate) ≤ 12 by decide)
  have twelfthCancel :
      (1 / 12 : Coordinate) * 12 = 1 :=
    RFAP.ConstructiveFraction.div_mul_cancel_of_ne 1 12 (by decide)
  calc
    window = (window * (1 / 12 : Coordinate)) * 12 := by
      rw [RFAP.ConstructiveFraction.mul_assoc, twelfthCancel]
      ring1
    _ ≤ (coefficientIndexQuadrance lower upper : Coordinate) * 12 :=
      scaledBound
    _ = 12 * (coefficientIndexQuadrance lower upper : Coordinate) := by
      ring1

/-- Universal source-independent upper bound for every consecutive squared
Dirichlet-window product.  The constant `24` is a first constructive
rational bound, not the optimal completed-complex constant. -/
theorem AreConsecutiveBest.dirichletWindowQuadrance_le_twentyFour
    {source : RFAP.HurwitzRational.Fraction} {lower upper : Pair}
    (consecutive : AreConsecutiveBest source.value lower upper) :
    dirichletWindowQuadrance source.value lower upper ≤ 24 := by
  have indexBound : coefficientIndexQuadrance lower upper ≤ 2 :=
    consecutive.coefficientIndexQuadrance_le_two
  have castIndexBound :
      (coefficientIndexQuadrance lower upper : Coordinate) ≤ 2 :=
    RFAP.ConstructiveFraction.natCast_le_direct indexBound
  have scaledIndexBound :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct castIndexBound
      (show (0 : Coordinate) ≤ 12 by decide)
  calc
    dirichletWindowQuadrance source.value lower upper ≤
        12 * (coefficientIndexQuadrance lower upper : Coordinate) :=
      dirichletWindowQuadrance_le_twelve_mul_index consecutive
    _ ≤ 12 * (2 : Coordinate) := scaledIndexBound
    _ = 24 := by ring1

end RFAP.DirichletWindow
