module
meta import Purelib.Elab.ConstructiveInjectivity
public import Purelib.Algebra.Monoid.Int
import Purelib.Data.GaussianInt.Pair.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Weighted
import Purelib.Data.GaussianInt.Basic
import Purelib.Data.GaussianInt.Fraction.Basic
import Purelib.Data.GaussianInt.Nearest
import Purelib.Data.GaussianInt.Pair.LinearCombination
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.SignedFraction.Arithmetic
import Purelib.Data.Rat.SignedFraction.Basic
import Purelib.Data.Rat.SignedFraction.Normalization
import Purelib.NumberTheory.Approximation.Best.Consecutive.Basic
import Purelib.NumberTheory.Approximation.Best.Error
public import Purelib.NumberTheory.Approximation.Dirichlet.Window.SourceBound
import Purelib.Data.GaussianInt.Embedding
import Purelib.NumberTheory.Approximation.Best.Consecutive.NormalForm
import Purelib.Data.GaussianInt.Norm.Basic
import Purelib.NumberTheory.Approximation.Best.Consecutive.Index
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Data

open Purelib.Data.Rat

open Purelib

open Purelib.NumberTheory.Approximation

section
@[expose] public section

/-!
# Universal finite Dirichlet-window bounds

This file strengthens the source-dependent consecutive-window certificate to
a universal rational constant.  The proof normalizes one consecutive pair,
rounds its displayed error ratio to the nearest Gaussian integer, and applies
the already proved empty-cylinder alternative to that one finite candidate.
No completed source, compactness argument, or infinite lattice is used.
-/

namespace Purelib.NumberTheory.Approximation.Dirichlet.Window.Basic

/-- Square-root-free boundary behind the weighted estimates.  If two
displayed Gaussian legs both have quadrance below one half but their sum has
quadrance at least one, the first leg's quadrance lies inside the rational
quadratic band `g^2 - 3*g + 1/4 < 0`. -/
theorem quadraticGap_neg_of_sumExterior
    {left right : Gaussian.Basic.Canonical}
    (leftSmall : Data.Gaussian.Norm.Basic.normSq left < (1 / 2 : Fraction.Rational))
    (rightSmall : Data.Gaussian.Norm.Basic.normSq right < (1 / 2 : Fraction.Rational))
    (sumExterior : (1 : Fraction.Rational) ≤ Data.Gaussian.Norm.Basic.normSq (left + right)) :
    Data.Gaussian.Norm.Basic.normSq left ^ 2 - 3 * Data.Gaussian.Norm.Basic.normSq left + 1 / 4 < 0 := by
  let leftNorm := Data.Gaussian.Norm.Basic.normSq left
  let rightNorm := Data.Gaussian.Norm.Basic.normSq right
  let dot := left.re * right.re + left.im * right.im
  let margin := 1 - leftNorm - rightNorm
  have leftNonnegative : 0 ≤ leftNorm := by
    dsimp only [leftNorm]
    exact Gaussian.Norm.Basic.normSq_nonneg left
  have rightNonnegative : 0 ≤ rightNorm := by
    dsimp only [rightNorm]
    exact Gaussian.Norm.Basic.normSq_nonneg right
  have normsBelowOne : leftNorm + rightNorm < 1 := by
    calc
      leftNorm + rightNorm <
          (1 / 2 : Fraction.Rational) + (1 / 2 : Fraction.Rational) :=
        Fraction.Order.Arithmetic.add_lt_add_direct leftSmall rightSmall
      _ = 1 := by decide
  have marginPositive : 0 < margin := by
    have differencePositive :=
      Fraction.Order.Arithmetic.sub_pos_direct normsBelowOne
    calc
      (0 : Fraction.Rational) < 1 - (leftNorm + rightNorm) := differencePositive
      _ = margin := by dsimp only [margin]; ring1
  have sumExpansion :
      Data.Gaussian.Norm.Basic.normSq (left + right) = leftNorm + rightNorm + 2 * dot := by
    dsimp only [leftNorm, rightNorm, dot]
    simp only [Data.Gaussian.Norm.Basic.normSq, Gaussian.Basic.add_re,
      Gaussian.Basic.add_im]
    ring1
  have marginLeTwiceDot : margin ≤ 2 * dot := by
    have shifted := Fraction.Order.Arithmetic.sub_le_sub_right_direct
      sumExterior (leftNorm + rightNorm)
    calc
      margin = 1 - (leftNorm + rightNorm) := by
        dsimp only [margin]
        ring1
      _ ≤ Data.Gaussian.Norm.Basic.normSq (left + right) - (leftNorm + rightNorm) := shifted
      _ = 2 * dot := by rw [sumExpansion]; ring1
  have marginSquareLe : margin ^ 2 ≤ (2 * dot) ^ 2 :=
    Fraction.Order.Arithmetic.pow_le_pow_direct marginPositive.le
      marginLeTwiceDot 2
  have dotCauchy : dot ^ 2 ≤ leftNorm * rightNorm := by
    apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
    calc
      0 ≤ (left.re * right.im - left.im * right.re) ^ 2 :=
        Fraction.Order.Arithmetic.sq_nonneg_direct _
      _ = leftNorm * rightNorm - dot ^ 2 := by
        dsimp only [leftNorm, rightNorm, dot, Data.Gaussian.Norm.Basic.normSq]
        ring1
  have marginSquareLeFourProduct :
      margin ^ 2 ≤ 4 * (leftNorm * rightNorm) := by
    calc
      margin ^ 2 ≤ (2 * dot) ^ 2 := marginSquareLe
      _ = 4 * dot ^ 2 := by ring1
      _ ≤ 4 * (leftNorm * rightNorm) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct dotCauchy
          (by decide)
  have finiteValueNonpositive :
      margin ^ 2 - 4 * leftNorm * rightNorm ≤ 0 := by
    have shifted := Fraction.Order.Arithmetic.sub_le_sub_right_direct
      marginSquareLeFourProduct (4 * (leftNorm * rightNorm))
    calc
      margin ^ 2 - 4 * leftNorm * rightNorm =
          margin ^ 2 - 4 * (leftNorm * rightNorm) := by ring1
      _ ≤ 4 * (leftNorm * rightNorm) -
          4 * (leftNorm * rightNorm) := shifted
      _ = 0 := by ring1
  let delta := (1 / 2 : Fraction.Rational) - rightNorm
  have halfPlusHalf :
      (1 / 2 : Fraction.Rational) + (1 / 2 : Fraction.Rational) = 1 := by decide
  have twiceHalf : (2 : Fraction.Rational) * (1 / 2 : Fraction.Rational) = 1 := by
    decide
  have fourHalf : (4 : Fraction.Rational) * (1 / 2 : Fraction.Rational) = 2 := by
    decide
  have halfSquare : ((1 / 2 : Fraction.Rational) ^ 2) = 1 / 4 := by
    decide
  have deltaPositive : 0 < delta := by
    dsimp only [delta]
    exact Fraction.Order.Arithmetic.sub_pos_direct rightSmall
  have twiceLeftNonnegative : 0 ≤ 2 * leftNorm :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) leftNonnegative
  have tailNonnegative : 0 ≤ 2 * leftNorm + delta :=
    add_nonneg twiceLeftNonnegative deltaPositive.le
  have factorPositive :
      0 < 2 * (1 / 2 : Fraction.Rational) + 2 * leftNorm + delta := by
    calc
      (0 : Fraction.Rational) < 2 * (1 / 2 : Fraction.Rational) := by decide
      _ ≤ 2 * (1 / 2 : Fraction.Rational) + (2 * leftNorm + delta) :=
        le_add_of_nonneg_right tailNonnegative
      _ = 2 * (1 / 2 : Fraction.Rational) + 2 * leftNorm + delta := by ring1
  have correctionPositive :
      0 < delta *
        (2 * (1 / 2 : Fraction.Rational) + 2 * leftNorm + delta) :=
    Fraction.Order.Arithmetic.mul_pos_direct deltaPositive factorPositive
  have marginIdentity :
      margin = ((1 / 2 : Fraction.Rational) - leftNorm) + delta := by
    dsimp only [margin, delta]
    calc
      (1 : Fraction.Rational) - leftNorm - rightNorm =
          ((1 / 2 : Fraction.Rational) + (1 / 2 : Fraction.Rational)) -
            leftNorm - rightNorm := by rw [halfPlusHalf]
      _ = ((1 / 2 : Fraction.Rational) - leftNorm) +
          ((1 / 2 : Fraction.Rational) - rightNorm) := by ring1
  have rightNormIdentity :
      rightNorm = (1 / 2 : Fraction.Rational) - delta := by
    dsimp only [delta]
    ring1
  have finiteValueIdentity :
      margin ^ 2 - 4 * leftNorm * rightNorm =
        ((1 / 2 : Fraction.Rational) - leftNorm) ^ 2 -
          4 * (1 / 2 : Fraction.Rational) * leftNorm +
          delta *
            (2 * (1 / 2 : Fraction.Rational) + 2 * leftNorm + delta) := by
    rw [marginIdentity, rightNormIdentity]
    ring1
  have halfValueLtFiniteValue :
      ((1 / 2 : Fraction.Rational) - leftNorm) ^ 2 -
          4 * (1 / 2 : Fraction.Rational) * leftNorm <
        margin ^ 2 - 4 * leftNorm * rightNorm := by
    calc
      ((1 / 2 : Fraction.Rational) - leftNorm) ^ 2 -
            4 * (1 / 2 : Fraction.Rational) * leftNorm =
          (((1 / 2 : Fraction.Rational) - leftNorm) ^ 2 -
            4 * (1 / 2 : Fraction.Rational) * leftNorm) + 0 := by
        ring1
      _ < (((1 / 2 : Fraction.Rational) - leftNorm) ^ 2 -
            4 * (1 / 2 : Fraction.Rational) * leftNorm) +
          delta *
            (2 * (1 / 2 : Fraction.Rational) + 2 * leftNorm + delta) :=
        Fraction.Order.Arithmetic.add_lt_add_left_direct correctionPositive _
      _ = margin ^ 2 - 4 * leftNorm * rightNorm :=
        finiteValueIdentity.symm
  have simplifiedHalfValueLtFiniteValue :
      ((1 / 2 : Fraction.Rational) - leftNorm) ^ 2 - 2 * leftNorm <
        margin ^ 2 - 4 * leftNorm * rightNorm := by
    calc
      ((1 / 2 : Fraction.Rational) - leftNorm) ^ 2 - 2 * leftNorm =
          ((1 / 2 : Fraction.Rational) - leftNorm) ^ 2 -
            4 * (1 / 2 : Fraction.Rational) * leftNorm := by rw [fourHalf]
      _ < margin ^ 2 - 4 * leftNorm * rightNorm :=
        halfValueLtFiniteValue
  have quadraticIdentity :
      ((1 / 2 : Fraction.Rational) - leftNorm) ^ 2 - 2 * leftNorm =
        leftNorm ^ 2 - 3 * leftNorm + 1 / 4 := by
    calc
      ((1 / 2 : Fraction.Rational) - leftNorm) ^ 2 - 2 * leftNorm =
          (1 / 2 : Fraction.Rational) ^ 2 -
            (2 * (1 / 2 : Fraction.Rational)) * leftNorm +
              leftNorm ^ 2 - 2 * leftNorm := by ring1
      _ = (1 / 2 : Fraction.Rational) ^ 2 - 1 * leftNorm +
          leftNorm ^ 2 - 2 * leftNorm := by rw [twiceHalf]
      _ = leftNorm ^ 2 - 3 * leftNorm +
          (1 / 2 : Fraction.Rational) ^ 2 := by ring1
      _ = leftNorm ^ 2 - 3 * leftNorm + 1 / 4 := by rw [halfSquare]
  calc
    Data.Gaussian.Norm.Basic.normSq left ^ 2 - 3 * Data.Gaussian.Norm.Basic.normSq left + 1 / 4 =
        ((1 / 2 : Fraction.Rational) - leftNorm) ^ 2 - 2 * leftNorm := by
      dsimp only [leftNorm]
      exact quadraticIdentity.symm
    _ < margin ^ 2 - 4 * leftNorm * rightNorm :=
      simplifiedHalfValueLtFiniteValue
    _ ≤ 0 := finiteValueNonpositive

/-- Turn the root-free quadratic alternative into a lower bound for any
displayed rational threshold on the nonnegative half interval. -/
theorem threshold_le_of_quadraticBoundary
    {gap threshold : Fraction.Rational}
    (thresholdLtHalf : threshold < (1 / 2 : Fraction.Rational))
    (thresholdPolynomialNonnegative :
      0 ≤ threshold ^ 2 - 3 * threshold + 1 / 4)
    (boundary :
      (1 / 2 : Fraction.Rational) ≤ gap ∨
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
          Fraction.Order.Arithmetic.add_lt_add_right_direct gapLtThreshold
            threshold
        _ < (1 / 2 : Fraction.Rational) + (1 / 2 : Fraction.Rational) :=
          Fraction.Order.Arithmetic.add_lt_add_direct thresholdLtHalf
            thresholdLtHalf
        _ = 1 := by decide
    have sumLtThree : gap + threshold < 3 :=
      sumLtOne.trans (show (1 : Fraction.Rational) < 3 by decide)
    have differencePositive : 0 < threshold - gap :=
      Fraction.Order.Arithmetic.sub_pos_direct gapLtThreshold
    have factorPositive : 0 < 3 - gap - threshold := by
      have positive := Fraction.Order.Arithmetic.sub_pos_direct sumLtThree
      calc
        (0 : Fraction.Rational) < 3 - (gap + threshold) := positive
        _ = 3 - gap - threshold := by ring1
    have correctionPositive :
        0 < (threshold - gap) * (3 - gap - threshold) :=
      Fraction.Order.Arithmetic.mul_pos_direct differencePositive
        factorPositive
    have thresholdPolynomialLtGapPolynomial :
        threshold ^ 2 - 3 * threshold + 1 / 4 <
          gap ^ 2 - 3 * gap + 1 / 4 := by
      calc
        threshold ^ 2 - 3 * threshold + 1 / 4 =
            (threshold ^ 2 - 3 * threshold + 1 / 4) + 0 := by ring1
        _ < (threshold ^ 2 - 3 * threshold + 1 / 4) +
            (threshold - gap) * (3 - gap - threshold) :=
          Fraction.Order.Arithmetic.add_lt_add_left_direct correctionPositive _
        _ = gap ^ 2 - 3 * gap + 1 / 4 := by ring1
    have gapPolynomialPositive :
        0 < gap ^ 2 - 3 * gap + 1 / 4 :=
      thresholdPolynomialNonnegative.trans_lt
        thresholdPolynomialLtGapPolynomial
    exact (not_lt_of_ge gapPolynomialPositive.le gapPolynomialNegative).elim

set_option genInjectivity false in
/-- A finite rational certificate for one weighted nearest-coefficient gap.
The budget equation is the exact arithmetic condition needed by the
two-leg estimate. -/
structure WeightCertificate where
  /-- The rational weight assigned to the determinant-gap leg. -/ leftWeight : Fraction.Rational
  /-- The rational weight assigned to the nearest-coefficient remainder leg. -/ rightWeight : Fraction.Rational
  /-- The claimed rational lower bound for the normalized determinant gap. -/ threshold : Fraction.Rational
  /-- The determinant-gap weight is strictly positive. -/ leftWeightPositive : 0 < leftWeight
  /-- The remainder weight is strictly positive. -/ rightWeightPositive : 0 < rightWeight
  /-- The weighted threshold and half-square remainder budget add to the product of the two weights. -/ budget :
    leftWeight * (leftWeight + rightWeight) * threshold +
        rightWeight * (leftWeight + rightWeight) * (1 / 2 : Fraction.Rational) =
      leftWeight * rightWeight

constructive_injectivity WeightCertificate

/-- Nearest-Gaussian-integer reduction turns a normalized exterior
alternative into any rational gap certified by two positive displayed
weights and the exact half-square budget equation. -/
theorem weightedThreshold_le_determinantGap
    (errorRatio denominatorRatio : Gaussian.Basic.Canonical)
    (leftWeight rightWeight threshold : Fraction.Rational)
    (leftWeightPositive : 0 < leftWeight)
    (rightWeightPositive : 0 < rightWeight)
    (budget :
      leftWeight * (leftWeight + rightWeight) * threshold +
          rightWeight * (leftWeight + rightWeight) * (1 / 2 : Fraction.Rational) =
        leftWeight * rightWeight)
    (denominatorInside : Data.Gaussian.Norm.Basic.normSq denominatorRatio < 1)
    (coefficientExterior : ∀ coefficient : GaussianInt,
      (1 : Fraction.Rational) ≤
          Data.Gaussian.Norm.Basic.normSq (errorRatio - GaussianInt.toGaussian coefficient) ∨
        1 ≤ Data.Gaussian.Norm.Basic.normSq
          (1 - GaussianInt.toGaussian coefficient * denominatorRatio)) :
    threshold ≤
      Data.Gaussian.Norm.Basic.normSq (1 - denominatorRatio * errorRatio) := by
  apply le_of_not_gt
  intro gapSmall
  let coefficient := GaussianInt.Nearest.nearest errorRatio
  let remainder := GaussianInt.Nearest.remainder errorRatio
  have remainderBound : Data.Gaussian.Norm.Basic.normSq remainder ≤ (1 / 2 : Fraction.Rational) := by
    dsimp only [remainder]
    exact GaussianInt.Nearest.remainder_normSq_le_half errorRatio
  by_cases coefficientZero : coefficient = 0
  · have remainderIdentity : remainder = errorRatio := by
      change errorRatio -
          GaussianInt.toGaussian (GaussianInt.Nearest.nearest errorRatio) = errorRatio
      change GaussianInt.Nearest.nearest errorRatio = 0 at coefficientZero
      rw [coefficientZero, GaussianInt.toGaussian_zero]
      apply Gaussian.Basic.ext <;>
        simp only [Gaussian.Basic.sub_re,
          Gaussian.Basic.sub_im,
          Gaussian.Basic.zero_re,
          Gaussian.Basic.zero_im] <;>
        ring1
    have productSmall :
        Data.Gaussian.Norm.Basic.normSq (denominatorRatio * errorRatio) < 1 / 2 := by
      apply Gaussian.Norm.Weighted.normSq_mul_lt_half_of_left_lt_one_of_right_le_half
        denominatorInside
      rw [← remainderIdentity]
      exact remainderBound
    have sumIdentity :
        (1 - denominatorRatio * errorRatio) +
            denominatorRatio * errorRatio = 1 := by
      apply Gaussian.Basic.ext <;>
        simp only [Gaussian.Basic.sub_re,
          Gaussian.Basic.sub_im,
          Gaussian.Basic.add_re,
          Gaussian.Basic.add_im,
          Gaussian.Basic.mul_re,
          Gaussian.Basic.mul_im,
          Gaussian.Basic.one_re,
          Gaussian.Basic.one_im] <;>
        ring1
    have impossible := Gaussian.Norm.Weighted.weighted_sum_lt_one leftWeight rightWeight threshold
      leftWeightPositive rightWeightPositive budget gapSmall productSmall
    rw [sumIdentity, Gaussian.Norm.Basic.normSq_one] at impossible
    exact (lt_irrefl 1 impossible).elim
  · have exterior := coefficientExterior coefficient
    have remainderIdentity :
        remainder = errorRatio - GaussianInt.toGaussian coefficient := rfl
    rcases exterior with errorExterior | denominatorExterior
    · have oneLeHalf : (1 : Fraction.Rational) ≤ 1 / 2 :=
        errorExterior.trans (by
          rw [← remainderIdentity]
          exact remainderBound)
      exact (not_le_of_gt (show (1 / 2 : Fraction.Rational) < 1 by decide)
        oneLeHalf).elim
    · have remainderProductSmall :
          Data.Gaussian.Norm.Basic.normSq (denominatorRatio * remainder) < 1 / 2 :=
        Gaussian.Norm.Weighted.normSq_mul_lt_half_of_left_lt_one_of_right_le_half
          denominatorInside remainderBound
      have denominatorIdentity :
          1 - GaussianInt.toGaussian coefficient * denominatorRatio =
            (1 - denominatorRatio * errorRatio) +
              denominatorRatio * remainder := by
        dsimp only [remainder, coefficient, GaussianInt.Nearest.remainder]
        apply Gaussian.Basic.ext <;>
          simp only [Gaussian.Basic.sub_re,
            Gaussian.Basic.sub_im,
            Gaussian.Basic.add_re,
            Gaussian.Basic.add_im,
            Gaussian.Basic.mul_re,
            Gaussian.Basic.mul_im,
            Gaussian.Basic.one_re,
            Gaussian.Basic.one_im] <;>
          ring1
      have denominatorSmall := Gaussian.Norm.Weighted.weighted_sum_lt_one leftWeight rightWeight
        threshold leftWeightPositive rightWeightPositive budget gapSmall
        remainderProductSmall
      rw [← denominatorIdentity] at denominatorSmall
      exact (not_lt_of_ge denominatorExterior denominatorSmall).elim

/-- Apply a displayed weight certificate to a normalized exterior
alternative. -/
theorem WeightCertificate.threshold_le_determinantGap
    (certificate : Dirichlet.Window.Basic.WeightCertificate)
    (errorRatio denominatorRatio : Gaussian.Basic.Canonical)
    (denominatorInside : Data.Gaussian.Norm.Basic.normSq denominatorRatio < 1)
    (coefficientExterior : ∀ coefficient : GaussianInt,
      (1 : Fraction.Rational) ≤
          Data.Gaussian.Norm.Basic.normSq (errorRatio - GaussianInt.toGaussian coefficient) ∨
        1 ≤ Data.Gaussian.Norm.Basic.normSq
          (1 - GaussianInt.toGaussian coefficient * denominatorRatio)) :
    certificate.threshold ≤
      Data.Gaussian.Norm.Basic.normSq (1 - denominatorRatio * errorRatio) := by
  exact Dirichlet.Window.Basic.weightedThreshold_le_determinantGap errorRatio denominatorRatio
    certificate.leftWeight certificate.rightWeight certificate.threshold
    certificate.leftWeightPositive certificate.rightWeightPositive
    certificate.budget denominatorInside coefficientExterior

/-- The small weights `2,1` give the simple gap `1/12`. -/
theorem one_twelfth_le_determinantGap
    (errorRatio denominatorRatio : Gaussian.Basic.Canonical)
    (denominatorInside : Data.Gaussian.Norm.Basic.normSq denominatorRatio < 1)
    (coefficientExterior : ∀ coefficient : GaussianInt,
      (1 : Fraction.Rational) ≤
          Data.Gaussian.Norm.Basic.normSq (errorRatio - GaussianInt.toGaussian coefficient) ∨
        1 ≤ Data.Gaussian.Norm.Basic.normSq
          (1 - GaussianInt.toGaussian coefficient * denominatorRatio)) :
    (1 / 12 : Fraction.Rational) ≤
      Data.Gaussian.Norm.Basic.normSq (1 - denominatorRatio * errorRatio) := by
  exact Dirichlet.Window.Basic.weightedThreshold_le_determinantGap errorRatio denominatorRatio
    2 1 (1 / 12) (by decide) (by decide) (by decide) denominatorInside
    coefficientExterior

/-! ## Normalizing one consecutive pair -/

/-- Upper error divided by lower error for a consecutive best pair. -/
def errorRatio (source : Gaussian.Basic.Canonical)
  (lower upper : GaussianInt.Pair.Basic.ConvergentPair) : Gaussian.Basic.Canonical :=
  Best.Error.error source upper *
    Data.Gaussian.Field.inv (Best.Error.error source lower)

/-- Lower denominator divided by upper denominator for a consecutive best
pair. -/
def denominatorRatio (lower upper :
  GaussianInt.Pair.Basic.ConvergentPair) : Gaussian.Basic.Canonical :=
  GaussianInt.toGaussian lower.denominator *
    Data.Gaussian.Field.inv (GaussianInt.toGaussian upper.denominator)

/-- Cancel a nonzero Gaussian right factor against its displayed inverse. -/
private theorem mul_inv_mul_cancel (left right :
  Gaussian.Basic.Canonical)
    (rightNonzero : right ≠ 0) :
    (left * Data.Gaussian.Field.inv right) * right = left := by
  calc
    (left * Data.Gaussian.Field.inv right) * right =
        left * (Data.Gaussian.Field.inv right * right) :=
      Gaussian.Basic.mul_assoc _ _ _
    _ = left * 1 := by
      rw [Gaussian.Field.inv_mul right rightNonzero]
    _ = left := Gaussian.Basic.mul_one _

/-- The lower error of a consecutive best pair is nonzero.

The upper error has strictly smaller nonnegative quadrance, excluding exact termination at the lower pair. -/
theorem AreConsecutiveBest.lowerError_nonzero
    {source : GaussianInt.Fraction} {lower upper : GaussianInt.Pair.Basic.ConvergentPair}
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest source.value lower upper) :
    Best.Error.error source.value lower ≠ 0 := by
  intro lowerErrorZero
  have lowerQuadranceZero := congrArg Data.Gaussian.Norm.Basic.normSq lowerErrorZero
  rw [Gaussian.Norm.Basic.normSq_zero] at lowerQuadranceZero
  have errorOrdered :
      Best.Error.errorQuadrance source.value upper <
        Best.Error.errorQuadrance source.value lower :=
    consecutive.2.1.2.1 lower consecutive.1.1 consecutive.2.2.1
  change Data.Gaussian.Norm.Basic.normSq (Best.Error.error source.value upper) <
    Data.Gaussian.Norm.Basic.normSq (Best.Error.error source.value lower) at errorOrdered
  rw [lowerQuadranceZero] at errorOrdered
  exact (not_lt_of_ge (Gaussian.Norm.Basic.normSq_nonneg (Best.Error.error source.value upper))
    errorOrdered).elim

/-- The upper denominator of a consecutive best pair remains nonzero after Gaussian embedding. -/
theorem
  AreConsecutiveBest.upperDenominatorGaussianNonzero
    {source : GaussianInt.Fraction} {lower upper : GaussianInt.Pair.Basic.ConvergentPair}
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest source.value lower upper) :
    GaussianInt.toGaussian upper.denominator ≠ 0 := by
  intro embeddedZero
  exact consecutive.2.1.1 (GaussianInt.toGaussian_eq_zero.mp embeddedZero)

/-- Multiplying the normalized error ratio by the lower error recovers the upper error. -/
theorem AreConsecutiveBest.errorRatio_mul_lowerError
    {source : GaussianInt.Fraction} {lower upper : GaussianInt.Pair.Basic.ConvergentPair}
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest source.value lower upper) :
    Dirichlet.Window.Basic.errorRatio source.value lower upper * Best.Error.error source.value lower =
      Best.Error.error source.value upper := by
  exact Dirichlet.Window.Basic.mul_inv_mul_cancel _ _
    (Dirichlet.Window.Basic.AreConsecutiveBest.lowerError_nonzero consecutive)

/-- Multiplying the denominator ratio by the upper denominator recovers the lower denominator. -/
theorem
  AreConsecutiveBest.denominatorRatio_mul_upperDenominator
    {source : GaussianInt.Fraction} {lower upper : GaussianInt.Pair.Basic.ConvergentPair}
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest source.value lower upper) :
    Dirichlet.Window.Basic.denominatorRatio lower upper * GaussianInt.toGaussian upper.denominator =
      GaussianInt.toGaussian lower.denominator := by
  exact Dirichlet.Window.Basic.mul_inv_mul_cancel _ _
    (Dirichlet.Window.Basic.AreConsecutiveBest.upperDenominatorGaussianNonzero consecutive)

/-- Consecutive denominator ordering places the normalized denominator ratio inside the unit disc. -/
theorem
  AreConsecutiveBest.denominatorRatio_normSq_lt_one
    {source : GaussianInt.Fraction} {lower upper : GaussianInt.Pair.Basic.ConvergentPair}
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest source.value lower upper) :
    Data.Gaussian.Norm.Basic.normSq (Dirichlet.Window.Basic.denominatorRatio lower upper) < 1 := by
  have upperPositive :
    0 < Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian upper.denominator) :=
    Gaussian.Norm.Basic.normSq_pos (Dirichlet.Window.Basic.AreConsecutiveBest.upperDenominatorGaussianNonzero
      consecutive)
  unfold Dirichlet.Window.Basic.denominatorRatio
  rw [Gaussian.Norm.Basic.normSq_mul,
    Gaussian.Field.normSq_inv _
      (Dirichlet.Window.Basic.AreConsecutiveBest.upperDenominatorGaussianNonzero consecutive)]
  change Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian lower.denominator) /
      Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian upper.denominator) < 1
  apply (Fraction.Order.Field.div_lt_iff_pos upperPositive).mpr
  rw [Fraction.Field.one_mul, GaussianInt.normSq_toGaussian,
    GaussianInt.normSq_toGaussian]
  exact Fraction.Cast.Order.natCast_lt_direct consecutive.2.2.1

/-- Every integral coefficient gives a normalized exterior alternative. -/
theorem
  AreConsecutiveBest.normalizedCoefficientExterior
    {source : GaussianInt.Fraction} {lower upper : GaussianInt.Pair.Basic.ConvergentPair}
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest source.value lower upper)
    (coefficient : GaussianInt) :
    (1 : Fraction.Rational) ≤
        Data.Gaussian.Norm.Basic.normSq (Dirichlet.Window.Basic.errorRatio source.value lower upper -
          GaussianInt.toGaussian coefficient) ∨
      1 ≤ Data.Gaussian.Norm.Basic.normSq
        (1 - GaussianInt.toGaussian coefficient * Dirichlet.Window.Basic.denominatorRatio lower upper) := by
  let candidate := GaussianInt.Pair.LinearCombination.linearCombination lower upper (-coefficient) 1
  have outside := (Best.Consecutive.NormalForm.AreConsecutiveBest.linearCombination_outside_mixedCylinder consecutive)
    (-coefficient) 1 (Or.inr (by decide))
  have lowerErrorPositive :
      0 < Best.Error.errorQuadrance source.value lower :=
    Gaussian.Norm.Basic.normSq_pos (Dirichlet.Window.Basic.AreConsecutiveBest.lowerError_nonzero consecutive)
  have upperDenominatorPositive :
      (0 : Fraction.Rational) < Best.Error.denominatorQuadrance upper :=
    Fraction.Cast.Order.natCast_pos_direct
      (GaussianInt.normNat_pos consecutive.2.1.1)
  have errorIdentity :
      Best.Error.error source.value candidate =
        (Dirichlet.Window.Basic.errorRatio source.value lower upper - GaussianInt.toGaussian coefficient) *
          Best.Error.error source.value lower := by
    dsimp only [candidate]
    rw [Best.Error.error_linearCombination_negUnit_one]
    have ratioCancel :=
      Dirichlet.Window.Basic.AreConsecutiveBest.errorRatio_mul_lowerError consecutive
    calc
      Best.Error.error source.value upper -
            GaussianInt.toGaussian coefficient * Best.Error.error source.value lower =
          Dirichlet.Window.Basic.errorRatio source.value lower upper * Best.Error.error source.value lower -
            GaussianInt.toGaussian coefficient * Best.Error.error source.value lower := by
        rw [ratioCancel]
      _ =
          (Dirichlet.Window.Basic.errorRatio source.value lower upper - GaussianInt.toGaussian coefficient) *
            Best.Error.error source.value lower := by
        apply Gaussian.Basic.ext <;>
          simp only [Gaussian.Basic.sub_re,
            Gaussian.Basic.sub_im,
            Gaussian.Basic.mul_re,
            Gaussian.Basic.mul_im] <;>
          ring1
  have denominatorIdentity :
      GaussianInt.toGaussian candidate.denominator =
        (1 - GaussianInt.toGaussian coefficient * Dirichlet.Window.Basic.denominatorRatio lower upper) *
          GaussianInt.toGaussian upper.denominator := by
    dsimp only [candidate]
    rw [Best.Error.toGaussian_denominator_linearCombination_negUnit_one]
    have ratioCancel :=
      Dirichlet.Window.Basic.AreConsecutiveBest.denominatorRatio_mul_upperDenominator consecutive
    calc
      GaussianInt.toGaussian upper.denominator -
            GaussianInt.toGaussian coefficient * GaussianInt.toGaussian lower.denominator =
          GaussianInt.toGaussian upper.denominator -
            GaussianInt.toGaussian coefficient *
              (Dirichlet.Window.Basic.denominatorRatio lower upper *
                GaussianInt.toGaussian upper.denominator) := by
        rw [ratioCancel]
      _ =
          (1 - GaussianInt.toGaussian coefficient * Dirichlet.Window.Basic.denominatorRatio lower upper) *
            GaussianInt.toGaussian upper.denominator := by
        apply Gaussian.Basic.ext <;>
          simp only [Gaussian.Basic.sub_re,
            Gaussian.Basic.sub_im,
            Gaussian.Basic.mul_re,
            Gaussian.Basic.mul_im,
            Gaussian.Basic.one_re,
            Gaussian.Basic.one_im] <;>
          ring1
  rcases outside with errorOutside | denominatorOutside
  · left
    apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct
      (c := Best.Error.errorQuadrance source.value lower)
    · calc
        (1 : Fraction.Rational) * Best.Error.errorQuadrance source.value lower =
            Best.Error.errorQuadrance source.value lower := by ring1
        _ ≤ Best.Error.errorQuadrance source.value candidate := errorOutside
        _ =
            Data.Gaussian.Norm.Basic.normSq (Dirichlet.Window.Basic.errorRatio source.value lower upper -
                GaussianInt.toGaussian coefficient) *
              Best.Error.errorQuadrance source.value lower := by
          unfold Best.Error.errorQuadrance
          rw [errorIdentity, Gaussian.Norm.Basic.normSq_mul]
    · exact lowerErrorPositive
  · right
    have castOutside :=
      Fraction.Cast.Order.natCast_le_direct denominatorOutside
    apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct
      (c := (Best.Error.denominatorQuadrance upper : Fraction.Rational))
    · calc
        (1 : Fraction.Rational) * (Best.Error.denominatorQuadrance upper : Fraction.Rational) =
            (Best.Error.denominatorQuadrance upper : Fraction.Rational) := by ring1
        _ ≤ (Best.Error.denominatorQuadrance candidate : Fraction.Rational) := castOutside
        _ = Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian candidate.denominator) :=
          (GaussianInt.normSq_toGaussian _).symm
        _ =
            Data.Gaussian.Norm.Basic.normSq
                (1 - GaussianInt.toGaussian coefficient *
                  Dirichlet.Window.Basic.denominatorRatio lower upper) *
              (Best.Error.denominatorQuadrance upper : Fraction.Rational) := by
          rw [denominatorIdentity, Gaussian.Norm.Basic.normSq_mul, GaussianInt.normSq_toGaussian]
          rfl
    · exact upperDenominatorPositive

/-- Every nontrivial integral linear combination gives a normalized exterior
alternative.  Unlike `normalizedCoefficientExterior`, which fixes the upper
coefficient to one, this form retains both coefficients.  The norm-two
leading combinations needed by the sharp index-one chamber cannot in general
be divided to the one-coefficient form inside `ℤ[i]`. -/
theorem
  AreConsecutiveBest.normalizedLinearCombinationExterior
    {source : GaussianInt.Fraction} {lower upper : GaussianInt.Pair.Basic.ConvergentPair}
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest source.value lower upper)
    (leftCoefficient rightCoefficient : GaussianInt)
    (coefficientNonzero :
      leftCoefficient ≠ 0 ∨ rightCoefficient ≠ 0) :
    (1 : Fraction.Rational) ≤
        Data.Gaussian.Norm.Basic.normSq
          (GaussianInt.toGaussian leftCoefficient +
            GaussianInt.toGaussian rightCoefficient *
              Dirichlet.Window.Basic.errorRatio source.value lower upper) ∨
      1 ≤
        Data.Gaussian.Norm.Basic.normSq
          (GaussianInt.toGaussian leftCoefficient * Dirichlet.Window.Basic.denominatorRatio lower upper +
            GaussianInt.toGaussian rightCoefficient) := by
  let candidate := GaussianInt.Pair.LinearCombination.linearCombination lower upper
    leftCoefficient rightCoefficient
  have outside := (Best.Consecutive.NormalForm.AreConsecutiveBest.linearCombination_outside_mixedCylinder consecutive)
    leftCoefficient rightCoefficient coefficientNonzero
  have lowerErrorPositive :
      0 < Best.Error.errorQuadrance source.value lower :=
    Gaussian.Norm.Basic.normSq_pos (Dirichlet.Window.Basic.AreConsecutiveBest.lowerError_nonzero consecutive)
  have upperDenominatorPositive :
      (0 : Fraction.Rational) < Best.Error.denominatorQuadrance upper :=
    Fraction.Cast.Order.natCast_pos_direct
      (GaussianInt.normNat_pos consecutive.2.1.1)
  have errorIdentity :
      Best.Error.error source.value candidate =
        (GaussianInt.toGaussian leftCoefficient +
            GaussianInt.toGaussian rightCoefficient *
              Dirichlet.Window.Basic.errorRatio source.value lower upper) *
          Best.Error.error source.value lower := by
    dsimp only [candidate]
    rw [Best.Error.error_linearCombination]
    have ratioCancel := Dirichlet.Window.Basic.AreConsecutiveBest.errorRatio_mul_lowerError consecutive
    calc
      GaussianInt.toGaussian leftCoefficient * Best.Error.error source.value lower +
            GaussianInt.toGaussian rightCoefficient * Best.Error.error source.value upper =
          GaussianInt.toGaussian leftCoefficient * Best.Error.error source.value lower +
            GaussianInt.toGaussian rightCoefficient *
              (Dirichlet.Window.Basic.errorRatio source.value lower upper *
                Best.Error.error source.value lower) := by
        rw [ratioCancel]
      _ =
          (GaussianInt.toGaussian leftCoefficient +
              GaussianInt.toGaussian rightCoefficient *
                Dirichlet.Window.Basic.errorRatio source.value lower upper) *
            Best.Error.error source.value lower := by
        apply Gaussian.Basic.ext <;>
          simp only [Gaussian.Basic.add_re,
            Gaussian.Basic.add_im,
            Gaussian.Basic.mul_re,
            Gaussian.Basic.mul_im] <;>
          ring1
  have denominatorIdentity :
      GaussianInt.toGaussian candidate.denominator =
        (GaussianInt.toGaussian leftCoefficient * Dirichlet.Window.Basic.denominatorRatio lower upper +
            GaussianInt.toGaussian rightCoefficient) *
          GaussianInt.toGaussian upper.denominator := by
    dsimp only [candidate, GaussianInt.Pair.LinearCombination.linearCombination]
    rw [GaussianInt.toGaussian_add, GaussianInt.toGaussian_mul, GaussianInt.toGaussian_mul]
    have ratioCancel := Dirichlet.Window.Basic.AreConsecutiveBest.denominatorRatio_mul_upperDenominator consecutive
    calc
      GaussianInt.toGaussian leftCoefficient * GaussianInt.toGaussian lower.denominator +
            GaussianInt.toGaussian rightCoefficient * GaussianInt.toGaussian upper.denominator =
          GaussianInt.toGaussian leftCoefficient *
              (Dirichlet.Window.Basic.denominatorRatio lower upper *
                GaussianInt.toGaussian upper.denominator) +
            GaussianInt.toGaussian rightCoefficient * GaussianInt.toGaussian upper.denominator := by
        rw [ratioCancel]
      _ =
          (GaussianInt.toGaussian leftCoefficient * Dirichlet.Window.Basic.denominatorRatio lower upper +
              GaussianInt.toGaussian rightCoefficient) *
            GaussianInt.toGaussian upper.denominator := by
        apply Gaussian.Basic.ext <;>
          simp only [Gaussian.Basic.add_re,
            Gaussian.Basic.add_im,
            Gaussian.Basic.mul_re,
            Gaussian.Basic.mul_im] <;>
          ring1
  rcases outside with errorOutside | denominatorOutside
  · left
    apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct
      (c := Best.Error.errorQuadrance source.value lower)
    · calc
        (1 : Fraction.Rational) * Best.Error.errorQuadrance source.value lower =
            Best.Error.errorQuadrance source.value lower := by ring1
        _ ≤ Best.Error.errorQuadrance source.value candidate := errorOutside
        _ =
            Data.Gaussian.Norm.Basic.normSq
                (GaussianInt.toGaussian leftCoefficient +
                  GaussianInt.toGaussian rightCoefficient *
                    Dirichlet.Window.Basic.errorRatio source.value lower upper) *
              Best.Error.errorQuadrance source.value lower := by
          unfold Best.Error.errorQuadrance
          rw [errorIdentity, Gaussian.Norm.Basic.normSq_mul]
    · exact lowerErrorPositive
  · right
    have castOutside :=
      Fraction.Cast.Order.natCast_le_direct denominatorOutside
    apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct
      (c := (Best.Error.denominatorQuadrance upper : Fraction.Rational))
    · calc
        (1 : Fraction.Rational) * (Best.Error.denominatorQuadrance upper : Fraction.Rational) =
            (Best.Error.denominatorQuadrance upper : Fraction.Rational) := by ring1
        _ ≤ (Best.Error.denominatorQuadrance candidate : Fraction.Rational) := castOutside
        _ = Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian candidate.denominator) :=
          (GaussianInt.normSq_toGaussian _).symm
        _ =
            Data.Gaussian.Norm.Basic.normSq
                (GaussianInt.toGaussian leftCoefficient *
                    Dirichlet.Window.Basic.denominatorRatio lower upper +
                  GaussianInt.toGaussian rightCoefficient) *
              (Best.Error.denominatorQuadrance upper : Fraction.Rational) := by
          rw [denominatorIdentity, Gaussian.Norm.Basic.normSq_mul, GaussianInt.normSq_toGaussian]
          rfl
    · exact upperDenominatorPositive

/-- Below the trivial half-gap branch, a consecutive normalized determinant
gap satisfies the exact square-root-free quadratic constraint. -/
theorem
  AreConsecutiveBest.normalizedDeterminantGap_quadratic_neg_of_lt_half
    {source : GaussianInt.Fraction} {lower upper : GaussianInt.Pair.Basic.ConvergentPair}
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest source.value lower upper)
    (gapSmall :
      Data.Gaussian.Norm.Basic.normSq
        (1 - Dirichlet.Window.Basic.denominatorRatio lower upper *
          Dirichlet.Window.Basic.errorRatio source.value lower upper) < (1 / 2 : Fraction.Rational)) :
    Data.Gaussian.Norm.Basic.normSq
          (1 - Dirichlet.Window.Basic.denominatorRatio lower upper *
            Dirichlet.Window.Basic.errorRatio source.value lower upper) ^ 2 -
        3 * Data.Gaussian.Norm.Basic.normSq
          (1 - Dirichlet.Window.Basic.denominatorRatio lower upper *
            Dirichlet.Window.Basic.errorRatio source.value lower upper) +
      1 / 4 < 0 := by
  let coefficient := GaussianInt.Nearest.nearest
    (Dirichlet.Window.Basic.errorRatio source.value lower upper)
  let remainder := GaussianInt.Nearest.remainder
    (Dirichlet.Window.Basic.errorRatio source.value lower upper)
  let gap := 1 - Dirichlet.Window.Basic.denominatorRatio lower upper *
    Dirichlet.Window.Basic.errorRatio source.value lower upper
  let remainderProduct := Dirichlet.Window.Basic.denominatorRatio lower upper * remainder
  have remainderBound : Data.Gaussian.Norm.Basic.normSq remainder ≤ (1 / 2 : Fraction.Rational) := by
    dsimp only [remainder]
    exact GaussianInt.Nearest.remainder_normSq_le_half
      (Dirichlet.Window.Basic.errorRatio source.value lower upper)
  have remainderProductSmall :
      Data.Gaussian.Norm.Basic.normSq remainderProduct < (1 / 2 : Fraction.Rational) := by
    dsimp only [remainderProduct]
    exact Gaussian.Norm.Weighted.normSq_mul_lt_half_of_left_lt_one_of_right_le_half
      (Dirichlet.Window.Basic.AreConsecutiveBest.denominatorRatio_normSq_lt_one consecutive) remainderBound
  have sumExterior : (1 : Fraction.Rational) ≤ Data.Gaussian.Norm.Basic.normSq (gap + remainderProduct) := by
    by_cases coefficientZero : coefficient = 0
    · have remainderIdentity :
          remainder = Dirichlet.Window.Basic.errorRatio source.value lower upper := by
        change Dirichlet.Window.Basic.errorRatio source.value lower upper -
            GaussianInt.toGaussian
              (GaussianInt.Nearest.nearest
                (Dirichlet.Window.Basic.errorRatio source.value lower upper)) =
          Dirichlet.Window.Basic.errorRatio source.value lower upper
        change GaussianInt.Nearest.nearest
          (Dirichlet.Window.Basic.errorRatio source.value lower upper) = 0 at coefficientZero
        rw [coefficientZero, GaussianInt.toGaussian_zero]
        apply Gaussian.Basic.ext <;>
          simp only [Gaussian.Basic.sub_re,
            Gaussian.Basic.sub_im,
            Gaussian.Basic.zero_re,
            Gaussian.Basic.zero_im] <;>
          ring1
      have sumIdentity : gap + remainderProduct = 1 := by
        dsimp only [gap, remainderProduct]
        rw [remainderIdentity]
        apply Gaussian.Basic.ext <;>
          simp only [Gaussian.Basic.sub_re,
            Gaussian.Basic.sub_im,
            Gaussian.Basic.add_re,
            Gaussian.Basic.add_im,
            Gaussian.Basic.mul_re,
            Gaussian.Basic.mul_im,
            Gaussian.Basic.one_re,
            Gaussian.Basic.one_im] <;>
          ring1
      rw [sumIdentity, Gaussian.Norm.Basic.normSq_one]
    · have exterior := Dirichlet.Window.Basic.AreConsecutiveBest.normalizedCoefficientExterior consecutive coefficient
      have remainderIdentity :
          remainder = Dirichlet.Window.Basic.errorRatio source.value lower upper -
            GaussianInt.toGaussian coefficient := rfl
      rcases exterior with errorExterior | denominatorExterior
      · have oneLeHalf : (1 : Fraction.Rational) ≤ 1 / 2 :=
          errorExterior.trans (by
            rw [← remainderIdentity]
            exact remainderBound)
        exact ((not_le_of_gt (show (1 / 2 : Fraction.Rational) < 1 by decide))
          oneLeHalf).elim
      · have denominatorIdentity :
            1 - GaussianInt.toGaussian coefficient * Dirichlet.Window.Basic.denominatorRatio lower upper =
              gap + remainderProduct := by
          dsimp only [gap, remainderProduct, remainder, coefficient,
            GaussianInt.Nearest.remainder]
          apply Gaussian.Basic.ext <;>
            simp only [Gaussian.Basic.sub_re,
              Gaussian.Basic.sub_im,
              Gaussian.Basic.add_re,
              Gaussian.Basic.add_im,
              Gaussian.Basic.mul_re,
              Gaussian.Basic.mul_im,
              Gaussian.Basic.one_re,
              Gaussian.Basic.one_im] <;>
            ring1
        rw [← denominatorIdentity]
        exact denominatorExterior
  apply Dirichlet.Window.Basic.quadraticGap_neg_of_sumExterior
  · exact gapSmall
  · exact remainderProductSmall
  · exact sumExterior

/-- Root-free algebraic boundary supplied by the nearest-coefficient argument:
the normalized gap is at least one half, or it lies in the displayed rational
quadratic band. -/
theorem
  AreConsecutiveBest.normalizedDeterminantGap_boundary
    {source : GaussianInt.Fraction} {lower upper : GaussianInt.Pair.Basic.ConvergentPair}
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest source.value lower upper) :
    (1 / 2 : Fraction.Rational) ≤
        Data.Gaussian.Norm.Basic.normSq
          (1 - Dirichlet.Window.Basic.denominatorRatio lower upper *
            Dirichlet.Window.Basic.errorRatio source.value lower upper) ∨
      Data.Gaussian.Norm.Basic.normSq
            (1 - Dirichlet.Window.Basic.denominatorRatio lower upper *
              Dirichlet.Window.Basic.errorRatio source.value lower upper) ^ 2 -
          3 * Data.Gaussian.Norm.Basic.normSq
            (1 - Dirichlet.Window.Basic.denominatorRatio lower upper *
              Dirichlet.Window.Basic.errorRatio source.value lower upper) +
        1 / 4 < 0 := by
  by_cases gapSmall :
      Data.Gaussian.Norm.Basic.normSq
        (1 - Dirichlet.Window.Basic.denominatorRatio lower upper *
          Dirichlet.Window.Basic.errorRatio source.value lower upper) < (1 / 2 : Fraction.Rational)
  · exact Or.inr
      (Dirichlet.Window.Basic.AreConsecutiveBest.normalizedDeterminantGap_quadratic_neg_of_lt_half consecutive gapSmall)
  · exact Or.inl (le_of_not_gt gapSmall)

/-- Any displayed rational below one half whose boundary polynomial is
nonnegative is a certified lower normalized gap for consecutive best pairs. -/
theorem
  AreConsecutiveBest.threshold_le_normalizedDeterminantGap_of_quadratic
    {source : GaussianInt.Fraction} {lower upper : GaussianInt.Pair.Basic.ConvergentPair}
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest source.value lower upper)
    (threshold : Fraction.Rational)
    (thresholdLtHalf : threshold < (1 / 2 : Fraction.Rational))
    (thresholdPolynomialNonnegative :
      0 ≤ threshold ^ 2 - 3 * threshold + 1 / 4) :
    threshold ≤
      Data.Gaussian.Norm.Basic.normSq
        (1 - Dirichlet.Window.Basic.denominatorRatio lower upper *
          Dirichlet.Window.Basic.errorRatio source.value lower upper) := by
  exact Dirichlet.Window.Basic.threshold_le_of_quadraticBoundary thresholdLtHalf
    thresholdPolynomialNonnegative
    (Dirichlet.Window.Basic.AreConsecutiveBest.normalizedDeterminantGap_boundary consecutive)

/-- Any displayed positive weights satisfying the half-square budget equation
give a certified normalized determinant gap for consecutive best pairs. -/
theorem
  AreConsecutiveBest.weightedThreshold_le_normalizedDeterminantGap
    {source : GaussianInt.Fraction} {lower upper : GaussianInt.Pair.Basic.ConvergentPair}
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest source.value lower upper)
    (leftWeight rightWeight threshold : Fraction.Rational)
    (leftWeightPositive : 0 < leftWeight)
    (rightWeightPositive : 0 < rightWeight)
    (budget :
      leftWeight * (leftWeight + rightWeight) * threshold +
          rightWeight * (leftWeight + rightWeight) * (1 / 2 : Fraction.Rational) =
        leftWeight * rightWeight) :
    threshold ≤
      Data.Gaussian.Norm.Basic.normSq
        (1 - Dirichlet.Window.Basic.denominatorRatio lower upper *
          Dirichlet.Window.Basic.errorRatio source.value lower upper) := by
  exact Dirichlet.Window.Basic.weightedThreshold_le_determinantGap _ _ leftWeight rightWeight
    threshold leftWeightPositive rightWeightPositive budget
    (Dirichlet.Window.Basic.AreConsecutiveBest.denominatorRatio_normSq_lt_one consecutive)
    (Dirichlet.Window.Basic.AreConsecutiveBest.normalizedCoefficientExterior consecutive)

/-- Consecutive best pairs have the simple universal normalized gap
`1/12`. -/
theorem
  AreConsecutiveBest.one_twelfth_le_normalizedDeterminantGap
    {source : GaussianInt.Fraction} {lower upper : GaussianInt.Pair.Basic.ConvergentPair}
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest source.value lower upper) :
    (1 / 12 : Fraction.Rational) ≤
      Data.Gaussian.Norm.Basic.normSq
        (1 - Dirichlet.Window.Basic.denominatorRatio lower upper *
          Dirichlet.Window.Basic.errorRatio source.value lower upper) := by
  exact Dirichlet.Window.Basic.AreConsecutiveBest.weightedThreshold_le_normalizedDeterminantGap consecutive
    2 1 (1 / 12) (by decide) (by decide) (by decide)

/-- Shallow displayed record for the rational threshold `35/408`. -/
def refinedGapThreshold : Fraction.Rational :=
  Data.Rat.SignedFraction.Normalization.ofFraction ⟨35, 408, by decide⟩

/-- Shallow displayed record for the reciprocal factor `408/35`. -/
def refinedIndexFactor : Fraction.Rational :=
  Data.Rat.SignedFraction.Normalization.ofFraction ⟨408, 35, by decide⟩

/-- Shallow displayed record for the universal bound `816/35`. -/
def refinedUniversalWindowBound : Fraction.Rational :=
  Data.Rat.SignedFraction.Normalization.ofFraction ⟨816, 35, by decide⟩

/-- Shallow displayed record for the sharper quadratic threshold `102/1189`. -/
def quadraticGapThreshold : Fraction.Rational :=
  Data.Rat.SignedFraction.Normalization.ofFraction ⟨102, 1189, by decide⟩

/-- Exact reciprocal `1189/102` of `quadraticGapThreshold`. -/
def quadraticIndexFactor : Fraction.Rational :=
  Data.Rat.SignedFraction.Normalization.ofFraction ⟨1189, 102, by decide⟩

/-- Universal index-two bound `1189/51` furnished by the quadratic
threshold. -/
def quadraticUniversalWindowBound : Fraction.Rational
  :=
  Data.Rat.SignedFraction.Normalization.ofFraction ⟨1189, 51, by decide⟩

/-- The rational gap threshold `35/408` is below one half. -/
theorem refinedGapThreshold_lt_half :
    Dirichlet.Window.Basic.refinedGapThreshold < (1 / 2 : Fraction.Rational) := by
  unfold Dirichlet.Window.Basic.refinedGapThreshold
  decide

/-- The threshold `35/408` has nonnegative value under the quadratic boundary polynomial. -/
theorem refinedGapThreshold_quadratic_nonnegative :
    0 ≤ Dirichlet.Window.Basic.refinedGapThreshold ^ 2 - 3 * Dirichlet.Window.Basic.refinedGapThreshold + 1 / 4 := by
  unfold Dirichlet.Window.Basic.refinedGapThreshold
  decide

/-- The rational gap threshold `102/1189` is below one half. -/
theorem quadraticGapThreshold_lt_half :
    Dirichlet.Window.Basic.quadraticGapThreshold < (1 / 2 : Fraction.Rational) := by
  unfold Dirichlet.Window.Basic.quadraticGapThreshold
  decide

/-- The threshold `102/1189` has nonnegative value under the quadratic boundary polynomial. -/
theorem quadraticGapThreshold_quadratic_nonnegative :
    0 ≤ Dirichlet.Window.Basic.quadraticGapThreshold ^ 2 - 3 * Dirichlet.Window.Basic.quadraticGapThreshold + 1 / 4 :=
      by
  unfold Dirichlet.Window.Basic.quadraticGapThreshold
  decide

attribute [local instance 2000] Purelib.Algebra.Monoid.Int.monoid in
/-- The denominator-cleared quadratic value at `102/1189` is exactly one. -/
theorem quadraticGapThreshold_integerCertificate :
    (4 * 102 ^ 2 - 12 * 102 * 1189 + 1189 ^ 2 : Int) = 1 := by
  decide

/-- The reciprocal factor `1189/102` is nonnegative. -/
theorem quadraticIndexFactor_nonneg :
    (0 : Fraction.Rational) ≤ Dirichlet.Window.Basic.quadraticIndexFactor := by
  unfold Dirichlet.Window.Basic.quadraticIndexFactor
  decide

/-- The quadratic gap threshold times its retained reciprocal factor is one. -/
theorem quadraticGapThreshold_mul_quadraticIndexFactor
  :
    Dirichlet.Window.Basic.quadraticGapThreshold * Dirichlet.Window.Basic.quadraticIndexFactor = 1 := by
  unfold Dirichlet.Window.Basic.quadraticGapThreshold Dirichlet.Window.Basic.quadraticIndexFactor
  rw [Data.Rat.SignedFraction.Arithmetic.ofFraction_mulFraction]
  calc
    _ = Data.Rat.SignedFraction.Normalization.ofFraction ⟨1, 1, by decide⟩ := by
      apply Data.Rat.SignedFraction.Normalization.ofFraction_eq_of_equivalent
      change (102 * 1189 : Int) * 1 = 1 * (1189 * 102)
      ring1
    _ = 1 := (Data.Rat.SignedFraction.Arithmetic.natCast_eq_fraction 1).symm

/-- Twice the quadratic index factor equals the universal bound `1189/51`. -/
theorem quadraticIndexFactor_mul_two :
    Dirichlet.Window.Basic.quadraticIndexFactor * 2 = Dirichlet.Window.Basic.quadraticUniversalWindowBound := by
  unfold Dirichlet.Window.Basic.quadraticIndexFactor Dirichlet.Window.Basic.quadraticUniversalWindowBound
  calc
    Data.Rat.SignedFraction.Normalization.ofFraction ⟨1189, 102, by decide⟩ * 2 =
        Data.Rat.SignedFraction.Normalization.ofFraction ⟨1189, 102, by decide⟩ *
          Data.Rat.SignedFraction.Normalization.ofFraction ⟨2, 1, by decide⟩ :=
      congrArg
        (fun value : Fraction.Rational =>
          Data.Rat.SignedFraction.Normalization.ofFraction ⟨1189, 102, by decide⟩ * value)
        (Data.Rat.SignedFraction.Arithmetic.natCast_eq_fraction 2)
    _ = Data.Rat.SignedFraction.Normalization.ofFraction
        (Data.Rat.SignedFraction.Arithmetic.mulFraction
          ⟨1189, 102, by decide⟩ ⟨2, 1, by decide⟩) :=
      Data.Rat.SignedFraction.Arithmetic.ofFraction_mulFraction _ _
    _ = Data.Rat.SignedFraction.Normalization.ofFraction ⟨1189, 51, by decide⟩ := by
      apply Data.Rat.SignedFraction.Normalization.ofFraction_eq_of_equivalent
      change (1189 * 2 : Int) * 51 = 1189 * (102 * 1)
      ring1

/-- Multiplication by 51 clears the universal bound denominator and gives 1189. -/
theorem quadraticUniversalWindowBound_mul_denominator :
    Dirichlet.Window.Basic.quadraticUniversalWindowBound * 51 = 1189 := by
  unfold Dirichlet.Window.Basic.quadraticUniversalWindowBound
  have clearance := Data.Rat.SignedFraction.Arithmetic.ofFraction_mul_den
    ({ num := 1189, den := 51, den_pos := by decide } :
      Data.Rat.SignedFraction)
  simpa only [Int.cast_ofNat] using clearance

/-- The quadratic universal bound `1189/51` is strictly smaller than `816/35`. -/
theorem
  quadraticUniversalWindowBound_lt_refinedUniversalWindowBound
  :
    Dirichlet.Window.Basic.quadraticUniversalWindowBound < Dirichlet.Window.Basic.refinedUniversalWindowBound := by
  unfold Dirichlet.Window.Basic.quadraticUniversalWindowBound Dirichlet.Window.Basic.refinedUniversalWindowBound
  decide

/-- The reciprocal factor `408/35` is nonnegative. -/
theorem refinedIndexFactor_nonneg : (0 :
  Fraction.Rational) ≤ Dirichlet.Window.Basic.refinedIndexFactor := by
  unfold Dirichlet.Window.Basic.refinedIndexFactor
  decide

/-- The refined threshold times its retained reciprocal factor is one. -/
theorem refinedGapThreshold_mul_refinedIndexFactor :
    Dirichlet.Window.Basic.refinedGapThreshold * Dirichlet.Window.Basic.refinedIndexFactor = 1 := by
  unfold Dirichlet.Window.Basic.refinedGapThreshold Dirichlet.Window.Basic.refinedIndexFactor
  rw [Data.Rat.SignedFraction.Arithmetic.ofFraction_mulFraction]
  calc
    _ = Data.Rat.SignedFraction.Normalization.ofFraction ⟨1, 1, by decide⟩ := by
      apply Data.Rat.SignedFraction.Normalization.ofFraction_eq_of_equivalent
      change (35 * 408 : Int) * 1 = 1 * (408 * 35)
      ring1
    _ = 1 := (Data.Rat.SignedFraction.Arithmetic.natCast_eq_fraction 1).symm

/-- Twice the refined index factor equals the universal bound `816/35`. -/
theorem refinedIndexFactor_mul_two :
    Dirichlet.Window.Basic.refinedIndexFactor * 2 = Dirichlet.Window.Basic.refinedUniversalWindowBound := by
  unfold Dirichlet.Window.Basic.refinedIndexFactor Dirichlet.Window.Basic.refinedUniversalWindowBound
  calc
    Data.Rat.SignedFraction.Normalization.ofFraction ⟨408, 35, by decide⟩ * 2 =
        Data.Rat.SignedFraction.Normalization.ofFraction ⟨408, 35, by decide⟩ *
          Data.Rat.SignedFraction.Normalization.ofFraction ⟨2, 1, by decide⟩ :=
      congrArg
        (fun value : Fraction.Rational =>
          Data.Rat.SignedFraction.Normalization.ofFraction ⟨408, 35, by decide⟩ * value)
        (Data.Rat.SignedFraction.Arithmetic.natCast_eq_fraction 2)
    _ = Data.Rat.SignedFraction.Normalization.ofFraction
        (Data.Rat.SignedFraction.Arithmetic.mulFraction
          ⟨408, 35, by decide⟩ ⟨2, 1, by decide⟩) :=
      Data.Rat.SignedFraction.Arithmetic.ofFraction_mulFraction _ _
    _ = Data.Rat.SignedFraction.Normalization.ofFraction ⟨816, 35, by decide⟩ := by
      apply Data.Rat.SignedFraction.Normalization.ofFraction_eq_of_equivalent
      change (408 * 2 : Int) * 35 = 816 * (35 * 1)
      ring1

/-- Multiplication by 35 clears the refined index factor denominator and gives 408. -/
theorem refinedIndexFactor_mul_denominator :
    Dirichlet.Window.Basic.refinedIndexFactor * 35 = 408 := by
  unfold Dirichlet.Window.Basic.refinedIndexFactor
  have clearance := Data.Rat.SignedFraction.Arithmetic.ofFraction_mul_den
    ({ num := 408, den := 35, den_pos := by decide } :
      Data.Rat.SignedFraction)
  simpa only [Int.cast_ofNat] using clearance

/-- Multiplication by 35 clears the refined universal bound denominator and gives 816. -/
theorem refinedUniversalWindowBound_mul_denominator :
    Dirichlet.Window.Basic.refinedUniversalWindowBound * 35 = 816 := by
  unfold Dirichlet.Window.Basic.refinedUniversalWindowBound
  have clearance := Data.Rat.SignedFraction.Arithmetic.ofFraction_mul_den
    ({ num := 816, den := 35, den_pos := by decide } :
      Data.Rat.SignedFraction)
  simpa only [Int.cast_ofNat] using clearance

/-- Multiplication by 408 clears the refined threshold denominator and gives 35. -/
theorem refinedGapThreshold_mul_denominator :
    Dirichlet.Window.Basic.refinedGapThreshold * 408 = 35 := by
  unfold Dirichlet.Window.Basic.refinedGapThreshold
  have clearance := Data.Rat.SignedFraction.Arithmetic.ofFraction_mul_den
    ({ num := 35, den := 408, den_pos := by decide } :
      Data.Rat.SignedFraction)
  simpa only [Int.cast_ofNat] using clearance

/-- The weights 12 and 5 satisfy the exact half-square budget for threshold `35/408`. -/
theorem refinedGapThreshold_budget :
    (12 : Fraction.Rational) * (12 + 5) * Dirichlet.Window.Basic.refinedGapThreshold +
          5 * (12 + 5) * (1 / 2) =
        12 * 5 := by
  have cancel2 : ((1 : Fraction.Rational) / 2) * 2 = 1 :=
    Fraction.Field.div_mul_cancel_of_ne 1 2
      (show (2 : Fraction.Rational) ≠ 0 by decide)
  apply Fraction.Field.mul_right_cancel_of_ne
    (show (2 : Fraction.Rational) ≠ 0 by decide)
  calc
    ((12 : Fraction.Rational) * (12 + 5) * Dirichlet.Window.Basic.refinedGapThreshold +
          5 * (12 + 5) * (1 / 2)) * 2 =
        Dirichlet.Window.Basic.refinedGapThreshold * 408 + ((1 / 2) * 2) * 85 := by
      ring1
    _ = 35 + ((1 / 2) * 2) * 85 :=
      congrArg (fun value : Fraction.Rational =>
        value + ((1 / 2) * 2) * 85)
        Dirichlet.Window.Basic.refinedGapThreshold_mul_denominator
    _ = 35 + 1 * 85 :=
      congrArg (fun value : Fraction.Rational => 35 + value * 85) cancel2
    _ = (12 * 5 : Fraction.Rational) * 2 := by ring1

/-- The explicit weights `12,5` sharpen the normalized consecutive gap to
the displayed rational `35/408`. -/
theorem
  AreConsecutiveBest.refinedGap_le_normalizedDeterminantGap
    {source : GaussianInt.Fraction} {lower upper : GaussianInt.Pair.Basic.ConvergentPair}
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest source.value lower upper) :
    Dirichlet.Window.Basic.refinedGapThreshold ≤
      Data.Gaussian.Norm.Basic.normSq
        (1 - Dirichlet.Window.Basic.denominatorRatio lower upper *
          Dirichlet.Window.Basic.errorRatio source.value lower upper) := by
  exact Dirichlet.Window.Basic.AreConsecutiveBest.weightedThreshold_le_normalizedDeterminantGap consecutive
    12 5 Dirichlet.Window.Basic.refinedGapThreshold (by decide) (by decide)
    Dirichlet.Window.Basic.refinedGapThreshold_budget

/-- The exact consecutive-window product times its normalized determinant
gap is the displayed coefficient-index quadrance. -/
theorem
  AreConsecutiveBest.dirichletWindow_mul_normalizedGap_eq_index
    {source : GaussianInt.Fraction} {lower upper : GaussianInt.Pair.Basic.ConvergentPair}
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest source.value lower upper) :
    Dirichlet.Window.SourceBound.dirichletWindowQuadrance source.value lower upper *
          Data.Gaussian.Norm.Basic.normSq
            (1 - Dirichlet.Window.Basic.denominatorRatio lower upper *
              Dirichlet.Window.Basic.errorRatio source.value lower upper) =
      (GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance lower upper : Fraction.Rational) := by
  have errorCancel := Dirichlet.Window.Basic.AreConsecutiveBest.errorRatio_mul_lowerError consecutive
  have denominatorCancel :=
    Dirichlet.Window.Basic.AreConsecutiveBest.denominatorRatio_mul_upperDenominator consecutive
  have factorIdentity :
      GaussianInt.toGaussian (GaussianInt.Pair.LinearCombination.coefficientDeterminant lower upper) =
        -((GaussianInt.toGaussian upper.denominator * Best.Error.error source.value lower) *
          (1 - Dirichlet.Window.Basic.denominatorRatio lower upper *
            Dirichlet.Window.Basic.errorRatio source.value lower upper)) := by
    rw [Best.Error.toGaussian_coefficientDeterminant]
    calc
      GaussianInt.toGaussian lower.denominator * Best.Error.error source.value upper -
            GaussianInt.toGaussian upper.denominator * Best.Error.error source.value lower =
          (Dirichlet.Window.Basic.denominatorRatio lower upper * GaussianInt.toGaussian upper.denominator) *
                (Dirichlet.Window.Basic.errorRatio source.value lower upper *
                  Best.Error.error source.value lower) -
            GaussianInt.toGaussian upper.denominator * Best.Error.error source.value lower := by
        rw [errorCancel, denominatorCancel]
      _ =
          -((GaussianInt.toGaussian upper.denominator * Best.Error.error source.value lower) *
            (1 - Dirichlet.Window.Basic.denominatorRatio lower upper *
              Dirichlet.Window.Basic.errorRatio source.value lower upper)) := by
        apply Gaussian.Basic.ext <;>
          simp only [Gaussian.Basic.sub_re,
            Gaussian.Basic.sub_im,
            Gaussian.Basic.mul_re,
            Gaussian.Basic.mul_im,
            Gaussian.Basic.neg_re,
            Gaussian.Basic.neg_im,
            Gaussian.Basic.one_re,
            Gaussian.Basic.one_im] <;>
          ring1
  rewrite [Dirichlet.Window.SourceBound.dirichletWindowQuadrance_eq_cast]
  unfold Best.Error.errorQuadrance Best.Error.denominatorQuadrance
  change
    ((GaussianInt.normNat upper.denominator : Fraction.Rational) *
        Data.Gaussian.Norm.Basic.normSq (Best.Error.error source.value lower)) *
          Data.Gaussian.Norm.Basic.normSq
            (1 - Dirichlet.Window.Basic.denominatorRatio lower upper *
              Dirichlet.Window.Basic.errorRatio source.value lower upper) =
      (GaussianInt.normNat (GaussianInt.Pair.LinearCombination.coefficientDeterminant lower upper) : Fraction.Rational)
  symm
  calc
    (GaussianInt.normNat (GaussianInt.Pair.LinearCombination.coefficientDeterminant lower upper) : Fraction.Rational) =
        Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian
          (GaussianInt.Pair.LinearCombination.coefficientDeterminant lower upper)) :=
      (GaussianInt.normSq_toGaussian _).symm
    _ = Data.Gaussian.Norm.Basic.normSq
        (-((GaussianInt.toGaussian upper.denominator * Best.Error.error source.value lower) *
          (1 - Dirichlet.Window.Basic.denominatorRatio lower upper *
            Dirichlet.Window.Basic.errorRatio source.value lower upper))) :=
      congrArg Data.Gaussian.Norm.Basic.normSq factorIdentity
    _ =
        ((GaussianInt.normNat upper.denominator : Fraction.Rational) *
          Data.Gaussian.Norm.Basic.normSq (Best.Error.error source.value lower)) *
            Data.Gaussian.Norm.Basic.normSq
              (1 - Dirichlet.Window.Basic.denominatorRatio lower upper *
                Dirichlet.Window.Basic.errorRatio source.value lower upper) := by
      rw [Gaussian.Norm.Basic.normSq_neg, Gaussian.Norm.Basic.normSq_mul, Gaussian.Norm.Basic.normSq_mul,
        GaussianInt.normSq_toGaussian]

/-- Any certified normalized gap gives a division-free upper constraint on
the exact consecutive-window product. -/
theorem
  AreConsecutiveBest.threshold_mul_dirichletWindow_le_index
    {source : GaussianInt.Fraction} {lower upper : GaussianInt.Pair.Basic.ConvergentPair}
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest source.value lower upper)
    (threshold : Fraction.Rational)
    (gapLower : threshold ≤
      Data.Gaussian.Norm.Basic.normSq
        (1 - Dirichlet.Window.Basic.denominatorRatio lower upper *
          Dirichlet.Window.Basic.errorRatio source.value lower upper)) :
    threshold * Dirichlet.Window.SourceBound.dirichletWindowQuadrance source.value lower upper ≤
      (GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance lower upper : Fraction.Rational) := by
  have windowNonnegative :
      0 ≤ Dirichlet.Window.SourceBound.dirichletWindowQuadrance source.value lower upper := by
    rewrite [Dirichlet.Window.SourceBound.dirichletWindowQuadrance_eq_cast]
    exact Fraction.Order.Arithmetic.mul_nonneg_direct
      (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _))
      (Gaussian.Norm.Basic.normSq_nonneg (Best.Error.error source.value lower))
  calc
    threshold * Dirichlet.Window.SourceBound.dirichletWindowQuadrance source.value lower upper =
        Dirichlet.Window.SourceBound.dirichletWindowQuadrance source.value lower upper * threshold := by
      ring1
    _ ≤ Dirichlet.Window.SourceBound.dirichletWindowQuadrance source.value lower upper *
          Data.Gaussian.Norm.Basic.normSq
            (1 - Dirichlet.Window.Basic.denominatorRatio lower upper *
              Dirichlet.Window.Basic.errorRatio source.value lower upper) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct gapLower
        windowNonnegative
    _ = (GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance lower upper : Fraction.Rational) :=
      Dirichlet.Window.Basic.AreConsecutiveBest.dirichletWindow_mul_normalizedGap_eq_index consecutive

/-- A displayed rational passing the quadratic boundary test gives a direct
division-free consecutive-window bound. -/
theorem
  AreConsecutiveBest.quadraticThreshold_mul_dirichletWindow_le_index
    {source : GaussianInt.Fraction} {lower upper : GaussianInt.Pair.Basic.ConvergentPair}
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest source.value lower upper)
    (threshold : Fraction.Rational)
    (thresholdLtHalf : threshold < (1 / 2 : Fraction.Rational))
    (thresholdPolynomialNonnegative :
      0 ≤ threshold ^ 2 - 3 * threshold + 1 / 4) :
    threshold * Dirichlet.Window.SourceBound.dirichletWindowQuadrance source.value lower upper ≤
      (GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance lower upper : Fraction.Rational) := by
  exact Dirichlet.Window.Basic.AreConsecutiveBest.threshold_mul_dirichletWindow_le_index consecutive threshold
    (Dirichlet.Window.Basic.AreConsecutiveBest.threshold_le_normalizedDeterminantGap_of_quadratic consecutive threshold
      thresholdLtHalf thresholdPolynomialNonnegative)

/-- The coefficient-index dichotomy turns every passing quadratic threshold
into the universal division-free bound `threshold * window ≤ 2`. -/
theorem
  AreConsecutiveBest.quadraticThreshold_mul_dirichletWindow_le_two
    {source : GaussianInt.Fraction} {lower upper : GaussianInt.Pair.Basic.ConvergentPair}
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest source.value lower upper)
    (threshold : Fraction.Rational)
    (thresholdLtHalf : threshold < (1 / 2 : Fraction.Rational))
    (thresholdPolynomialNonnegative :
      0 ≤ threshold ^ 2 - 3 * threshold + 1 / 4) :
    threshold * Dirichlet.Window.SourceBound.dirichletWindowQuadrance source.value lower upper ≤ 2 := by
  have indexBound : GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance lower upper ≤ 2 :=
    (Best.Consecutive.Index.AreConsecutiveBest.coefficientIndexQuadrance_le_two consecutive)
  have castIndexBound :
      (GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance lower upper : Fraction.Rational) ≤ 2 :=
    Fraction.Cast.Order.natCast_le_direct indexBound
  exact (Dirichlet.Window.Basic.AreConsecutiveBest.quadraticThreshold_mul_dirichletWindow_le_index consecutive threshold
    thresholdLtHalf thresholdPolynomialNonnegative).trans castIndexBound

/-- Turn any quadratic-certified rational threshold and displayed reciprocal
factor into an unscaled window bound. -/
theorem
  AreConsecutiveBest.dirichletWindowQuadrance_le_factor_mul_index_of_quadraticThreshold
    {source : GaussianInt.Fraction} {lower upper : GaussianInt.Pair.Basic.ConvergentPair}
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest source.value lower upper)
    (threshold factor : Fraction.Rational)
    (thresholdLtHalf : threshold < (1 / 2 : Fraction.Rational))
    (thresholdPolynomialNonnegative :
      0 ≤ threshold ^ 2 - 3 * threshold + 1 / 4)
    (thresholdMulFactor : threshold * factor = 1)
    (factorNonnegative : 0 ≤ factor) :
    Dirichlet.Window.SourceBound.dirichletWindowQuadrance source.value lower upper ≤
      factor * (GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance lower upper : Fraction.Rational) := by
  have thresholdBound :=
    Dirichlet.Window.Basic.AreConsecutiveBest.quadraticThreshold_mul_dirichletWindow_le_index consecutive threshold
      thresholdLtHalf thresholdPolynomialNonnegative
  have scaledBound :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      thresholdBound factorNonnegative
  calc
    Dirichlet.Window.SourceBound.dirichletWindowQuadrance source.value lower upper =
        (threshold *
          Dirichlet.Window.SourceBound.dirichletWindowQuadrance source.value lower upper) * factor := by
      calc
        Dirichlet.Window.SourceBound.dirichletWindowQuadrance source.value lower upper =
            1 * Dirichlet.Window.SourceBound.dirichletWindowQuadrance source.value lower upper := by
          ring1
        _ = (threshold * factor) *
            Dirichlet.Window.SourceBound.dirichletWindowQuadrance source.value lower upper := by
          rw [thresholdMulFactor]
        _ = (threshold *
            Dirichlet.Window.SourceBound.dirichletWindowQuadrance source.value lower upper) * factor := by
          ring1
    _ ≤ (GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance lower upper : Fraction.Rational) * factor :=
      scaledBound
    _ = factor *
        (GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance lower upper : Fraction.Rational) := by
      ring1

/-- Universal index-two consequence of a quadratic-certified threshold and
its displayed reciprocal factor. -/
theorem
  AreConsecutiveBest.dirichletWindowQuadrance_le_factor_mul_two_of_quadraticThreshold
    {source : GaussianInt.Fraction} {lower upper : GaussianInt.Pair.Basic.ConvergentPair}
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest source.value lower upper)
    (threshold factor : Fraction.Rational)
    (thresholdLtHalf : threshold < (1 / 2 : Fraction.Rational))
    (thresholdPolynomialNonnegative :
      0 ≤ threshold ^ 2 - 3 * threshold + 1 / 4)
    (thresholdMulFactor : threshold * factor = 1)
    (factorNonnegative : 0 ≤ factor) :
    Dirichlet.Window.SourceBound.dirichletWindowQuadrance source.value lower upper ≤ factor * 2 := by
  have indexBound : GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance lower upper ≤ 2 :=
    (Best.Consecutive.Index.AreConsecutiveBest.coefficientIndexQuadrance_le_two consecutive)
  have castIndexBound :
      (GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance lower upper : Fraction.Rational) ≤ 2 :=
    Fraction.Cast.Order.natCast_le_direct indexBound
  have scaledIndexBound :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct castIndexBound
      factorNonnegative
  exact
    (Dirichlet.Window.Basic.AreConsecutiveBest.dirichletWindowQuadrance_le_factor_mul_index_of_quadraticThreshold
      consecutive threshold factor thresholdLtHalf
        thresholdPolynomialNonnegative thresholdMulFactor factorNonnegative).trans
      scaledIndexBound

/-- The refined `12,5` certificate bounds a consecutive squared window by
`408/35` times its coefficient-index quadrance. -/
theorem
  AreConsecutiveBest.dirichletWindowQuadrance_le_refinedIndexFactor
    {source : GaussianInt.Fraction} {lower upper : GaussianInt.Pair.Basic.ConvergentPair}
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest source.value lower upper) :
    Dirichlet.Window.SourceBound.dirichletWindowQuadrance source.value lower upper ≤
      Dirichlet.Window.Basic.refinedIndexFactor *
        (GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance lower upper : Fraction.Rational) := by
  exact
    Dirichlet.Window.Basic.AreConsecutiveBest.dirichletWindowQuadrance_le_factor_mul_index_of_quadraticThreshold
      consecutive Dirichlet.Window.Basic.refinedGapThreshold Dirichlet.Window.Basic.refinedIndexFactor
        Dirichlet.Window.Basic.refinedGapThreshold_lt_half
        Dirichlet.Window.Basic.refinedGapThreshold_quadratic_nonnegative
        Dirichlet.Window.Basic.refinedGapThreshold_mul_refinedIndexFactor
          Dirichlet.Window.Basic.refinedIndexFactor_nonneg

/-- Refined universal source-independent bound `816/35` for every
consecutive squared Dirichlet-window product. -/
theorem
  AreConsecutiveBest.dirichletWindowQuadrance_le_refinedUniversalBound
    {source : GaussianInt.Fraction} {lower upper : GaussianInt.Pair.Basic.ConvergentPair}
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest source.value lower upper) :
    Dirichlet.Window.SourceBound.dirichletWindowQuadrance source.value lower upper ≤
      Dirichlet.Window.Basic.refinedUniversalWindowBound := by
  have indexBound : GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance lower upper ≤ 2 :=
    (Best.Consecutive.Index.AreConsecutiveBest.coefficientIndexQuadrance_le_two consecutive)
  have castIndexBound :
      (GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance lower upper : Fraction.Rational) ≤ 2 :=
    Fraction.Cast.Order.natCast_le_direct indexBound
  have scaledIndexBound :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct castIndexBound
      Dirichlet.Window.Basic.refinedIndexFactor_nonneg
  calc
    Dirichlet.Window.SourceBound.dirichletWindowQuadrance source.value lower upper ≤
        Dirichlet.Window.Basic.refinedIndexFactor *
          (GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance lower upper : Fraction.Rational) :=
      Dirichlet.Window.Basic.AreConsecutiveBest.dirichletWindowQuadrance_le_refinedIndexFactor consecutive
    _ ≤ Dirichlet.Window.Basic.refinedIndexFactor * 2 := scaledIndexBound
    _ = Dirichlet.Window.Basic.refinedUniversalWindowBound := Dirichlet.Window.Basic.refinedIndexFactor_mul_two

/-- The quadratic certificate `102/1189` bounds a consecutive squared window
by `1189/102` times its coefficient-index quadrance. -/
theorem
  AreConsecutiveBest.dirichletWindowQuadrance_le_quadraticIndexFactor
    {source : GaussianInt.Fraction} {lower upper : GaussianInt.Pair.Basic.ConvergentPair}
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest source.value lower upper) :
    Dirichlet.Window.SourceBound.dirichletWindowQuadrance source.value lower upper ≤
      Dirichlet.Window.Basic.quadraticIndexFactor *
        (GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance lower upper : Fraction.Rational) :=
  Dirichlet.Window.Basic.AreConsecutiveBest.dirichletWindowQuadrance_le_factor_mul_index_of_quadraticThreshold
    consecutive Dirichlet.Window.Basic.quadraticGapThreshold Dirichlet.Window.Basic.quadraticIndexFactor
      Dirichlet.Window.Basic.quadraticGapThreshold_lt_half
      Dirichlet.Window.Basic.quadraticGapThreshold_quadratic_nonnegative
      Dirichlet.Window.Basic.quadraticGapThreshold_mul_quadraticIndexFactor
      Dirichlet.Window.Basic.quadraticIndexFactor_nonneg

/-- Sharper universal source-independent bound `1189/51` for every
consecutive squared Dirichlet-window product. -/
theorem
  AreConsecutiveBest.dirichletWindowQuadrance_le_quadraticUniversalBound
    {source : GaussianInt.Fraction} {lower upper : GaussianInt.Pair.Basic.ConvergentPair}
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest source.value lower upper) :
    Dirichlet.Window.SourceBound.dirichletWindowQuadrance source.value lower upper ≤
      Dirichlet.Window.Basic.quadraticUniversalWindowBound := by
  calc
    Dirichlet.Window.SourceBound.dirichletWindowQuadrance source.value lower upper ≤
        Dirichlet.Window.Basic.quadraticIndexFactor * 2 :=
      Dirichlet.Window.Basic.AreConsecutiveBest.dirichletWindowQuadrance_le_factor_mul_two_of_quadraticThreshold
        consecutive Dirichlet.Window.Basic.quadraticGapThreshold Dirichlet.Window.Basic.quadraticIndexFactor
          Dirichlet.Window.Basic.quadraticGapThreshold_lt_half
          Dirichlet.Window.Basic.quadraticGapThreshold_quadratic_nonnegative
          Dirichlet.Window.Basic.quadraticGapThreshold_mul_quadraticIndexFactor
          Dirichlet.Window.Basic.quadraticIndexFactor_nonneg
    _ = Dirichlet.Window.Basic.quadraticUniversalWindowBound := Dirichlet.Window.Basic.quadraticIndexFactor_mul_two

/-- The squared Dirichlet-window product is at most twelve times the
coefficient-index quadrance. -/
theorem
  AreConsecutiveBest.dirichletWindowQuadrance_le_twelve_mul_index
    {source : GaussianInt.Fraction} {lower upper : GaussianInt.Pair.Basic.ConvergentPair}
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest source.value lower upper) :
    Dirichlet.Window.SourceBound.dirichletWindowQuadrance source.value lower upper ≤
      12 * (GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance lower upper : Fraction.Rational) := by
  let window := Dirichlet.Window.SourceBound.dirichletWindowQuadrance source.value lower upper
  let gap := Data.Gaussian.Norm.Basic.normSq
    (1 - Dirichlet.Window.Basic.denominatorRatio lower upper *
      Dirichlet.Window.Basic.errorRatio source.value lower upper)
  have windowNonnegative : 0 ≤ window := by
    dsimp only [window]
    rewrite [Dirichlet.Window.SourceBound.dirichletWindowQuadrance_eq_cast]
    exact Fraction.Order.Arithmetic.mul_nonneg_direct
      (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _))
      (Gaussian.Norm.Basic.normSq_nonneg (Best.Error.error source.value lower))
  have gapLower : (1 / 12 : Fraction.Rational) ≤ gap := by
    dsimp only [gap]
    exact Dirichlet.Window.Basic.AreConsecutiveBest.one_twelfth_le_normalizedDeterminantGap consecutive
  have productIdentity :
      window * gap =
        (GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance lower upper : Fraction.Rational) := by
    dsimp only [window, gap]
    exact Dirichlet.Window.Basic.AreConsecutiveBest.dirichletWindow_mul_normalizedGap_eq_index consecutive
  have dividedBound :
      window * (1 / 12 : Fraction.Rational) ≤
        (GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance lower upper : Fraction.Rational) := by
    calc
      window * (1 / 12 : Fraction.Rational) ≤ window * gap :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct gapLower
          windowNonnegative
      _ = (GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance lower upper : Fraction.Rational) :=
        productIdentity
  have scaledBound :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct dividedBound
      (show (0 : Fraction.Rational) ≤ 12 by decide)
  have twelfthCancel :
      (1 / 12 : Fraction.Rational) * 12 = 1 :=
    Fraction.Field.div_mul_cancel_of_ne 1 12 (by decide)
  calc
    window = (window * (1 / 12 : Fraction.Rational)) * 12 := by
      rw [Fraction.Field.mul_assoc, twelfthCancel]
      ring1
    _ ≤ (GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance lower upper : Fraction.Rational) * 12 :=
      scaledBound
    _ = 12 * (GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance lower upper : Fraction.Rational) := by
      ring1

/-- Universal source-independent upper bound for every consecutive squared
Dirichlet-window product.  The constant `24` is a first constructive
rational bound, not the optimal completed-complex constant. -/
theorem
  AreConsecutiveBest.dirichletWindowQuadrance_le_twentyFour
    {source : GaussianInt.Fraction} {lower upper : GaussianInt.Pair.Basic.ConvergentPair}
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest source.value lower upper) :
    Dirichlet.Window.SourceBound.dirichletWindowQuadrance source.value lower upper ≤ 24 := by
  have indexBound : GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance lower upper ≤ 2 :=
    (Best.Consecutive.Index.AreConsecutiveBest.coefficientIndexQuadrance_le_two consecutive)
  have castIndexBound :
      (GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance lower upper : Fraction.Rational) ≤ 2 :=
    Fraction.Cast.Order.natCast_le_direct indexBound
  have scaledIndexBound :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct castIndexBound
      (show (0 : Fraction.Rational) ≤ 12 by decide)
  calc
    Dirichlet.Window.SourceBound.dirichletWindowQuadrance source.value lower upper ≤
        12 * (GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance lower upper : Fraction.Rational) :=
      Dirichlet.Window.Basic.AreConsecutiveBest.dirichletWindowQuadrance_le_twelve_mul_index consecutive
    _ ≤ 12 * (2 : Fraction.Rational) := scaledIndexBound
    _ = 24 := by ring1

end Purelib.NumberTheory.Approximation.Dirichlet.Window.Basic

end
