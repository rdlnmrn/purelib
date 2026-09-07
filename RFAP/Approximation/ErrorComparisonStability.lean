import mathlib.Tactic.QuotientFreeOmega
import mathlib.Tactic.QuotientFreeRing
import RFAP.Approximation.DirichletWindow

/-!
# Explicit rational stability of a strict error comparison

A strict comparison between two displayed approximation errors has rational
clearance.  A computed natural weight turns the two weighted quadrance
inequalities into an explicit positive squared-distance budget preserving
that comparison.  This is a wholly finite substitute for an appeal to
continuity or openness.
-/

namespace RFAP.ErrorComparisonStability

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Pair := RFAP.HurwitzRational.ConvergentPair

open RFAP.BestApproximation
open RFAP.ConstructiveGaussianHeight.GaussianInt

def comparisonClearance
    (center : Gaussian) (reference contender : Pair) : Coordinate :=
  errorQuadrance center contender - errorQuadrance center reference

theorem comparisonClearance_pos
    {center : Gaussian} {reference contender : Pair}
    (strict : errorQuadrance center reference <
      errorQuadrance center contender) :
    0 < comparisonClearance center reference contender := by
  exact RFAP.ConstructiveFraction.sub_pos_direct strict

/-- A finite weight large enough to absorb the multiplicative slack in both
weighted quadrance estimates. -/
def comparisonWeightNat
    (center : Gaussian) (reference contender : Pair) : Nat :=
  RFAP.ConstructiveFraction.ceilNat
      (4 * (errorQuadrance center reference + 1) /
        comparisonClearance center reference contender) + 1

def comparisonWeight
    (center : Gaussian) (reference contender : Pair) : Coordinate :=
  (comparisonWeightNat center reference contender : Coordinate)

theorem comparisonWeight_pos
    (center : Gaussian) (reference contender : Pair) :
    0 < comparisonWeight center reference contender := by
  apply RFAP.ConstructiveFraction.natCast_pos_direct
  unfold comparisonWeightNat
  exact Nat.zero_lt_succ _

theorem one_le_comparisonWeight
    (center : Gaussian) (reference contender : Pair) :
    (1 : Coordinate) ≤ comparisonWeight center reference contender := by
  unfold comparisonWeight
  change ((1 : Nat) : Coordinate) ≤
    (comparisonWeightNat center reference contender : Coordinate)
  apply RFAP.ConstructiveFraction.natCast_le_direct
  unfold comparisonWeightNat
  exact Nat.succ_le_succ (Nat.zero_le _)

private theorem four_reference_lt_weight_mul_clearance
    {center : Gaussian} {reference contender : Pair}
    (strict : errorQuadrance center reference <
      errorQuadrance center contender) :
    4 * (errorQuadrance center reference + 1) <
      comparisonWeight center reference contender *
        comparisonClearance center reference contender := by
  have clearancePositive := comparisonClearance_pos strict
  have numeratorNonnegative :
      (0 : Coordinate) ≤ 4 * (errorQuadrance center reference + 1) :=
    RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
      (add_nonneg
        (RFAP.ConstructiveGaussian.Gaussian.normSq_nonneg _)
        (by decide))
  have ratioNonnegative :
      (0 : Coordinate) ≤
        4 * (errorQuadrance center reference + 1) /
          comparisonClearance center reference contender :=
    RFAP.ConstructiveFraction.div_nonneg_direct numeratorNonnegative
      clearancePositive.le
  have ratioLeCeiling :
      4 * (errorQuadrance center reference + 1) /
          comparisonClearance center reference contender ≤
        (RFAP.ConstructiveFraction.ceilNat
          (4 * (errorQuadrance center reference + 1) /
            comparisonClearance center reference contender) : Coordinate) :=
    RFAP.ConstructiveFraction.le_natCast_ceilNat_of_nonneg ratioNonnegative
  have ceilingLtWeight :
      (RFAP.ConstructiveFraction.ceilNat
          (4 * (errorQuadrance center reference + 1) /
            comparisonClearance center reference contender) : Coordinate) <
        comparisonWeight center reference contender := by
    unfold comparisonWeight
    apply RFAP.ConstructiveFraction.natCast_lt_direct
    unfold comparisonWeightNat
    exact Nat.lt_add_one_iff.mpr (Nat.le_refl _)
  have ratioLtWeight := ratioLeCeiling.trans_lt ceilingLtWeight
  exact (RFAP.ConstructiveFraction.div_lt_iff_pos clearancePositive).1
    ratioLtWeight

/-- Positive strictness left after compensating for the two weighted
quadrance normalizations. -/
def comparisonMargin
    (center : Gaussian) (reference contender : Pair) : Coordinate :=
  comparisonWeight center reference contender ^ 2 *
      errorQuadrance center contender -
    (1 + comparisonWeight center reference contender) ^ 2 *
      errorQuadrance center reference

theorem comparisonMargin_pos
    {center : Gaussian} {reference contender : Pair}
    (strict : errorQuadrance center reference <
      errorQuadrance center contender) :
    0 < comparisonMargin center reference contender := by
  let referenceNorm := errorQuadrance center reference
  let contenderNorm := errorQuadrance center contender
  let clearance := comparisonClearance center reference contender
  let weight := comparisonWeight center reference contender
  have referenceNonnegative : 0 ≤ referenceNorm :=
    RFAP.ConstructiveGaussian.Gaussian.normSq_nonneg _
  have weightPositive : 0 < weight := by
    simpa only [weight] using
      comparisonWeight_pos center reference contender
  have oneLeWeight : (1 : Coordinate) ≤ weight := by
    simpa only [weight] using
      one_le_comparisonWeight center reference contender
  have oneLeTwoWeight : (1 : Coordinate) ≤ 2 * weight := by
    calc
      (1 : Coordinate) ≤ weight := oneLeWeight
      _ = 1 * weight := by ring1
      _ ≤ 2 * weight :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
          (by decide) weightPositive.le
  have twoWeightMinusOneNonnegative : 0 ≤ 2 * weight - 1 :=
    RFAP.ConstructiveFraction.sub_nonneg_direct oneLeTwoWeight
  have shortGapPositive :
      0 < (2 * weight - 1) * referenceNorm + 4 * weight := by
    exact add_pos_of_nonneg_of_pos
      (RFAP.ConstructiveFraction.mul_nonneg_direct
        twoWeightMinusOneNonnegative referenceNonnegative)
      (RFAP.ConstructiveFraction.mul_pos_direct (by decide) weightPositive)
  have shortBound :
      (2 * weight + 1) * referenceNorm <
        4 * weight * (referenceNorm + 1) := by
    apply RFAP.ConstructiveFraction.lt_of_sub_pos_direct
    calc
      (0 : Coordinate) <
          (2 * weight - 1) * referenceNorm + 4 * weight :=
        shortGapPositive
      _ = 4 * weight * (referenceNorm + 1) -
          (2 * weight + 1) * referenceNorm := by ring1
  have weightedClearance :
      4 * weight * (referenceNorm + 1) < weight ^ 2 * clearance := by
    have scaled :=
      RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct weightPositive
        (show 4 * (referenceNorm + 1) < weight * clearance by
          simpa only [referenceNorm, clearance, weight] using
            four_reference_lt_weight_mul_clearance strict)
    calc
      4 * weight * (referenceNorm + 1) =
          weight * (4 * (referenceNorm + 1)) := by ring1
      _ < weight * (weight * clearance) := scaled
      _ = weight ^ 2 * clearance := by ring1
  have baselineStrict :
      (1 + weight) ^ 2 * referenceNorm <
        weight ^ 2 * contenderNorm := by
    calc
      (1 + weight) ^ 2 * referenceNorm =
          weight ^ 2 * referenceNorm +
            (2 * weight + 1) * referenceNorm := by ring1
      _ < weight ^ 2 * referenceNorm + weight ^ 2 * clearance :=
        RFAP.ConstructiveFraction.add_lt_add_left_direct
          (shortBound.trans weightedClearance) _
      _ = weight ^ 2 * contenderNorm := by
        dsimp only [clearance, comparisonClearance, referenceNorm,
          contenderNorm]
        ring1
  unfold comparisonMargin
  simpa only [referenceNorm, contenderNorm, weight] using
    RFAP.ConstructiveFraction.sub_pos_direct baselineStrict

/-- Coefficient converting squared source displacement into the two
weighted perturbation losses. -/
def comparisonCoefficient
    (center : Gaussian) (reference contender : Pair) : Coordinate :=
  let weight := comparisonWeight center reference contender
  weight * (1 + weight) ^ 2 *
      (denominatorQuadrance reference : Coordinate) +
    weight ^ 2 * (1 + weight) *
      (denominatorQuadrance contender : Coordinate)

theorem comparisonCoefficient_nonneg
    (center : Gaussian) (reference contender : Pair) :
    0 ≤ comparisonCoefficient center reference contender := by
  let weight := comparisonWeight center reference contender
  have weightNonnegative : 0 ≤ weight :=
    (comparisonWeight_pos center reference contender).le
  have onePlusWeightNonnegative : 0 ≤ 1 + weight :=
    add_nonneg (by decide) weightNonnegative
  unfold comparisonCoefficient
  dsimp only [weight]
  exact add_nonneg
    (RFAP.ConstructiveFraction.mul_nonneg_direct
      (RFAP.ConstructiveFraction.mul_nonneg_direct weightNonnegative
        (RFAP.ConstructiveFraction.pow_nonneg_direct
          onePlusWeightNonnegative 2))
      (RFAP.ConstructiveFraction.natCast_le_direct (Nat.zero_le _)))
    (RFAP.ConstructiveFraction.mul_nonneg_direct
      (RFAP.ConstructiveFraction.mul_nonneg_direct
        (RFAP.ConstructiveFraction.pow_nonneg_direct weightNonnegative 2)
        onePlusWeightNonnegative)
      (RFAP.ConstructiveFraction.natCast_le_direct (Nat.zero_le _)))

/-- Explicit positive squared-distance budget preserving one strict rational
error comparison. -/
def comparisonDistanceSq
    (center : Gaussian) (reference contender : Pair) : Coordinate :=
  comparisonMargin center reference contender /
    (1 + comparisonCoefficient center reference contender)

theorem comparisonDistanceSq_pos
    {center : Gaussian} {reference contender : Pair}
    (strict : errorQuadrance center reference <
      errorQuadrance center contender) :
    0 < comparisonDistanceSq center reference contender := by
  unfold comparisonDistanceSq
  exact RFAP.ConstructiveFraction.div_pos_direct
    (comparisonMargin_pos strict)
    ((show (0 : Coordinate) < 1 by decide).trans_le
      (le_add_of_nonneg_right
        (comparisonCoefficient_nonneg center reference contender)))

private theorem error_perturbation_identity
    (center sample : Gaussian) (pair : Pair) :
    RFAP.HurwitzApproximation.error sample pair =
      RFAP.HurwitzApproximation.error center pair +
        (sample - center) * toGaussian pair.denominator := by
  unfold RFAP.HurwitzApproximation.error
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
      RFAP.ConstructiveGaussian.Gaussian.sub_im,
      RFAP.ConstructiveGaussian.Gaussian.add_re,
      RFAP.ConstructiveGaussian.Gaussian.add_im,
      RFAP.ConstructiveGaussian.Gaussian.mul_re,
      RFAP.ConstructiveGaussian.Gaussian.mul_im] <;>
    ring1

private theorem exact_error_sum_identity
    (center sample : Gaussian) (pair : Pair) :
    RFAP.HurwitzApproximation.error sample pair +
        -((sample - center) * toGaussian pair.denominator) =
      RFAP.HurwitzApproximation.error center pair := by
  rw [error_perturbation_identity]
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [RFAP.ConstructiveGaussian.Gaussian.add_re,
      RFAP.ConstructiveGaussian.Gaussian.add_im,
      RFAP.ConstructiveGaussian.Gaussian.neg_re,
      RFAP.ConstructiveGaussian.Gaussian.neg_im] <;>
    ring1

private theorem perturbation_normSq
    (center sample : Gaussian) (pair : Pair) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        ((sample - center) * toGaussian pair.denominator) =
      RFAP.ConstructiveGaussian.Gaussian.normSq (sample - center) *
        (denominatorQuadrance pair : Coordinate) := by
  rw [RFAP.ConstructiveGaussian.Gaussian.normSq_mul, normSq_toGaussian]
  rfl

/-- Every source inside the computed rational squared-distance budget retains
the supplied strict error comparison. -/
theorem errorQuadrance_lt_of_distance
    {center sample : Gaussian} {reference contender : Pair}
    (_strict : errorQuadrance center reference <
      errorQuadrance center contender)
    (distanceSmall :
      RFAP.ConstructiveGaussian.Gaussian.normSq (sample - center) <
        comparisonDistanceSq center reference contender) :
    errorQuadrance sample reference < errorQuadrance sample contender := by
  let weight := comparisonWeight center reference contender
  let referenceExact := RFAP.HurwitzApproximation.error center reference
  let contenderExact := RFAP.HurwitzApproximation.error center contender
  let referenceSample := RFAP.HurwitzApproximation.error sample reference
  let contenderSample := RFAP.HurwitzApproximation.error sample contender
  let referencePerturbation :=
    (sample - center) * toGaussian reference.denominator
  let contenderPerturbation :=
    (sample - center) * toGaussian contender.denominator
  let distance :=
    RFAP.ConstructiveGaussian.Gaussian.normSq (sample - center)
  let coefficient := comparisonCoefficient center reference contender
  let margin := comparisonMargin center reference contender
  let referenceLoss :=
    weight * (1 + weight) ^ 2 *
      RFAP.ConstructiveGaussian.Gaussian.normSq referencePerturbation
  let contenderLoss :=
    weight ^ 2 * (1 + weight) *
      RFAP.ConstructiveGaussian.Gaussian.normSq contenderPerturbation
  have weightPositive : 0 < weight := by
    simpa only [weight] using
      comparisonWeight_pos center reference contender
  have onePlusWeightPositive : 0 < 1 + weight :=
    (show (0 : Coordinate) < 1 by decide).trans_le
      (le_add_of_nonneg_right weightPositive.le)
  have coefficientNonnegative : 0 ≤ coefficient := by
    simpa only [coefficient] using
      comparisonCoefficient_nonneg center reference contender
  have lossIdentity :
      referenceLoss + contenderLoss = coefficient * distance := by
    dsimp only [referenceLoss, contenderLoss]
    rw [show RFAP.ConstructiveGaussian.Gaussian.normSq referencePerturbation =
          distance * (denominatorQuadrance reference : Coordinate) by
        dsimp only [referencePerturbation, distance]
        exact perturbation_normSq center sample reference,
      show RFAP.ConstructiveGaussian.Gaussian.normSq contenderPerturbation =
          distance * (denominatorQuadrance contender : Coordinate) by
        dsimp only [contenderPerturbation, distance]
        exact perturbation_normSq center sample contender]
    dsimp only [coefficient, distance, comparisonCoefficient, weight]
    ring1
  have lossLtMargin : referenceLoss + contenderLoss < margin := by
    have denominatorPositive : 0 < 1 + coefficient :=
      (show (0 : Coordinate) < 1 by decide).trans_le
        (le_add_of_nonneg_right coefficientNonnegative)
    have scaledDistance :=
      (RFAP.ConstructiveFraction.lt_div_iff_pos denominatorPositive).1
        (show distance < margin / (1 + coefficient) by
          simpa only [distance, margin, coefficient, comparisonDistanceSq]
            using distanceSmall)
    rw [lossIdentity]
    calc
      coefficient * distance ≤ (1 + coefficient) * distance :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
          (le_add_of_nonneg_left (by decide))
          (RFAP.ConstructiveGaussian.Gaussian.normSq_nonneg _)
      _ = distance * (1 + coefficient) := by ring1
      _ < margin := scaledDistance
  have weightedReference := RFAP.DirichletWindow.weighted_normSq_add_le
    referenceExact referencePerturbation 1 weight
  have referenceBound :
      weight * (1 + weight) *
          RFAP.ConstructiveGaussian.Gaussian.normSq referenceSample ≤
        (1 + weight) ^ 2 *
            RFAP.ConstructiveGaussian.Gaussian.normSq referenceExact +
          referenceLoss := by
    rw [← error_perturbation_identity center sample reference] at weightedReference
    have scaled :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        weightedReference onePlusWeightPositive.le
    dsimp only [referenceLoss]
    calc
      weight * (1 + weight) *
          RFAP.ConstructiveGaussian.Gaussian.normSq referenceSample =
        (1 + weight) *
          (1 * weight *
            RFAP.ConstructiveGaussian.Gaussian.normSq referenceSample) := by
          ring1
      _ ≤ (1 + weight) *
          (1 * (1 + weight) *
              RFAP.ConstructiveGaussian.Gaussian.normSq referenceExact +
            weight * (1 + weight) *
              RFAP.ConstructiveGaussian.Gaussian.normSq
                referencePerturbation) := scaled
      _ = (1 + weight) ^ 2 *
            RFAP.ConstructiveGaussian.Gaussian.normSq referenceExact +
          weight * (1 + weight) ^ 2 *
            RFAP.ConstructiveGaussian.Gaussian.normSq
              referencePerturbation := by ring1
  have weightedContender := RFAP.DirichletWindow.weighted_normSq_add_le
    contenderSample (-contenderPerturbation) 1 weight
  have contenderBound :
      weight ^ 2 *
          RFAP.ConstructiveGaussian.Gaussian.normSq contenderExact ≤
        weight * (1 + weight) *
            RFAP.ConstructiveGaussian.Gaussian.normSq contenderSample +
          contenderLoss := by
    rw [exact_error_sum_identity center sample contender,
      RFAP.ConstructiveGaussian.Gaussian.normSq_neg] at weightedContender
    have scaled :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        weightedContender weightPositive.le
    dsimp only [contenderLoss]
    calc
      weight ^ 2 *
          RFAP.ConstructiveGaussian.Gaussian.normSq contenderExact =
        weight *
          (1 * weight *
            RFAP.ConstructiveGaussian.Gaussian.normSq contenderExact) := by
          ring1
      _ ≤ weight *
          (1 * (1 + weight) *
              RFAP.ConstructiveGaussian.Gaussian.normSq contenderSample +
            weight * (1 + weight) *
              RFAP.ConstructiveGaussian.Gaussian.normSq
                contenderPerturbation) := scaled
      _ = weight * (1 + weight) *
            RFAP.ConstructiveGaussian.Gaussian.normSq contenderSample +
          weight ^ 2 * (1 + weight) *
            RFAP.ConstructiveGaussian.Gaussian.normSq
              contenderPerturbation := by ring1
  have referenceWithContenderLoss :
      weight * (1 + weight) *
            RFAP.ConstructiveGaussian.Gaussian.normSq referenceSample +
          contenderLoss <
        weight ^ 2 *
          RFAP.ConstructiveGaussian.Gaussian.normSq contenderExact := by
    calc
      weight * (1 + weight) *
            RFAP.ConstructiveGaussian.Gaussian.normSq referenceSample +
          contenderLoss ≤
        ((1 + weight) ^ 2 *
            RFAP.ConstructiveGaussian.Gaussian.normSq referenceExact +
          referenceLoss) + contenderLoss :=
        RFAP.ConstructiveFraction.add_le_add_direct referenceBound (le_refl _)
      _ = (1 + weight) ^ 2 *
            RFAP.ConstructiveGaussian.Gaussian.normSq referenceExact +
          (referenceLoss + contenderLoss) := by ring1
      _ < (1 + weight) ^ 2 *
            RFAP.ConstructiveGaussian.Gaussian.normSq referenceExact +
          margin :=
        RFAP.ConstructiveFraction.add_lt_add_left_direct lossLtMargin _
      _ = weight ^ 2 *
          RFAP.ConstructiveGaussian.Gaussian.normSq contenderExact := by
        dsimp only [margin, comparisonMargin, referenceExact,
          contenderExact]
        unfold errorQuadrance
        ring1
  have scaledSampleStrict :
      weight * (1 + weight) *
          RFAP.ConstructiveGaussian.Gaussian.normSq referenceSample <
        weight * (1 + weight) *
          RFAP.ConstructiveGaussian.Gaussian.normSq contenderSample := by
    have withLoss := referenceWithContenderLoss.trans_le contenderBound
    have cancelled :=
      RFAP.ConstructiveFraction.lt_of_add_lt_add_right_direct withLoss
    simpa only using cancelled
  unfold errorQuadrance
  apply RFAP.ConstructiveFraction.lt_of_mul_lt_mul_right_direct
    (c := weight * (1 + weight))
  · calc
      RFAP.ConstructiveGaussian.Gaussian.normSq referenceSample *
          (weight * (1 + weight)) =
        weight * (1 + weight) *
          RFAP.ConstructiveGaussian.Gaussian.normSq referenceSample := by ring1
      _ < weight * (1 + weight) *
          RFAP.ConstructiveGaussian.Gaussian.normSq contenderSample :=
        scaledSampleStrict
      _ = RFAP.ConstructiveGaussian.Gaussian.normSq contenderSample *
          (weight * (1 + weight)) := by ring1
  · exact RFAP.ConstructiveFraction.mul_pos_direct weightPositive
      onePlusWeightPositive

end RFAP.ErrorComparisonStability
