module
import Purelib.Data.GaussianInt.Pair.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Cast
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Weighted
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
public import Purelib.Data.Rat.Rounding.Floor
public import Purelib.NumberTheory.Approximation.Best.Error
import Purelib.NumberTheory.Approximation.Best.Error.Bounds

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.GaussianInt.Embedding
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Data

open Purelib.Data.Rat

open Purelib

open Purelib.NumberTheory.Approximation

section
public section

/-!
# Explicit rational stability of a strict error comparison

A strict comparison between two displayed approximation errors has rational
clearance.  A computed natural weight turns the two weighted quadrance
inequalities into an explicit positive squared-distance budget preserving
that comparison.  This is a wholly finite substitute for an appeal to
continuity or openness.
-/

namespace Purelib.NumberTheory.Approximation.Best.Stability.ErrorComparison

/-- The contender error quadrance minus the reference error quadrance at the center.

A positive value records a strict advantage for the reference approximation. -/
@[expose] def comparisonClearance
    (center : Gaussian.Basic.Canonical) (reference contender : GaussianInt.Pair.Basic.ConvergentPair) :
      Fraction.Rational :=
  Best.Error.errorQuadrance center contender - Best.Error.errorQuadrance center reference

/-- A strict reference advantage gives positive comparison clearance. -/
theorem comparisonClearance_pos
    {center : Gaussian.Basic.Canonical} {reference contender : GaussianInt.Pair.Basic.ConvergentPair}
    (strict : Best.Error.errorQuadrance center reference <
      Best.Error.errorQuadrance center contender) :
    0 < comparisonClearance center reference contender := by
  exact Fraction.Order.Arithmetic.sub_pos_direct strict

/-- A finite weight large enough to absorb the multiplicative slack in both
weighted quadrance estimates. -/
@[expose] def comparisonWeightNat
    (center : Gaussian.Basic.Canonical) (reference contender : GaussianInt.Pair.Basic.ConvergentPair) : Nat :=
  Data.Rat.Rounding.Floor.ceilNat
      (4 * (Best.Error.errorQuadrance center reference + 1) /
        comparisonClearance center reference contender) + 1

/-- The rational reading of the computed positive natural comparison weight.

The integer-backed cast reads the original natural weight directly without
performing one rational addition for every unit of that weight. -/
@[expose] def comparisonWeight
    (center : Gaussian.Basic.Canonical) (reference contender : GaussianInt.Pair.Basic.ConvergentPair) :
      Fraction.Rational :=
  Fraction.Cast.fromInt
    (comparisonWeightNat center reference contender : Int)

/-- The direct rational reading equals the cast of the original natural weight. -/
theorem comparisonWeight_eq_cast
    (center : Gaussian.Basic.Canonical) (reference contender : GaussianInt.Pair.Basic.ConvergentPair) :
    comparisonWeight center reference contender =
      (comparisonWeightNat center reference contender : Fraction.Rational) :=
  (Fraction.Cast.natCast_eq_fromInt _).symm

/-- The ceiling-based comparison weight is strictly positive. -/
theorem comparisonWeight_pos
    (center : Gaussian.Basic.Canonical) (reference contender : GaussianInt.Pair.Basic.ConvergentPair) :
    0 < comparisonWeight center reference contender := by
  rewrite [comparisonWeight_eq_cast]
  apply Fraction.Cast.Order.natCast_pos_direct
  unfold comparisonWeightNat
  exact Nat.zero_lt_succ _

/-- The comparison weight is at least one. -/
theorem one_le_comparisonWeight
    (center : Gaussian.Basic.Canonical) (reference contender : GaussianInt.Pair.Basic.ConvergentPair) :
    (1 : Fraction.Rational) ≤ comparisonWeight center reference contender := by
  rewrite [comparisonWeight_eq_cast]
  change ((1 : Nat) : Fraction.Rational) ≤
    (comparisonWeightNat center reference contender : Fraction.Rational)
  apply Fraction.Cast.Order.natCast_le_direct
  unfold comparisonWeightNat
  exact Nat.succ_le_succ (Nat.zero_le _)

/-- The computed weight times clearance strictly exceeds four times the reference quadrance plus one.

The strict error comparison makes the clearance positive, so the ceiling construction yields the required strict product
bound. -/
private theorem
  four_reference_lt_weight_mul_clearance
    {center : Gaussian.Basic.Canonical} {reference contender : GaussianInt.Pair.Basic.ConvergentPair}
    (strict : Best.Error.errorQuadrance center reference <
      Best.Error.errorQuadrance center contender) :
    4 * (Best.Error.errorQuadrance center reference + 1) <
      comparisonWeight center reference contender *
        comparisonClearance center reference contender := by
  have clearancePositive := comparisonClearance_pos strict
  have numeratorNonnegative :
      (0 : Fraction.Rational) ≤ 4 * (Best.Error.errorQuadrance center reference + 1) :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (add_nonneg
        (Gaussian.Norm.Basic.normSq_nonneg _)
        (by decide))
  have ratioNonnegative :
      (0 : Fraction.Rational) ≤
        4 * (Best.Error.errorQuadrance center reference + 1) /
          comparisonClearance center reference contender :=
    Fraction.Order.Field.div_nonneg_direct numeratorNonnegative
      clearancePositive.le
  have ratioLeCeiling :
      4 * (Best.Error.errorQuadrance center reference + 1) /
          comparisonClearance center reference contender ≤
        (Data.Rat.Rounding.Floor.ceilNat
          (4 * (Best.Error.errorQuadrance center reference + 1) /
            comparisonClearance center reference contender) : Fraction.Rational) :=
    Data.Rat.Rounding.Floor.le_natCast_ceilNat_of_nonneg ratioNonnegative
  have ceilingLtWeight :
      (Data.Rat.Rounding.Floor.ceilNat
          (4 * (Best.Error.errorQuadrance center reference + 1) /
            comparisonClearance center reference contender) : Fraction.Rational) <
        comparisonWeight center reference contender := by
    rewrite [comparisonWeight_eq_cast]
    apply Fraction.Cast.Order.natCast_lt_direct
    unfold comparisonWeightNat
    exact Nat.lt_add_one_iff.mpr (Nat.le_refl _)
  have ratioLtWeight := ratioLeCeiling.trans_lt ceilingLtWeight
  exact (Fraction.Order.Field.div_lt_iff_pos clearancePositive).1
    ratioLtWeight

/-- Positive strictness left after compensating for the two weighted
quadrance normalizations. -/
@[expose] def comparisonMargin
    (center : Gaussian.Basic.Canonical) (reference contender : GaussianInt.Pair.Basic.ConvergentPair) :
      Fraction.Rational :=
  comparisonWeight center reference contender ^ 2 *
      Best.Error.errorQuadrance center contender -
    (1 + comparisonWeight center reference contender) ^ 2 *
      Best.Error.errorQuadrance center reference

/-- A strict center comparison gives a positive weighted comparison margin.

The ceiling weight compensates for both weighted quadrance normalizations without changing either approximation pair. -/
theorem comparisonMargin_pos
    {center : Gaussian.Basic.Canonical} {reference contender : GaussianInt.Pair.Basic.ConvergentPair}
    (strict : Best.Error.errorQuadrance center reference <
      Best.Error.errorQuadrance center contender) :
    0 < comparisonMargin center reference contender := by
  let referenceNorm := Best.Error.errorQuadrance center reference
  let contenderNorm := Best.Error.errorQuadrance center contender
  let clearance := comparisonClearance center reference contender
  let weight := comparisonWeight center reference contender
  have referenceNonnegative : 0 ≤ referenceNorm :=
    Gaussian.Norm.Basic.normSq_nonneg _
  have weightPositive : 0 < weight := by
    simpa only [-eq_self, -iff_self, weight] using
      comparisonWeight_pos center reference contender
  have oneLeWeight : (1 : Fraction.Rational) ≤ weight := by
    simpa only [-eq_self, -iff_self, weight] using
      one_le_comparisonWeight center reference contender
  have oneLeTwoWeight : (1 : Fraction.Rational) ≤ 2 * weight := by
    calc
      (1 : Fraction.Rational) ≤ weight := oneLeWeight
      _ = 1 * weight := by ring1
      _ ≤ 2 * weight :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          (by decide) weightPositive.le
  have twoWeightMinusOneNonnegative : 0 ≤ 2 * weight - 1 :=
    Fraction.Order.Arithmetic.sub_nonneg_direct oneLeTwoWeight
  have shortGapPositive :
      0 < (2 * weight - 1) * referenceNorm + 4 * weight := by
    exact Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct
      (Fraction.Order.Arithmetic.mul_nonneg_direct
        twoWeightMinusOneNonnegative referenceNonnegative)
      (Fraction.Order.Arithmetic.mul_pos_direct (by decide) weightPositive)
  have shortBound :
      (2 * weight + 1) * referenceNorm <
        4 * weight * (referenceNorm + 1) := by
    apply Fraction.Order.Arithmetic.lt_of_sub_pos_direct
    calc
      (0 : Fraction.Rational) <
          (2 * weight - 1) * referenceNorm + 4 * weight :=
        shortGapPositive
      _ = 4 * weight * (referenceNorm + 1) -
          (2 * weight + 1) * referenceNorm := by ring1
  have weightedClearance :
      4 * weight * (referenceNorm + 1) < weight ^ 2 * clearance := by
    have scaled :=
      Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct weightPositive
        (show 4 * (referenceNorm + 1) < weight * clearance by
          simpa only [-eq_self, -iff_self, referenceNorm, clearance, weight] using
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
        Fraction.Order.Arithmetic.add_lt_add_left_direct
          (shortBound.trans weightedClearance) _
      _ = weight ^ 2 * contenderNorm := by
        dsimp only [clearance, comparisonClearance, referenceNorm,
          contenderNorm]
        ring1
  unfold comparisonMargin
  simpa only [-eq_self, -iff_self, referenceNorm, contenderNorm, weight] using
    Fraction.Order.Arithmetic.sub_pos_direct baselineStrict

/-- Coefficient converting squared source displacement into the two
weighted perturbation losses.

Both retained denominator quadrances use direct integer-backed rational
readings, preserving the original weight and each original denominator. -/
@[expose] def comparisonCoefficient
    (center : Gaussian.Basic.Canonical) (reference contender : GaussianInt.Pair.Basic.ConvergentPair) :
      Fraction.Rational :=
  let weight := comparisonWeight center reference contender
  weight * (1 + weight) ^ 2 *
      Fraction.Cast.fromInt (Best.Error.denominatorQuadrance reference : Int) +
    weight ^ 2 * (1 + weight) *
      Fraction.Cast.fromInt (Best.Error.denominatorQuadrance contender : Int)

/-- The direct coefficient equals the expression using the original natural casts. -/
theorem comparisonCoefficient_eq_cast
    (center : Gaussian.Basic.Canonical) (reference contender : GaussianInt.Pair.Basic.ConvergentPair) :
    comparisonCoefficient center reference contender =
      let weight := comparisonWeight center reference contender
      weight * (1 + weight) ^ 2 *
          (Best.Error.denominatorQuadrance reference : Fraction.Rational) +
        weight ^ 2 * (1 + weight) *
          (Best.Error.denominatorQuadrance contender : Fraction.Rational) := by
  unfold comparisonCoefficient
  rewrite [Fraction.Cast.natCast_eq_fromInt, Fraction.Cast.natCast_eq_fromInt]
  rfl

/-- The coefficient of the squared source displacement is nonnegative. -/
theorem comparisonCoefficient_nonneg
    (center : Gaussian.Basic.Canonical) (reference contender : GaussianInt.Pair.Basic.ConvergentPair) :
    0 ≤ comparisonCoefficient center reference contender := by
  let weight := comparisonWeight center reference contender
  have weightNonnegative : 0 ≤ weight :=
    (comparisonWeight_pos center reference contender).le
  have onePlusWeightNonnegative : 0 ≤ 1 + weight :=
    add_nonneg (by decide) weightNonnegative
  rewrite [comparisonCoefficient_eq_cast]
  dsimp only [weight]
  exact add_nonneg
    (Fraction.Order.Arithmetic.mul_nonneg_direct
      (Fraction.Order.Arithmetic.mul_nonneg_direct weightNonnegative
        (Fraction.Order.Arithmetic.pow_nonneg_direct
          onePlusWeightNonnegative 2))
      (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)))
    (Fraction.Order.Arithmetic.mul_nonneg_direct
      (Fraction.Order.Arithmetic.mul_nonneg_direct
        (Fraction.Order.Arithmetic.pow_nonneg_direct weightNonnegative 2)
        onePlusWeightNonnegative)
      (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)))

/-- Explicit positive squared-distance budget preserving one strict rational
error comparison. -/
@[expose] def comparisonDistanceSq
    (center : Gaussian.Basic.Canonical) (reference contender : GaussianInt.Pair.Basic.ConvergentPair) :
      Fraction.Rational :=
  comparisonMargin center reference contender /
    (1 + comparisonCoefficient center reference contender)

/-- A strict center comparison gives a positive computed squared-distance budget. -/
theorem comparisonDistanceSq_pos
    {center : Gaussian.Basic.Canonical} {reference contender : GaussianInt.Pair.Basic.ConvergentPair}
    (strict : Best.Error.errorQuadrance center reference <
      Best.Error.errorQuadrance center contender) :
    0 < comparisonDistanceSq center reference contender := by
  unfold comparisonDistanceSq
  exact Fraction.Order.Field.div_pos_direct
    (comparisonMargin_pos strict)
    ((show (0 : Fraction.Rational) < 1 by decide).trans_le
      (le_add_of_nonneg_right
        (comparisonCoefficient_nonneg center reference contender)))

/-- Subtracting the denominator-scaled source displacement recovers the center error. -/
private theorem exact_error_sum_identity
    (center sample : Gaussian.Basic.Canonical) (pair : GaussianInt.Pair.Basic.ConvergentPair) :
    Best.Error.error sample pair +
        -((sample - center) * Purelib.Data.GaussianInt.toGaussian pair.denominator) =
      Best.Error.error center pair := by
  rw [Best.Error.error_perturbation_identity]
  apply Gaussian.Basic.ext <;>
    simp only [-eq_self, -iff_self, Gaussian.Basic.add_re,
      Gaussian.Basic.add_im,
      Gaussian.Basic.neg_re,
      Gaussian.Basic.neg_im] <;>
    ring1

/-- The error perturbation quadrance is source displacement quadrance times denominator quadrance. -/
private theorem perturbation_normSq
    (center sample : Gaussian.Basic.Canonical) (pair : GaussianInt.Pair.Basic.ConvergentPair) :
    Data.Gaussian.Norm.Basic.normSq
        ((sample - center) * Purelib.Data.GaussianInt.toGaussian pair.denominator) =
      Data.Gaussian.Norm.Basic.normSq (sample - center) *
        (Best.Error.denominatorQuadrance pair : Fraction.Rational) := by
  rw [Gaussian.Norm.Basic.normSq_mul, GaussianInt.normSq_toGaussian]
  rfl

/-- Every source inside the computed rational squared-distance budget retains
the supplied strict error comparison. -/
theorem errorQuadrance_lt_of_distance
    {center sample : Gaussian.Basic.Canonical} {reference contender : GaussianInt.Pair.Basic.ConvergentPair}
    (_strict : Best.Error.errorQuadrance center reference <
      Best.Error.errorQuadrance center contender)
    (distanceSmall :
      Data.Gaussian.Norm.Basic.normSq (sample - center) <
        comparisonDistanceSq center reference contender) :
    Best.Error.errorQuadrance sample reference < Best.Error.errorQuadrance sample contender := by
  let weight := comparisonWeight center reference contender
  let referenceExact := Best.Error.error center reference
  let contenderExact := Best.Error.error center contender
  let referenceSample := Best.Error.error sample reference
  let contenderSample := Best.Error.error sample contender
  let referencePerturbation :=
    (sample - center) * GaussianInt.toGaussian reference.denominator
  let contenderPerturbation :=
    (sample - center) * GaussianInt.toGaussian contender.denominator
  let distance :=
    Data.Gaussian.Norm.Basic.normSq (sample - center)
  let coefficient := comparisonCoefficient center reference contender
  let margin := comparisonMargin center reference contender
  let referenceLoss :=
    weight * (1 + weight) ^ 2 *
      Data.Gaussian.Norm.Basic.normSq referencePerturbation
  let contenderLoss :=
    weight ^ 2 * (1 + weight) *
      Data.Gaussian.Norm.Basic.normSq contenderPerturbation
  have weightPositive : 0 < weight := by
    simpa only [-eq_self, -iff_self, weight] using
      comparisonWeight_pos center reference contender
  have onePlusWeightPositive : 0 < 1 + weight :=
    (show (0 : Fraction.Rational) < 1 by decide).trans_le
      (le_add_of_nonneg_right weightPositive.le)
  have coefficientNonnegative : 0 ≤ coefficient := by
    simpa only [-eq_self, -iff_self, coefficient] using
      comparisonCoefficient_nonneg center reference contender
  have lossIdentity :
      referenceLoss + contenderLoss = coefficient * distance := by
    dsimp only [referenceLoss, contenderLoss]
    rw [show Data.Gaussian.Norm.Basic.normSq referencePerturbation =
          distance * (Best.Error.denominatorQuadrance reference : Fraction.Rational) by
        dsimp only [referencePerturbation, distance]
        exact perturbation_normSq center sample reference,
      show Data.Gaussian.Norm.Basic.normSq contenderPerturbation =
          distance * (Best.Error.denominatorQuadrance contender : Fraction.Rational) by
        dsimp only [contenderPerturbation, distance]
        exact perturbation_normSq center sample contender]
    dsimp only [coefficient, distance]
    rewrite [comparisonCoefficient_eq_cast]
    dsimp only [weight]
    ring1
  have lossLtMargin : referenceLoss + contenderLoss < margin := by
    have denominatorPositive : 0 < 1 + coefficient :=
      (show (0 : Fraction.Rational) < 1 by decide).trans_le
        (le_add_of_nonneg_right coefficientNonnegative)
    have scaledDistance :=
      (Fraction.Order.Field.lt_div_iff_pos denominatorPositive).1
        (show distance < margin / (1 + coefficient) by
          simpa only [-eq_self, -iff_self, distance, margin, coefficient,
            comparisonDistanceSq]
            using distanceSmall)
    rw [lossIdentity]
    calc
      coefficient * distance ≤ (1 + coefficient) * distance :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          (le_add_of_nonneg_left (by decide))
          (Gaussian.Norm.Basic.normSq_nonneg _)
      _ = distance * (1 + coefficient) := by ring1
      _ < margin := scaledDistance
  have weightedReference := Gaussian.Norm.Weighted.weighted_normSq_add_le
    referenceExact referencePerturbation 1 weight
  have referenceBound :
      weight * (1 + weight) *
          Data.Gaussian.Norm.Basic.normSq referenceSample ≤
        (1 + weight) ^ 2 *
            Data.Gaussian.Norm.Basic.normSq referenceExact +
          referenceLoss := by
    rw [← Best.Error.error_perturbation_identity center sample reference] at weightedReference
    have scaled :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        weightedReference onePlusWeightPositive.le
    dsimp only [referenceLoss]
    calc
      weight * (1 + weight) *
          Data.Gaussian.Norm.Basic.normSq referenceSample =
        (1 + weight) *
          (1 * weight *
            Data.Gaussian.Norm.Basic.normSq referenceSample) := by
          ring1
      _ ≤ (1 + weight) *
          (1 * (1 + weight) *
              Data.Gaussian.Norm.Basic.normSq referenceExact +
            weight * (1 + weight) *
              Data.Gaussian.Norm.Basic.normSq
                referencePerturbation) := scaled
      _ = (1 + weight) ^ 2 *
            Data.Gaussian.Norm.Basic.normSq referenceExact +
          weight * (1 + weight) ^ 2 *
            Data.Gaussian.Norm.Basic.normSq
              referencePerturbation := by ring1
  have weightedContender := Gaussian.Norm.Weighted.weighted_normSq_add_le
    contenderSample (-contenderPerturbation) 1 weight
  have contenderBound :
      weight ^ 2 *
          Data.Gaussian.Norm.Basic.normSq contenderExact ≤
        weight * (1 + weight) *
            Data.Gaussian.Norm.Basic.normSq contenderSample +
          contenderLoss := by
    rw [exact_error_sum_identity center sample contender,
      Gaussian.Norm.Basic.normSq_neg] at weightedContender
    have scaled :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        weightedContender weightPositive.le
    dsimp only [contenderLoss]
    calc
      weight ^ 2 *
          Data.Gaussian.Norm.Basic.normSq contenderExact =
        weight *
          (1 * weight *
            Data.Gaussian.Norm.Basic.normSq contenderExact) := by
          ring1
      _ ≤ weight *
          (1 * (1 + weight) *
              Data.Gaussian.Norm.Basic.normSq contenderSample +
            weight * (1 + weight) *
              Data.Gaussian.Norm.Basic.normSq
                contenderPerturbation) := scaled
      _ = weight * (1 + weight) *
            Data.Gaussian.Norm.Basic.normSq contenderSample +
          weight ^ 2 * (1 + weight) *
            Data.Gaussian.Norm.Basic.normSq
              contenderPerturbation := by ring1
  have referenceWithContenderLoss :
      weight * (1 + weight) *
            Data.Gaussian.Norm.Basic.normSq referenceSample +
          contenderLoss <
        weight ^ 2 *
          Data.Gaussian.Norm.Basic.normSq contenderExact := by
    calc
      weight * (1 + weight) *
            Data.Gaussian.Norm.Basic.normSq referenceSample +
          contenderLoss ≤
        ((1 + weight) ^ 2 *
            Data.Gaussian.Norm.Basic.normSq referenceExact +
          referenceLoss) + contenderLoss :=
        Fraction.Order.Arithmetic.add_le_add_direct referenceBound (le_refl _)
      _ = (1 + weight) ^ 2 *
            Data.Gaussian.Norm.Basic.normSq referenceExact +
          (referenceLoss + contenderLoss) := by ring1
      _ < (1 + weight) ^ 2 *
            Data.Gaussian.Norm.Basic.normSq referenceExact +
          margin :=
        Fraction.Order.Arithmetic.add_lt_add_left_direct lossLtMargin _
      _ = weight ^ 2 *
          Data.Gaussian.Norm.Basic.normSq contenderExact := by
        dsimp only [margin, comparisonMargin, referenceExact,
          contenderExact]
        unfold Best.Error.errorQuadrance
        ring1
  have scaledSampleStrict :
      weight * (1 + weight) *
          Data.Gaussian.Norm.Basic.normSq referenceSample <
        weight * (1 + weight) *
          Data.Gaussian.Norm.Basic.normSq contenderSample := by
    have withLoss := referenceWithContenderLoss.trans_le contenderBound
    have cancelled :=
      Fraction.Order.Arithmetic.lt_of_add_lt_add_right_direct withLoss
    simpa only using cancelled
  unfold Best.Error.errorQuadrance
  apply Fraction.Order.Arithmetic.lt_of_mul_lt_mul_right_direct
    (c := weight * (1 + weight))
  · calc
      Data.Gaussian.Norm.Basic.normSq referenceSample *
          (weight * (1 + weight)) =
        weight * (1 + weight) *
          Data.Gaussian.Norm.Basic.normSq referenceSample := by ring1
      _ < weight * (1 + weight) *
          Data.Gaussian.Norm.Basic.normSq contenderSample :=
        scaledSampleStrict
      _ = Data.Gaussian.Norm.Basic.normSq contenderSample *
          (weight * (1 + weight)) := by ring1
  · exact Fraction.Order.Arithmetic.mul_pos_direct weightPositive
      onePlusWeightPositive

end Purelib.NumberTheory.Approximation.Best.Stability.ErrorComparison

end
