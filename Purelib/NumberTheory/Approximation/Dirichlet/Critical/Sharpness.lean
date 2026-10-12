module
import Purelib.Algebra.NatCast
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Rounding.Floor
import Purelib.NumberTheory.Approximation.Best.Consecutive.Basic
import Purelib.NumberTheory.Approximation.Best.Error
import Purelib.NumberTheory.Approximation.Dirichlet.Critical.Cylinder.Basic
public import Purelib.NumberTheory.Approximation.Dirichlet.Critical.Pair
import Purelib.NumberTheory.Approximation.Dirichlet.Critical.Parameter
import Purelib.NumberTheory.Approximation.Dirichlet.Window.SourceBound
import Purelib.NumberTheory.Pell.FiniteBranch
import Purelib.Data.GaussianInt.Embedding
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.GaussianInt.Fraction.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

public section

open Purelib.Data.Rat

open Purelib

open Purelib.NumberTheory.Approximation

open Purelib.NumberTheory

section

/-!
# Sharpness of Pell-indexed approximation windows

Exact rational boundary factors compare the Pell parameter with a supplied
sharper threshold. The finite stage retains its requested scale and the original
pair construction, together with the displayed strict clearance bounds.
-/

namespace Purelib.NumberTheory.Approximation.Dirichlet.Critical.Sharpness

/-- The normalized gap and the actual squared Dirichlet window are exact
reciprocals. -/
theorem criticalGap_mul_dirichletWindow (stage :
  Nat) :
    Dirichlet.Critical.Cylinder.Basic.criticalGap (Dirichlet.Critical.Parameter.pellParameter stage) *
      Dirichlet.Window.SourceBound.dirichletWindowQuadrance (Dirichlet.Critical.Pair.criticalSource stage).value
        (Dirichlet.Critical.Pair.criticalLowerPair stage) (Dirichlet.Critical.Pair.criticalUpperPair stage) = 1 := open
          Purelib.Data in by
  have productNonzero :
      GaussianInt.toGaussian (Dirichlet.Critical.Pair.criticalUpperPair stage).denominator *
          Dirichlet.Critical.Pair.criticalGapVector (Dirichlet.Critical.Parameter.pellParameter stage) ≠ 0 :=
    Gaussian.Field.mul_ne_zero_direct
      (Dirichlet.Critical.Pair.criticalUpper_denominatorGaussian_ne_zero stage)
      (Dirichlet.Critical.Pair.criticalGapVector_ne_zero (Dirichlet.Critical.Parameter.pellParameter_isCritical stage))
  have productNormNonzero :
      Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian (Dirichlet.Critical.Pair.criticalUpperPair
        stage).denominator *
        Dirichlet.Critical.Pair.criticalGapVector (Dirichlet.Critical.Parameter.pellParameter stage)) ≠ 0 :=
    fun zero => productNonzero (Gaussian.Norm.Basic.normSq_eq_zero.mp zero)
  rewrite [Dirichlet.Window.SourceBound.dirichletWindowQuadrance_eq_cast]
  unfold Best.Error.denominatorQuadrance Best.Error.errorQuadrance
  rw [Dirichlet.Critical.Pair.criticalSource_error_lower, ← GaussianInt.normSq_toGaussian]
  unfold Dirichlet.Critical.Pair.criticalLowerError Dirichlet.Critical.Cylinder.Basic.criticalGap
  rw [Gaussian.Norm.Basic.normSq_neg,
    Gaussian.Field.normSq_inv _ productNonzero,
    Gaussian.Norm.Basic.normSq_mul]
  change
    Data.Gaussian.Norm.Basic.normSq (Dirichlet.Critical.Pair.criticalGapVector
      (Dirichlet.Critical.Parameter.pellParameter stage)) *
        (Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian (Dirichlet.Critical.Pair.criticalUpperPair
          stage).denominator) *
          (Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian (Dirichlet.Critical.Pair.criticalUpperPair
            stage).denominator) *
            Data.Gaussian.Norm.Basic.normSq (Dirichlet.Critical.Pair.criticalGapVector
              (Dirichlet.Critical.Parameter.pellParameter stage)))⁻¹) = 1
  calc
    Data.Gaussian.Norm.Basic.normSq (Dirichlet.Critical.Pair.criticalGapVector
      (Dirichlet.Critical.Parameter.pellParameter stage)) *
          (Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian (Dirichlet.Critical.Pair.criticalUpperPair
            stage).denominator) *
            (Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian (Dirichlet.Critical.Pair.criticalUpperPair
              stage).denominator) *
              Data.Gaussian.Norm.Basic.normSq (Dirichlet.Critical.Pair.criticalGapVector
                (Dirichlet.Critical.Parameter.pellParameter stage)))⁻¹) =
        (Data.Gaussian.Norm.Basic.normSq (Dirichlet.Critical.Pair.criticalGapVector
          (Dirichlet.Critical.Parameter.pellParameter stage)) *
            Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian (Dirichlet.Critical.Pair.criticalUpperPair
              stage).denominator)) *
          (Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian (Dirichlet.Critical.Pair.criticalUpperPair
            stage).denominator) *
            Data.Gaussian.Norm.Basic.normSq (Dirichlet.Critical.Pair.criticalGapVector
              (Dirichlet.Critical.Parameter.pellParameter stage)))⁻¹ :=
      (Fraction.Field.mul_assoc _ _ _).symm
    _ = (Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian (Dirichlet.Critical.Pair.criticalUpperPair
      stage).denominator) *
            Data.Gaussian.Norm.Basic.normSq (Dirichlet.Critical.Pair.criticalGapVector
              (Dirichlet.Critical.Parameter.pellParameter stage))) *
          (Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian (Dirichlet.Critical.Pair.criticalUpperPair
            stage).denominator) *
            Data.Gaussian.Norm.Basic.normSq (Dirichlet.Critical.Pair.criticalGapVector
              (Dirichlet.Critical.Parameter.pellParameter stage)))⁻¹ := by
      rw [Fraction.Field.mul_comm
        (Data.Gaussian.Norm.Basic.normSq (Dirichlet.Critical.Pair.criticalGapVector
          (Dirichlet.Critical.Parameter.pellParameter stage)))]
    _ = Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian (Dirichlet.Critical.Pair.criticalUpperPair
      stage).denominator *
            Dirichlet.Critical.Pair.criticalGapVector (Dirichlet.Critical.Parameter.pellParameter stage)) *
          (Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian (Dirichlet.Critical.Pair.criticalUpperPair
            stage).denominator *
            Dirichlet.Critical.Pair.criticalGapVector (Dirichlet.Critical.Parameter.pellParameter stage)))⁻¹ := by
      rw [Gaussian.Norm.Basic.normSq_mul]
    _ = 1 := Fraction.Field.mul_inv_cancel _ productNormNonzero

/-- Exact rational factorization of the critical gap.  Clearing the fixed
denominator `16` avoids introducing the omitted quadratic endpoint. -/
theorem criticalGap_scaled_factorization (value :
  Fraction.Rational) :
    Dirichlet.Critical.Cylinder.Basic.criticalGap value * 16 =
      48 * value +
        Dirichlet.Critical.Cylinder.Basic.parameterPolynomial value * (value ^ 2 + 4 * value + 17) := by
  calc
    Dirichlet.Critical.Cylinder.Basic.criticalGap value * 16 =
        48 * value +
          Dirichlet.Critical.Cylinder.Basic.parameterPolynomial value * (value ^ 2 + 4 * value + 17) +
          (4 * Dirichlet.Critical.Cylinder.Basic.half ^ 2 - 1) *
            ((4 * Dirichlet.Critical.Cylinder.Basic.half ^ 2 + 1) * (1 + value ^ 2) ^ 2 -
              16 * value) := by
      rw [Dirichlet.Critical.Cylinder.Basic.criticalGap_eq]
      unfold Dirichlet.Critical.Cylinder.Basic.parameterPolynomial
      simp only [Dirichlet.Critical.Cylinder.Basic.half, -eq_self, -iff_self]
      ring1
    _ = 48 * value +
        Dirichlet.Critical.Cylinder.Basic.parameterPolynomial value * (value ^ 2 + 4 * value + 17) := by
      rw [Dirichlet.Critical.Cylinder.Basic.four_mul_half_sq]
      ring1

/-- A coarse but convenient strict defect estimate.  Its slack is ample on
`1/4 ≤ s < 1/3`, and its denominator-free form composes cleanly with the
Pell identity. -/
theorem
  criticalGap_lt_three_parameter_add_two_defects
    {value : Fraction.Rational} (certificate : Dirichlet.Critical.Cylinder.Basic.IsCriticalParameter value) :
    Dirichlet.Critical.Cylinder.Basic.criticalGap value <
      3 * value + 2 * Dirichlet.Critical.Cylinder.Basic.parameterPolynomial value := by
  have valueNonnegative := Dirichlet.Critical.Cylinder.Basic.criticalParameter_nonnegative certificate
  have valueLtOne : value < (1 : Fraction.Rational) :=
    certificate.2.1.trans (by decide)
  have squareLeOne : value ^ 2 ≤ (1 : Fraction.Rational) := by
    have valueLeOne := valueLtOne.le
    simpa only [one_pow, -eq_self, -iff_self] using
      Fraction.Order.Arithmetic.pow_le_pow_direct valueNonnegative valueLeOne 2
  have fourValueLtTwo : 4 * value < (2 : Fraction.Rational) := by
    calc
      4 * value < 4 * (1 / 3 : Fraction.Rational) :=
        Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
          (by decide) certificate.2.1
      _ < 2 := by decide
  have factorLtThirtyTwo :
      value ^ 2 + 4 * value + 17 < (32 : Fraction.Rational) := by
    calc
      value ^ 2 + 4 * value + 17 ≤ 1 + 4 * value + 17 :=
        Fraction.Order.Arithmetic.add_le_add_right_direct
          (Fraction.Order.Arithmetic.add_le_add_right_direct
            squareLeOne (4 * value)) 17
      _ < 1 + 2 + 17 :=
        Fraction.Order.Arithmetic.add_lt_add_right_direct
          (Fraction.Order.Arithmetic.add_lt_add_left_direct
            fourValueLtTwo 1) 17
      _ = 20 := by ring1
      _ < 32 := by
        simpa only [Nat.cast_ofNat, -eq_self, -iff_self] using
          Fraction.Cast.Order.natCast_lt_direct
            (show 20 < 32 by decide)
  have defectScaledStrict :
      Dirichlet.Critical.Cylinder.Basic.parameterPolynomial value * (value ^ 2 + 4 * value + 17) <
        Dirichlet.Critical.Cylinder.Basic.parameterPolynomial value * 32 :=
    Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
      certificate.2.2 factorLtThirtyTwo
  apply Fraction.Order.Arithmetic.lt_of_mul_lt_mul_right_direct (c := 16)
  · calc
      Dirichlet.Critical.Cylinder.Basic.criticalGap value * 16 =
          48 * value + Dirichlet.Critical.Cylinder.Basic.parameterPolynomial value *
            (value ^ 2 + 4 * value + 17) :=
        criticalGap_scaled_factorization value
      _ < 48 * value + Dirichlet.Critical.Cylinder.Basic.parameterPolynomial value * 32 :=
        Fraction.Order.Arithmetic.add_lt_add_left_direct
          defectScaledStrict (48 * value)
      _ = (3 * value + 2 * Dirichlet.Critical.Cylinder.Basic.parameterPolynomial value) * 16 := by
        ring1
  · simpa only [Nat.cast_ofNat, -eq_self, -iff_self] using
      Fraction.Cast.Order.natCast_pos_direct
        (show 0 < 16 by decide)

/-- Polynomial whose smaller omitted zero is the optimal rational-window
threshold. -/
@[expose] def windowBoundaryPolynomial (threshold
  : Fraction.Rational) : Fraction.Rational :=
  threshold ^ 2 - 12 * threshold + 9

/-- A displayed threshold on the sharper side of the optimal boundary. -/
@[expose] def IsSharperWindowThreshold (threshold
  : Fraction.Rational) : Prop :=
  (3 / 4 : Fraction.Rational) ≤ threshold ∧ threshold < 1 ∧
    windowBoundaryPolynomial threshold < 0

/-- Multiplying the threshold parameter `threshold/3` by three recovers the threshold. -/
private theorem thresholdParameter_mul_three
  (threshold : Fraction.Rational) :
    (threshold / 3) * 3 = threshold :=
  Fraction.Field.div_mul_cancel_of_ne threshold 3 (by decide)

/-- The parameter polynomial at one third of a threshold becomes its window boundary polynomial after scaling by nine.
-/
theorem
  parameterPolynomial_thresholdParameter_scaled
    (threshold : Fraction.Rational) :
    Dirichlet.Critical.Cylinder.Basic.parameterPolynomial (threshold / 3) * 9 =
      windowBoundaryPolynomial threshold := by
  calc
    Dirichlet.Critical.Cylinder.Basic.parameterPolynomial (threshold / 3) * 9 =
        ((threshold / 3) * 3) ^ 2 -
          4 * ((threshold / 3) * 3) * 3 + 9 := by
      unfold Dirichlet.Critical.Cylinder.Basic.parameterPolynomial
      ring1
    _ = windowBoundaryPolynomial threshold := by
      rw [thresholdParameter_mul_three]
      unfold windowBoundaryPolynomial
      ring1

/-- A sharper threshold has a nonnegative parameter after division by three. -/
private theorem
  sharperThreshold_parameter_nonnegative
    {threshold : Fraction.Rational} (certificate : IsSharperWindowThreshold threshold) :
    0 ≤ threshold / 3 := by
  have thresholdNonnegative : (0 : Fraction.Rational) ≤ threshold :=
    (show (0 : Fraction.Rational) ≤ 3 / 4 by decide).trans certificate.1
  exact Fraction.Order.Field.div_nonneg_direct thresholdNonnegative
    (by decide)

/-- A sharper threshold divided by three is strictly below one third. -/
private theorem
  sharperThreshold_parameter_lt_oneThird
    {threshold : Fraction.Rational} (certificate : IsSharperWindowThreshold threshold) :
    threshold / 3 < (1 / 3 : Fraction.Rational) := by
  apply (Fraction.Order.Field.div_lt_iff_pos (by decide)).2
  calc
    threshold < 1 := certificate.2.1
    _ = (1 / 3 : Fraction.Rational) * 3 := by decide

/-- The parameter polynomial is negative at one third of a sharper threshold. -/
private theorem
  sharperThreshold_parameterPolynomial_neg
    {threshold : Fraction.Rational} (certificate : IsSharperWindowThreshold threshold) :
    Dirichlet.Critical.Cylinder.Basic.parameterPolynomial (threshold / 3) < 0 := by
  apply Fraction.Order.Arithmetic.lt_of_mul_lt_mul_right_direct (c := 9)
  · calc
      Dirichlet.Critical.Cylinder.Basic.parameterPolynomial (threshold / 3) * 9 =
          windowBoundaryPolynomial threshold :=
        parameterPolynomial_thresholdParameter_scaled threshold
      _ < 0 := certificate.2.2
      _ = (0 : Fraction.Rational) * 9 := by ring1
  · decide

/-- The difference of two parameter polynomial values factors into their reversed difference times `4 - right - left`.
-/
private theorem parameterPolynomial_difference
    (left right : Fraction.Rational) :
    Dirichlet.Critical.Cylinder.Basic.parameterPolynomial left - Dirichlet.Critical.Cylinder.Basic.parameterPolynomial
      right =
      (right - left) * (4 - right - left) := by
  unfold Dirichlet.Critical.Cylinder.Basic.parameterPolynomial
  ring1

/-- Every finite Pell parameter lies below one third of a sharper window threshold.

The parameter polynomial is positive on the Pell value and negative at the threshold parameter, and its exact difference
factorization gives the strict order. -/
private theorem
  pellParameter_lt_thresholdParameter
    {threshold : Fraction.Rational} (certificate : IsSharperWindowThreshold threshold)
    (stage : Nat) :
    Dirichlet.Critical.Parameter.pellParameter stage < threshold / 3 := by
  have leftPositive := Dirichlet.Critical.Parameter.parameterPolynomial_pellParameter_pos stage
  have rightNegative := sharperThreshold_parameterPolynomial_neg certificate
  have polynomialDifferencePositive :
      0 < Dirichlet.Critical.Cylinder.Basic.parameterPolynomial (Dirichlet.Critical.Parameter.pellParameter stage) -
        Dirichlet.Critical.Cylinder.Basic.parameterPolynomial (threshold / 3) :=
    Fraction.Order.Arithmetic.sub_pos_direct
      (rightNegative.trans leftPositive)
  have parameterSumLtFour :
      threshold / 3 + Dirichlet.Critical.Parameter.pellParameter stage < (4 : Fraction.Rational) := by
    calc
      threshold / 3 + Dirichlet.Critical.Parameter.pellParameter stage <
          (1 / 3 : Fraction.Rational) + 1 / 3 :=
        Fraction.Order.Arithmetic.add_lt_add_direct
          (sharperThreshold_parameter_lt_oneThird certificate)
          (Dirichlet.Critical.Parameter.pellParameter_isCritical stage).2.1
      _ < 4 := by decide
  have factorPositive :
      0 < 4 - threshold / 3 - Dirichlet.Critical.Parameter.pellParameter stage := by
    have differencePositive :=
      Fraction.Order.Arithmetic.sub_pos_direct parameterSumLtFour
    calc
      (0 : Fraction.Rational) < 4 - (threshold / 3 + Dirichlet.Critical.Parameter.pellParameter stage) :=
        differencePositive
      _ = 4 - threshold / 3 - Dirichlet.Critical.Parameter.pellParameter stage := by ring1
  have productPositive :
      0 < (4 - threshold / 3 - Dirichlet.Critical.Parameter.pellParameter stage) *
        (threshold / 3 - Dirichlet.Critical.Parameter.pellParameter stage) := by
    calc
      (0 : Fraction.Rational) <
          Dirichlet.Critical.Cylinder.Basic.parameterPolynomial (Dirichlet.Critical.Parameter.pellParameter stage) -
            Dirichlet.Critical.Cylinder.Basic.parameterPolynomial (threshold / 3) :=
        polynomialDifferencePositive
      _ = (4 - threshold / 3 - Dirichlet.Critical.Parameter.pellParameter stage) *
          (threshold / 3 - Dirichlet.Critical.Parameter.pellParameter stage) := by
        rw [parameterPolynomial_difference]
        ring1
  exact Fraction.Order.Arithmetic.lt_of_sub_pos_direct
    (Fraction.Order.Arithmetic.pos_of_mul_pos_right_direct
      productPositive factorPositive.le)

/-- The negative boundary polynomial is smaller than twelve times the threshold-to-Pell margin.

For a sharper threshold, the two parameter polynomials and their difference factorization bound the positive clearance
by `12 * (threshold - 3 * pellParameter stage)`. -/
private theorem
  boundaryClearance_lt_twelve_parameterMargin
    {threshold : Fraction.Rational} (certificate : IsSharperWindowThreshold threshold)
    (stage : Nat) :
    -windowBoundaryPolynomial threshold <
      12 * (threshold - 3 * Dirichlet.Critical.Parameter.pellParameter stage) := by
  let sourceParameter := Dirichlet.Critical.Parameter.pellParameter stage
  let thresholdParameter := threshold / 3
  have sourcePositive := Dirichlet.Critical.Parameter.parameterPolynomial_pellParameter_pos stage
  have parameterOrder : sourceParameter < thresholdParameter :=
    pellParameter_lt_thresholdParameter certificate stage
  have differencePositive : 0 < thresholdParameter - sourceParameter :=
    Fraction.Order.Arithmetic.sub_pos_direct parameterOrder
  have thresholdNonnegative :=
    sharperThreshold_parameter_nonnegative certificate
  have sourceNonnegative :=
    Dirichlet.Critical.Cylinder.Basic.criticalParameter_nonnegative
      (Dirichlet.Critical.Parameter.pellParameter_isCritical stage)
  have sumNonnegative : 0 ≤ thresholdParameter + sourceParameter :=
    add_nonneg thresholdNonnegative sourceNonnegative
  have factorLeFour :
      4 - thresholdParameter - sourceParameter ≤ (4 : Fraction.Rational) := by
    calc
      4 - thresholdParameter - sourceParameter =
          4 - (thresholdParameter + sourceParameter) := by ring1
      _ ≤ 4 := (Fraction.Order.Arithmetic.sub_le_iff_le_add_direct).mpr (by
          have shifted := Fraction.Order.Arithmetic.add_le_add_direct
            (Fraction.Order.Basic.le_refl (4 : Fraction.Rational)) sumNonnegative
          rw [Fraction.Field.add_comm _ (0 : Fraction.Rational), Fraction.Field.zero_add] at shifted
          exact shifted)
  have firstStrict :
      -windowBoundaryPolynomial threshold <
        9 * (Dirichlet.Critical.Cylinder.Basic.parameterPolynomial sourceParameter -
          Dirichlet.Critical.Cylinder.Basic.parameterPolynomial thresholdParameter) := by
    have scaledSourcePositive :
        0 < 9 * Dirichlet.Critical.Cylinder.Basic.parameterPolynomial sourceParameter :=
      Fraction.Order.Arithmetic.mul_pos_direct (by decide) sourcePositive
    calc
      -windowBoundaryPolynomial threshold =
          -(Dirichlet.Critical.Cylinder.Basic.parameterPolynomial thresholdParameter * 9) := by
        rw [parameterPolynomial_thresholdParameter_scaled]
      _ < 9 * Dirichlet.Critical.Cylinder.Basic.parameterPolynomial sourceParameter -
          9 * Dirichlet.Critical.Cylinder.Basic.parameterPolynomial thresholdParameter := by
        apply Fraction.Order.Arithmetic.lt_of_sub_pos_direct
        calc
          (0 : Fraction.Rational) < 9 * Dirichlet.Critical.Cylinder.Basic.parameterPolynomial sourceParameter :=
            scaledSourcePositive
          _ =
              (9 * Dirichlet.Critical.Cylinder.Basic.parameterPolynomial sourceParameter -
                  9 * Dirichlet.Critical.Cylinder.Basic.parameterPolynomial thresholdParameter) -
                -(Dirichlet.Critical.Cylinder.Basic.parameterPolynomial thresholdParameter * 9) := by ring1
      _ = 9 * (Dirichlet.Critical.Cylinder.Basic.parameterPolynomial sourceParameter -
          Dirichlet.Critical.Cylinder.Basic.parameterPolynomial thresholdParameter) := by ring1
  calc
    -windowBoundaryPolynomial threshold <
        9 * (Dirichlet.Critical.Cylinder.Basic.parameterPolynomial sourceParameter -
          Dirichlet.Critical.Cylinder.Basic.parameterPolynomial thresholdParameter) := firstStrict
    _ = 9 * (thresholdParameter - sourceParameter) *
        (4 - thresholdParameter - sourceParameter) := by
      rw [parameterPolynomial_difference]
      ring1
    _ ≤ 9 * (thresholdParameter - sourceParameter) * 4 :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct factorLeFour
        (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
          differencePositive.le)
    _ = 12 * ((threshold / 3) * 3 -
        3 * Dirichlet.Critical.Parameter.pellParameter stage) := by
      dsimp only [thresholdParameter, sourceParameter, -eq_self, -iff_self]
      ring1
    _ = 12 * (threshold - 3 * Dirichlet.Critical.Parameter.pellParameter stage) := by
      rw [thresholdParameter_mul_three]

/-- Negating the boundary polynomial at a sharper threshold gives a positive rational clearance. -/
private theorem boundaryNegation_pos
    {threshold : Fraction.Rational} (certificate : IsSharperWindowThreshold threshold) :
    0 < -windowBoundaryPolynomial threshold := by
  calc
    (0 : Fraction.Rational) < 0 - windowBoundaryPolynomial threshold :=
      Fraction.Order.Arithmetic.sub_pos_direct certificate.2.2
    _ = -windowBoundaryPolynomial threshold := by ring1

/-- A wholly explicit stage index.  The first summand makes the Pell defect
small enough; `requestedScale` then moves the witness beyond any supplied
finite scale. -/
@[expose] def sharpnessStage (threshold :
  Fraction.Rational) (requestedScale : Nat) : Nat :=
  Data.Rat.Rounding.Floor.ceilNat
      (24 / -windowBoundaryPolynomial threshold) +
    requestedScale + 1

/-- The explicit sharpness stage exceeds the requested finite scale. -/
theorem requestedScale_lt_sharpnessStage
    (threshold : Fraction.Rational) (requestedScale : Nat) :
    requestedScale < sharpnessStage threshold requestedScale := by
  unfold sharpnessStage
  exact Nat.lt_succ_of_le
    (Nat.le_add_left requestedScale
      (Data.Rat.Rounding.Floor.ceilNat
        (24 / -windowBoundaryPolynomial threshold)))

/-- The selected stage makes the squared Pell denominator times boundary clearance exceed 24.

The rational ceiling in the stage formula supplies an explicit bound, which is transported through the finite Pell
denominator growth estimate. -/
private theorem sharpnessStage_clearance
    {threshold : Fraction.Rational} (certificate : IsSharperWindowThreshold threshold)
    (requestedScale : Nat) :
    (24 : Fraction.Rational) <
      -windowBoundaryPolynomial threshold *
        (Pell.FiniteBranch.pellDenominator (sharpnessStage threshold requestedScale) :
          Fraction.Rational) ^ 2 := by
  let delta := -windowBoundaryPolynomial threshold
  let ceiling := Data.Rat.Rounding.Floor.ceilNat (24 / delta)
  let stage := sharpnessStage threshold requestedScale
  have deltaPositive : 0 < delta := boundaryNegation_pos certificate
  have ratioNonnegative : (0 : Fraction.Rational) ≤ 24 / delta :=
    (Fraction.Order.Field.div_pos_direct (by decide) deltaPositive).le
  have ratioLeCeiling :
      24 / delta ≤ (ceiling : Fraction.Rational) :=
    Data.Rat.Rounding.Floor.le_natCast_ceilNat_of_nonneg ratioNonnegative
  have ceilingLtStageNat : ceiling < stage := by
    dsimp only [ceiling, stage, delta, sharpnessStage, -eq_self, -iff_self]
    exact Nat.lt_succ_of_le
      (Nat.le_add_right
        (Data.Rat.Rounding.Floor.ceilNat
          (24 / -windowBoundaryPolynomial threshold)) requestedScale)
  have ceilingLtStage :
      (ceiling : Fraction.Rational) < (stage : Fraction.Rational) :=
    Fraction.Cast.Order.natCast_lt_direct ceilingLtStageNat
  have ratioLtStage : 24 / delta < (stage : Fraction.Rational) :=
    ratioLeCeiling.trans_lt ceilingLtStage
  have twentyFourLtStageDelta :
      (24 : Fraction.Rational) < (stage : Fraction.Rational) * delta :=
    (Fraction.Order.Field.div_lt_iff_pos deltaPositive).1 ratioLtStage
  have stageLtDenominatorNat :
      stage < Pell.FiniteBranch.pellDenominator stage := Pell.FiniteBranch.stage_lt_pellDenominator stage
  have stageLtDenominator :
      (stage : Fraction.Rational) < (Pell.FiniteBranch.pellDenominator stage : Fraction.Rational) :=
    Fraction.Cast.Order.natCast_lt_direct stageLtDenominatorNat
  have stageDeltaLtDenominatorDelta :
      (stage : Fraction.Rational) * delta <
        (Pell.FiniteBranch.pellDenominator stage : Fraction.Rational) * delta :=
    Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct
      stageLtDenominator deltaPositive
  have denominatorLeSquareNat :
      Pell.FiniteBranch.pellDenominator stage ≤ Nat.pow (Pell.FiniteBranch.pellDenominator stage) 2 := by
    have positive := Pell.FiniteBranch.pellDenominator_pos stage
    change Pell.FiniteBranch.pellDenominator stage ≤
      (1 * Pell.FiniteBranch.pellDenominator stage) * Pell.FiniteBranch.pellDenominator stage
    rw [Nat.one_mul]
    exact Nat.le_mul_of_pos_right (Pell.FiniteBranch.pellDenominator stage) positive
  have denominatorLeSquare :
      (Pell.FiniteBranch.pellDenominator stage : Fraction.Rational) ≤
        (Nat.pow (Pell.FiniteBranch.pellDenominator stage) 2 : Nat) :=
    Fraction.Cast.Order.natCast_le_direct denominatorLeSquareNat
  have denominatorDeltaLeSquareDelta :
      (Pell.FiniteBranch.pellDenominator stage : Fraction.Rational) * delta ≤
        (Pell.FiniteBranch.pellDenominator stage : Fraction.Rational) ^ 2 * delta := by
    have castPower :
        (Nat.pow (Pell.FiniteBranch.pellDenominator stage) 2 : Nat) =
          (Pell.FiniteBranch.pellDenominator stage : Fraction.Rational) ^ 2 := by
      change (((1 * Pell.FiniteBranch.pellDenominator stage) * Pell.FiniteBranch.pellDenominator stage : Nat) :
        Fraction.Rational) = _
      rw [Nat.one_mul, Algebra.NatCast.mul]
      ring1
    rw [← castPower]
    exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      denominatorLeSquare deltaPositive.le
  calc
    (24 : Fraction.Rational) <
        (sharpnessStage threshold requestedScale : Fraction.Rational) *
          -windowBoundaryPolynomial threshold := by
      simpa only [stage, delta, -eq_self, -iff_self] using twentyFourLtStageDelta
    _ < (Pell.FiniteBranch.pellDenominator (sharpnessStage threshold requestedScale) :
          Fraction.Rational) * -windowBoundaryPolynomial threshold :=
      by simpa only [stage, delta, -eq_self, -iff_self] using stageDeltaLtDenominatorDelta
    _ ≤ (Pell.FiniteBranch.pellDenominator (sharpnessStage threshold requestedScale) :
          Fraction.Rational) ^ 2 * -windowBoundaryPolynomial threshold :=
      by simpa only [stage, delta, -eq_self, -iff_self] using denominatorDeltaLeSquareDelta
    _ = -windowBoundaryPolynomial threshold *
        (Pell.FiniteBranch.pellDenominator (sharpnessStage threshold requestedScale) :
          Fraction.Rational) ^ 2 := by ring1

/-- Sufficient denominator clearance makes 24 times the Pell parameter defect smaller than the boundary clearance. -/
private theorem
  scaledPellDefect_lt_boundaryNegation
    {threshold : Fraction.Rational} (stage : Nat)
    (clearance :
      (24 : Fraction.Rational) < -windowBoundaryPolynomial threshold *
        (Pell.FiniteBranch.pellDenominator stage : Fraction.Rational) ^ 2) :
    24 * Dirichlet.Critical.Cylinder.Basic.parameterPolynomial (Dirichlet.Critical.Parameter.pellParameter stage) <
      -windowBoundaryPolynomial threshold := by
  have denominatorSquarePositive :
      0 < (Pell.FiniteBranch.pellDenominator stage : Fraction.Rational) ^ 2 := by
    simpa only [pow_two, -eq_self, -iff_self] using
      Fraction.Order.Arithmetic.mul_pos_direct
        (Dirichlet.Critical.Parameter.pellDenominator_cast_pos stage)
          (Dirichlet.Critical.Parameter.pellDenominator_cast_pos stage)
  apply Fraction.Order.Arithmetic.lt_of_mul_lt_mul_right_direct
    (c := (Pell.FiniteBranch.pellDenominator stage : Fraction.Rational) ^ 2)
  · calc
      (24 * Dirichlet.Critical.Cylinder.Basic.parameterPolynomial (Dirichlet.Critical.Parameter.pellParameter stage)) *
            (Pell.FiniteBranch.pellDenominator stage : Fraction.Rational) ^ 2 =
          24 * (Dirichlet.Critical.Cylinder.Basic.parameterPolynomial (Dirichlet.Critical.Parameter.pellParameter stage)
            *
            (Pell.FiniteBranch.pellDenominator stage : Fraction.Rational) ^ 2) := by ring1
      _ = 24 := by rw [Dirichlet.Critical.Parameter.parameterPolynomial_pellParameter_scaled]; ring1
      _ < -windowBoundaryPolynomial threshold *
          (Pell.FiniteBranch.pellDenominator stage : Fraction.Rational) ^ 2 := clearance
  · exact denominatorSquarePositive

/-- The critical gap is below a sharper threshold once the explicit denominator clearance holds.

The scaled Pell defect and boundary margin estimates control the exact rational gap without introducing a limiting
endpoint. -/
private theorem
  criticalGap_lt_sharperThreshold_of_clearance
    {threshold : Fraction.Rational} (certificate : IsSharperWindowThreshold threshold)
    (stage : Nat)
    (clearance :
      (24 : Fraction.Rational) < -windowBoundaryPolynomial threshold *
        (Pell.FiniteBranch.pellDenominator stage : Fraction.Rational) ^ 2) :
    Dirichlet.Critical.Cylinder.Basic.criticalGap (Dirichlet.Critical.Parameter.pellParameter stage) < threshold := by
  have scaledDefect := scaledPellDefect_lt_boundaryNegation stage clearance
  have boundaryMargin := boundaryClearance_lt_twelve_parameterMargin
    certificate stage
  have twiceDefectLtMargin :
      2 * Dirichlet.Critical.Cylinder.Basic.parameterPolynomial (Dirichlet.Critical.Parameter.pellParameter stage) <
        threshold - 3 * Dirichlet.Critical.Parameter.pellParameter stage := by
    apply Fraction.Order.Arithmetic.lt_of_mul_lt_mul_right_direct (c := 12)
    · calc
        (2 * Dirichlet.Critical.Cylinder.Basic.parameterPolynomial (Dirichlet.Critical.Parameter.pellParameter stage)) *
          12 =
            24 * Dirichlet.Critical.Cylinder.Basic.parameterPolynomial (Dirichlet.Critical.Parameter.pellParameter
              stage) := by ring1
        _ < -windowBoundaryPolynomial threshold := scaledDefect
        _ < 12 * (threshold - 3 * Dirichlet.Critical.Parameter.pellParameter stage) := boundaryMargin
        _ = (threshold - 3 * Dirichlet.Critical.Parameter.pellParameter stage) * 12 := by ring1
    · decide
  calc
    Dirichlet.Critical.Cylinder.Basic.criticalGap (Dirichlet.Critical.Parameter.pellParameter stage) <
        3 * Dirichlet.Critical.Parameter.pellParameter stage +
          2 * Dirichlet.Critical.Cylinder.Basic.parameterPolynomial (Dirichlet.Critical.Parameter.pellParameter stage)
            :=
      criticalGap_lt_three_parameter_add_two_defects
        (Dirichlet.Critical.Parameter.pellParameter_isCritical stage)
    _ < 3 * Dirichlet.Critical.Parameter.pellParameter stage +
        (threshold - 3 * Dirichlet.Critical.Parameter.pellParameter stage) :=
      Fraction.Order.Arithmetic.add_lt_add_left_direct
        twiceDefectLtMargin (3 * Dirichlet.Critical.Parameter.pellParameter stage)
    _ = threshold := by ring1

/-- At the explicit stage selected from a sharper rational threshold, the
normalized critical gap is already strictly below that threshold. -/
theorem criticalGap_lt_sharperThreshold
    {threshold : Fraction.Rational} (certificate : IsSharperWindowThreshold threshold)
    (requestedScale : Nat) :
    Dirichlet.Critical.Cylinder.Basic.criticalGap
        (Dirichlet.Critical.Parameter.pellParameter (sharpnessStage threshold
          requestedScale)) < threshold :=
  criticalGap_lt_sharperThreshold_of_clearance certificate
    (sharpnessStage threshold requestedScale)
    (sharpnessStage_clearance certificate requestedScale)

/-- The explicitly selected Pell denominator lies beyond the requested
finite scale. -/
theorem requestedScale_lt_criticalDenominator
    (threshold : Fraction.Rational) (requestedScale : Nat) :
    requestedScale <
      Pell.FiniteBranch.pellDenominator (sharpnessStage threshold requestedScale) :=
  (requestedScale_lt_sharpnessStage threshold requestedScale).trans
    (Pell.FiniteBranch.stage_lt_pellDenominator (sharpnessStage threshold requestedScale))

/-- The actual upper-pair denominator quadrance also lies beyond the supplied
natural scale. -/
theorem
  requestedScale_lt_criticalUpperDenominatorQuadrance
    (threshold : Fraction.Rational) (requestedScale : Nat) :
    requestedScale < Best.Error.denominatorQuadrance
      (Dirichlet.Critical.Pair.criticalUpperPair (sharpnessStage threshold requestedScale))
        := by
  let stage := sharpnessStage threshold requestedScale
  have requestedLtDenominator : requestedScale < Pell.FiniteBranch.pellDenominator stage := by
    simpa only [stage, -eq_self, -iff_self] using
      requestedScale_lt_criticalDenominator threshold requestedScale
  have denominatorPositive := Pell.FiniteBranch.pellDenominator_pos stage
  have denominatorLeSquare :
      Pell.FiniteBranch.pellDenominator stage ≤ Pell.FiniteBranch.pellDenominator stage ^ 2 := by
    simpa only [pow_two, -eq_self, -iff_self] using
      Nat.le_mul_of_pos_right (Pell.FiniteBranch.pellDenominator stage) denominatorPositive
  have squarePositive : 0 < Pell.FiniteBranch.pellDenominator stage ^ 2 := by
    simpa only [pow_two, -eq_self, -iff_self] using
      Nat.mul_pos denominatorPositive denominatorPositive
  rw [show Dirichlet.Critical.Pair.criticalUpperPair (sharpnessStage threshold
    requestedScale) =
      Dirichlet.Critical.Pair.criticalUpperPair stage by rfl,
    Dirichlet.Critical.Pair.criticalUpper_denominatorQuadrance]
  exact requestedLtDenominator.trans_le denominatorLeSquare |>.trans (by
    simpa only [Nat.one_mul, -eq_self, -iff_self] using
      Nat.mul_lt_mul_of_pos_right (show 1 < 4 by decide) squarePositive)

/-- The actual squared Dirichlet window of the critical pair is positive. -/
private theorem criticalDirichletWindow_pos
  (stage : Nat) :
    0 < Dirichlet.Window.SourceBound.dirichletWindowQuadrance (Dirichlet.Critical.Pair.criticalSource stage).value
      (Dirichlet.Critical.Pair.criticalLowerPair stage) (Dirichlet.Critical.Pair.criticalUpperPair stage) := open
        Purelib.Data in by
  apply Fraction.Order.Arithmetic.pos_of_mul_pos_right_direct
  · calc
      (0 : Fraction.Rational) < 1 := by decide
      _ = Dirichlet.Critical.Cylinder.Basic.criticalGap (Dirichlet.Critical.Parameter.pellParameter stage) *
          Dirichlet.Window.SourceBound.dirichletWindowQuadrance (Dirichlet.Critical.Pair.criticalSource stage).value
            (Dirichlet.Critical.Pair.criticalLowerPair stage) (Dirichlet.Critical.Pair.criticalUpperPair stage) :=
        (criticalGap_mul_dirichletWindow stage).symm
  · unfold Dirichlet.Critical.Cylinder.Basic.criticalGap
    exact Gaussian.Norm.Basic.normSq_nonneg _

/-- Every sharper displayed rational threshold fails on an explicitly
constructed consecutive-best window beyond every supplied finite scale. -/
theorem
  one_lt_sharperThreshold_mul_criticalWindow
    {threshold : Fraction.Rational} (certificate : IsSharperWindowThreshold threshold)
    (requestedScale : Nat) :
    1 < threshold *
      Dirichlet.Window.SourceBound.dirichletWindowQuadrance
        (Dirichlet.Critical.Pair.criticalSource (sharpnessStage threshold
          requestedScale)).value
        (Dirichlet.Critical.Pair.criticalLowerPair (sharpnessStage threshold
          requestedScale))
        (Dirichlet.Critical.Pair.criticalUpperPair (sharpnessStage threshold
          requestedScale)) := by
  let stage := sharpnessStage threshold requestedScale
  have gapStrict : Dirichlet.Critical.Cylinder.Basic.criticalGap (Dirichlet.Critical.Parameter.pellParameter stage) <
    threshold := by
    simpa only [stage, -eq_self, -iff_self] using
      criticalGap_lt_sharperThreshold certificate requestedScale
  have windowPositive := criticalDirichletWindow_pos stage
  calc
    (1 : Fraction.Rational) = Dirichlet.Critical.Cylinder.Basic.criticalGap (Dirichlet.Critical.Parameter.pellParameter
      stage) *
        Dirichlet.Window.SourceBound.dirichletWindowQuadrance (Dirichlet.Critical.Pair.criticalSource stage).value
          (Dirichlet.Critical.Pair.criticalLowerPair stage) (Dirichlet.Critical.Pair.criticalUpperPair stage) :=
      (criticalGap_mul_dirichletWindow stage).symm
    _ < threshold *
        Dirichlet.Window.SourceBound.dirichletWindowQuadrance (Dirichlet.Critical.Pair.criticalSource stage).value
          (Dirichlet.Critical.Pair.criticalLowerPair stage) (Dirichlet.Critical.Pair.criticalUpperPair stage) :=
      Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct
        gapStrict windowPositive

/-- Bundled paper-facing conclusion: the explicit denominator exceeds the
request, its endpoints are consecutive best approximations, and the proposed
sharper window inequality fails. -/
theorem criticalWindowSharpness
    {threshold : Fraction.Rational} (certificate : IsSharperWindowThreshold threshold)
    (requestedScale : Nat) :
    requestedScale < Best.Error.denominatorQuadrance
        (Dirichlet.Critical.Pair.criticalUpperPair (sharpnessStage threshold
          requestedScale)) ∧
      Best.Consecutive.Basic.AreConsecutiveBest
        (Dirichlet.Critical.Pair.criticalSource (sharpnessStage threshold
          requestedScale)).value
        (Dirichlet.Critical.Pair.criticalLowerPair (sharpnessStage threshold
          requestedScale))
        (Dirichlet.Critical.Pair.criticalUpperPair (sharpnessStage threshold
          requestedScale)) ∧
      1 < threshold *
        Dirichlet.Window.SourceBound.dirichletWindowQuadrance
          (Dirichlet.Critical.Pair.criticalSource (sharpnessStage threshold
            requestedScale)).value
          (Dirichlet.Critical.Pair.criticalLowerPair (sharpnessStage threshold
            requestedScale))
          (Dirichlet.Critical.Pair.criticalUpperPair (sharpnessStage threshold
            requestedScale)) := by
  exact ⟨requestedScale_lt_criticalUpperDenominatorQuadrance
      threshold requestedScale,
    Dirichlet.Critical.Pair.criticalPairs_areConsecutiveBest _,
    one_lt_sharperThreshold_mul_criticalWindow certificate requestedScale⟩

end Purelib.NumberTheory.Approximation.Dirichlet.Critical.Sharpness

end
