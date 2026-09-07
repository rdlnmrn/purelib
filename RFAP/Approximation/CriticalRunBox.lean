import mathlib.Data.ConstructiveList
import mathlib.Tactic.QuotientFreeOmega
import mathlib.Tactic.QuotientFreeRing
import RFAP.Approximation.CriticalBadWindowRun
import RFAP.Geometry.Boxes

/-!
# Rational robustness boxes for finite critical runs

This module begins the robust-box upgrade of the exact same-source critical
run.  A strict bad-window violation has an explicit positive rational
clearance.  A finite weighted two-leg estimate turns that clearance into an
executable positive squared-distance budget for perturbing the displayed
source while retaining the strict threshold violation.
-/

namespace RFAP.CriticalRunBox

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Pair := RFAP.HurwitzRational.ConvergentPair
abbrev Box := RFAP.Boxes.Box
abbrev BadWindow := RFAP.DynamicalSharpness.BadWindow

open RFAP.BestApproximation
open RFAP.ConstructiveGaussianHeight.GaussianInt

/-- The exact left-hand side of a bad window's strict threshold inequality. -/
def violationValue
    {threshold : Coordinate} {requestedScale : Nat}
    (window : BadWindow threshold requestedScale) : Coordinate :=
  threshold * (denominatorQuadrance window.upper : Coordinate) *
    errorQuadrance window.source.value window.lower

/-- Positive rational slack in the exact bad-window inequality. -/
def violationClearance
    {threshold : Coordinate} {requestedScale : Nat}
    (window : BadWindow threshold requestedScale) : Coordinate :=
  violationValue window - 1

theorem violationValue_gt_one
    {threshold : Coordinate} {requestedScale : Nat}
    (window : BadWindow threshold requestedScale) :
    1 < violationValue window := by
  calc
    (1 : Coordinate) < threshold *
        ((denominatorQuadrance window.upper : Coordinate) *
          errorQuadrance window.source.value window.lower) := by
      simpa only [dirichletWindowQuadrance] using window.violates
    _ = violationValue window := by
      unfold violationValue
      ring1

theorem violationClearance_pos
    {threshold : Coordinate} {requestedScale : Nat}
    (window : BadWindow threshold requestedScale) :
    0 < violationClearance window :=
  RFAP.ConstructiveFraction.sub_pos_direct (violationValue_gt_one window)

/-- Integer weight large enough to make the weighted perturbation estimate
arbitrarily close to its exact-source value. -/
def stabilityWeightNat
    {threshold : Coordinate} {requestedScale : Nat}
    (window : BadWindow threshold requestedScale) : Nat :=
  RFAP.ConstructiveFraction.ceilNat (2 / violationClearance window) + 1

def stabilityWeight
    {threshold : Coordinate} {requestedScale : Nat}
    (window : BadWindow threshold requestedScale) : Coordinate :=
  (stabilityWeightNat window : Coordinate)

theorem stabilityWeight_pos
    {threshold : Coordinate} {requestedScale : Nat}
    (window : BadWindow threshold requestedScale) :
    0 < stabilityWeight window := by
  apply RFAP.ConstructiveFraction.natCast_pos_direct
  unfold stabilityWeightNat
  exact Nat.zero_lt_succ _

theorem two_lt_stabilityWeight_mul_clearance
    {threshold : Coordinate} {requestedScale : Nat}
    (window : BadWindow threshold requestedScale) :
    (2 : Coordinate) <
      stabilityWeight window * violationClearance window := by
  have clearancePositive := violationClearance_pos window
  have ratioNonnegative :
      (0 : Coordinate) ≤ 2 / violationClearance window :=
    (RFAP.ConstructiveFraction.div_pos_direct (by decide)
      clearancePositive).le
  have ratioLeCeiling :
      2 / violationClearance window ≤
        (RFAP.ConstructiveFraction.ceilNat
          (2 / violationClearance window) : Coordinate) :=
    RFAP.ConstructiveFraction.le_natCast_ceilNat_of_nonneg ratioNonnegative
  have ceilingLtWeightNat :
      RFAP.ConstructiveFraction.ceilNat
          (2 / violationClearance window) < stabilityWeightNat window := by
    unfold stabilityWeightNat
    exact Nat.lt_add_one_iff.mpr (Nat.le_refl _)
  have ceilingLtWeight :
      (RFAP.ConstructiveFraction.ceilNat
          (2 / violationClearance window) : Coordinate) <
        stabilityWeight window :=
    RFAP.ConstructiveFraction.natCast_lt_direct ceilingLtWeightNat
  have ratioLtWeight :
      2 / violationClearance window < stabilityWeight window :=
    ratioLeCeiling.trans_lt ceilingLtWeight
  exact (RFAP.ConstructiveFraction.div_lt_iff_pos clearancePositive).1
    ratioLtWeight

/-- Remaining scaled strictness after paying for the weighted normalization. -/
def stabilityMargin
    {threshold : Coordinate} {requestedScale : Nat}
    (window : BadWindow threshold requestedScale) : Coordinate :=
  stabilityWeight window * violationClearance window - 1

theorem stabilityMargin_pos
    {threshold : Coordinate} {requestedScale : Nat}
    (window : BadWindow threshold requestedScale) :
    0 < stabilityMargin window := by
  apply RFAP.ConstructiveFraction.sub_pos_direct
  exact (show (1 : Coordinate) < 2 by decide).trans
    (two_lt_stabilityWeight_mul_clearance window)

private theorem threshold_pos
    {threshold : Coordinate} {requestedScale : Nat}
    (window : BadWindow threshold requestedScale) : 0 < threshold := by
  have exactViolation := window.violates
  have windowNonnegative :
      (0 : Coordinate) ≤ dirichletWindowQuadrance window.source.value
        window.lower window.upper := by
    unfold dirichletWindowQuadrance
    exact RFAP.ConstructiveFraction.mul_nonneg_direct
      (RFAP.ConstructiveFraction.natCast_le_direct (Nat.zero_le _))
      (RFAP.ConstructiveGaussian.Gaussian.normSq_nonneg _)
  by_contra thresholdSmall
  have thresholdNonpositive : threshold ≤ 0 := le_of_not_gt thresholdSmall
  have productNonpositive :
      threshold * dirichletWindowQuadrance window.source.value
        window.lower window.upper ≤ 0 := by
    rw [show (0 : Coordinate) = 0 *
        dirichletWindowQuadrance window.source.value
          window.lower window.upper by ring1]
    exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
      thresholdNonpositive windowNonnegative
  exact (not_lt_of_ge productNonpositive
    ((show (0 : Coordinate) < 1 by decide).trans exactViolation)).elim

private theorem upperQuadrance_pos
    {threshold : Coordinate} {requestedScale : Nat}
    (window : BadWindow threshold requestedScale) :
    0 < denominatorQuadrance window.upper :=
  (Nat.zero_le requestedScale).trans_lt window.beyondScale

/-- Coefficient multiplying source squared distance in the weighted loss. -/
def stabilityCoefficient
    {threshold : Coordinate} {requestedScale : Nat}
    (window : BadWindow threshold requestedScale) : Coordinate :=
  threshold * (denominatorQuadrance window.upper : Coordinate) *
    stabilityWeight window * (1 + stabilityWeight window) *
      (denominatorQuadrance window.lower : Coordinate)

theorem stabilityCoefficient_pos
    {threshold : Coordinate} {requestedScale : Nat}
    (window : BadWindow threshold requestedScale) :
    0 < stabilityCoefficient window := by
  have lowerPositive : 0 < denominatorQuadrance window.lower :=
    window.consecutive.1.1
      |> fun nonzero => RFAP.ConstructiveGaussianHeight.GaussianInt.normNat_pos
        nonzero
  unfold stabilityCoefficient
  exact RFAP.ConstructiveFraction.mul_pos_direct
    (RFAP.ConstructiveFraction.mul_pos_direct
      (RFAP.ConstructiveFraction.mul_pos_direct
        (RFAP.ConstructiveFraction.mul_pos_direct
          (threshold_pos window)
          (RFAP.ConstructiveFraction.natCast_pos_direct
            (upperQuadrance_pos window)))
        (stabilityWeight_pos window))
      ((show (0 : Coordinate) < 1 by decide).trans_le
        (le_add_of_nonneg_right (stabilityWeight_pos window).le)))
    (RFAP.ConstructiveFraction.natCast_pos_direct lowerPositive)

/-- Positive squared source-distance budget retaining the strict violation. -/
def allowedSourceDistanceSq
    {threshold : Coordinate} {requestedScale : Nat}
    (window : BadWindow threshold requestedScale) : Coordinate :=
  stabilityMargin window / (2 * stabilityCoefficient window)

theorem allowedSourceDistanceSq_pos
    {threshold : Coordinate} {requestedScale : Nat}
    (window : BadWindow threshold requestedScale) :
    0 < allowedSourceDistanceSq window := by
  unfold allowedSourceDistanceSq
  exact RFAP.ConstructiveFraction.div_pos_direct
    (stabilityMargin_pos window)
    (RFAP.ConstructiveFraction.mul_pos_direct (by decide)
      (stabilityCoefficient_pos window))

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

private theorem exactError_sum_identity
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

/-- The explicit distance budget is sound: every rational source within it
retains the strict threshold violation for this fixed displayed pair. -/
theorem one_lt_threshold_mul_window_of_distance
    {threshold : Coordinate} {requestedScale : Nat}
    (window : BadWindow threshold requestedScale) (sample : Gaussian)
    (distanceSmall :
      RFAP.ConstructiveGaussian.Gaussian.normSq
          (sample - window.source.value) <
        allowedSourceDistanceSq window) :
    1 < threshold * dirichletWindowQuadrance sample
      window.lower window.upper := by
  let center := window.source.value
  let exactError := RFAP.HurwitzApproximation.error center window.lower
  let sampleError := RFAP.HurwitzApproximation.error sample window.lower
  let displacement :=
    (sample - center) * toGaussian window.lower.denominator
  let upperScale := (denominatorQuadrance window.upper : Coordinate)
  let lowerScale := (denominatorQuadrance window.lower : Coordinate)
  let coefficient := threshold * upperScale
  let weight := stabilityWeight window
  let loss := coefficient * weight * (1 + weight) *
    RFAP.ConstructiveGaussian.Gaussian.normSq displacement
  have coefficientPositive : 0 < coefficient :=
    RFAP.ConstructiveFraction.mul_pos_direct (threshold_pos window)
      (RFAP.ConstructiveFraction.natCast_pos_direct
        (upperQuadrance_pos window))
  have weightPositive : 0 < weight := by
    simpa only [weight] using stabilityWeight_pos window
  have onePlusWeightPositive : (0 : Coordinate) < 1 + weight :=
    (show (0 : Coordinate) < 1 by decide).trans_le
      (le_add_of_nonneg_right weightPositive.le)
  have stabilityCoefficientIdentity :
      stabilityCoefficient window =
        coefficient * weight * (1 + weight) * lowerScale := by
    unfold stabilityCoefficient
    dsimp only [coefficient, weight, upperScale, lowerScale]
  have coefficientTimesDistanceLtMargin :
      stabilityCoefficient window *
          RFAP.ConstructiveGaussian.Gaussian.normSq (sample - center) <
        stabilityMargin window := by
    have allowedPositive := allowedSourceDistanceSq_pos window
    have coefficientPositive' := stabilityCoefficient_pos window
    calc
      stabilityCoefficient window *
          RFAP.ConstructiveGaussian.Gaussian.normSq (sample - center) <
        stabilityCoefficient window * allowedSourceDistanceSq window :=
          RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
            coefficientPositive' (by
              simpa only [center] using distanceSmall)
      _ = allowedSourceDistanceSq window * stabilityCoefficient window :=
        RFAP.ConstructiveFraction.mul_comm _ _
      _ < allowedSourceDistanceSq window *
          (2 * stabilityCoefficient window) := by
        apply RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
          allowedPositive
        calc
          stabilityCoefficient window =
              1 * stabilityCoefficient window := by ring1
          _ < 2 * stabilityCoefficient window :=
            RFAP.ConstructiveFraction.mul_lt_mul_of_pos_right_direct
              (by decide) coefficientPositive'
      _ = stabilityMargin window := by
        unfold allowedSourceDistanceSq
        exact RFAP.ConstructiveFraction.div_mul_cancel_of_ne _ _
          (RFAP.ConstructiveFraction.mul_ne_zero_direct
            (by decide) coefficientPositive'.ne')
  have lossLtMargin : loss < stabilityMargin window := by
    dsimp only [loss]
    rw [show RFAP.ConstructiveGaussian.Gaussian.normSq displacement =
        RFAP.ConstructiveGaussian.Gaussian.normSq (sample - center) *
          lowerScale by
      dsimp only [displacement, lowerScale, center]
      exact perturbation_normSq _ _ _]
    calc
      coefficient * weight * (1 + weight) *
          (RFAP.ConstructiveGaussian.Gaussian.normSq (sample - center) *
            lowerScale) =
        stabilityCoefficient window *
          RFAP.ConstructiveGaussian.Gaussian.normSq (sample - center) := by
            rw [stabilityCoefficientIdentity]
            ring1
      _ < stabilityMargin window := coefficientTimesDistanceLtMargin
  have exactValueIdentity :
      violationValue window =
        coefficient * RFAP.ConstructiveGaussian.Gaussian.normSq exactError := by
    unfold violationValue errorQuadrance
    dsimp only [coefficient, exactError, center, upperScale]
  have marginIdentity :
      stabilityMargin window =
        coefficient * weight *
            RFAP.ConstructiveGaussian.Gaussian.normSq exactError -
          (1 + weight) := by
    unfold stabilityMargin violationClearance
    rw [exactValueIdentity]
    dsimp only [weight]
    ring1
  have weighted := RFAP.DirichletWindow.weighted_normSq_add_le
    sampleError (-displacement) 1 weight
  have weightedErrorBound :
      weight * RFAP.ConstructiveGaussian.Gaussian.normSq exactError ≤
        (1 + weight) *
            RFAP.ConstructiveGaussian.Gaussian.normSq sampleError +
          weight * (1 + weight) *
            RFAP.ConstructiveGaussian.Gaussian.normSq displacement := by
    rw [exactError_sum_identity center sample window.lower,
      RFAP.ConstructiveGaussian.Gaussian.normSq_neg] at weighted
    simpa only [sampleError, displacement, exactError] using (show
      weight * RFAP.ConstructiveGaussian.Gaussian.normSq exactError ≤
        (1 + weight) *
            RFAP.ConstructiveGaussian.Gaussian.normSq sampleError +
          weight * (1 + weight) *
            RFAP.ConstructiveGaussian.Gaussian.normSq displacement by
      calc
        weight * RFAP.ConstructiveGaussian.Gaussian.normSq exactError =
            1 * weight *
              RFAP.ConstructiveGaussian.Gaussian.normSq exactError := by ring1
        _ ≤ 1 * (1 + weight) *
              RFAP.ConstructiveGaussian.Gaussian.normSq sampleError +
            weight * (1 + weight) *
              RFAP.ConstructiveGaussian.Gaussian.normSq displacement :=
          weighted
        _ = _ := by ring1)
  have scaledWeighted :
      coefficient * weight *
          RFAP.ConstructiveGaussian.Gaussian.normSq exactError ≤
        coefficient * (1 + weight) *
            RFAP.ConstructiveGaussian.Gaussian.normSq sampleError + loss := by
    have scaled :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        weightedErrorBound coefficientPositive.le
    dsimp only [loss]
    calc
      coefficient * weight *
          RFAP.ConstructiveGaussian.Gaussian.normSq exactError =
        coefficient *
          (weight * RFAP.ConstructiveGaussian.Gaussian.normSq exactError) := by
            ring1
      _ ≤ coefficient *
          ((1 + weight) *
              RFAP.ConstructiveGaussian.Gaussian.normSq sampleError +
            weight * (1 + weight) *
              RFAP.ConstructiveGaussian.Gaussian.normSq displacement) := scaled
      _ = coefficient * (1 + weight) *
            RFAP.ConstructiveGaussian.Gaussian.normSq sampleError +
          coefficient * weight * (1 + weight) *
            RFAP.ConstructiveGaussian.Gaussian.normSq displacement := by ring1
  have exactStrictWithLoss :
      (1 + weight) + loss <
        coefficient * weight *
          RFAP.ConstructiveGaussian.Gaussian.normSq exactError := by
    calc
      (1 + weight) + loss < (1 + weight) + stabilityMargin window :=
        RFAP.ConstructiveFraction.add_lt_add_left_direct lossLtMargin _
      _ = coefficient * weight *
          RFAP.ConstructiveGaussian.Gaussian.normSq exactError := by
        rw [marginIdentity]
        ring1
  have scaledViolationWithLoss :
      (1 + weight) + loss <
        (coefficient *
            RFAP.ConstructiveGaussian.Gaussian.normSq sampleError) *
          (1 + weight) + loss := by
    calc
      (1 + weight) + loss <
          coefficient * weight *
            RFAP.ConstructiveGaussian.Gaussian.normSq exactError :=
        exactStrictWithLoss
      _ ≤ coefficient * (1 + weight) *
            RFAP.ConstructiveGaussian.Gaussian.normSq sampleError + loss :=
        scaledWeighted
      _ = (coefficient *
            RFAP.ConstructiveGaussian.Gaussian.normSq sampleError) *
          (1 + weight) + loss := by ring1
  have scaledViolation :
      (1 : Coordinate) * (1 + weight) <
        (coefficient *
          RFAP.ConstructiveGaussian.Gaussian.normSq sampleError) *
            (1 + weight) := by
    have cancelled :=
      RFAP.ConstructiveFraction.lt_of_add_lt_add_right_direct
        scaledViolationWithLoss
    simpa only [RFAP.ConstructiveFraction.one_mul] using cancelled
  have violation :
      (1 : Coordinate) <
        coefficient *
          RFAP.ConstructiveGaussian.Gaussian.normSq sampleError :=
    RFAP.ConstructiveFraction.lt_of_mul_lt_mul_right_direct
      scaledViolation onePlusWeightPositive
  unfold dirichletWindowQuadrance errorQuadrance
  dsimp only [coefficient, sampleError, upperScale] at violation ⊢
  calc
    (1 : Coordinate) < threshold *
        (denominatorQuadrance window.upper : Coordinate) *
          RFAP.ConstructiveGaussian.Gaussian.normSq
            (RFAP.HurwitzApproximation.error sample window.lower) := violation
    _ = threshold *
        ((denominatorQuadrance window.upper : Coordinate) *
          RFAP.ConstructiveGaussian.Gaussian.normSq
            (RFAP.HurwitzApproximation.error sample window.lower)) := by
      ring1

/-- Positive rational side length chosen inside one violation's squared
distance budget. -/
def violationBoxRadius
    {threshold : Coordinate} {requestedScale : Nat}
    (window : BadWindow threshold requestedScale) : Coordinate :=
  min 1 (allowedSourceDistanceSq window * (1 / 4 : Coordinate))

theorem violationBoxRadius_pos
    {threshold : Coordinate} {requestedScale : Nat}
    (window : BadWindow threshold requestedScale) :
    0 < violationBoxRadius window := by
  unfold violationBoxRadius
  apply lt_min (by decide)
  exact RFAP.ConstructiveFraction.mul_pos_direct
    (allowedSourceDistanceSq_pos window) (by decide)

/-- Proper rational square extending up and right from the exact source. -/
def violationBox
    {threshold : Coordinate} {requestedScale : Nat}
    (window : BadWindow threshold requestedScale) : Box where
  xLower := window.source.value.re
  xUpper := window.source.value.re + violationBoxRadius window
  yLower := window.source.value.im
  yUpper := window.source.value.im + violationBoxRadius window
  x_valid := le_add_of_nonneg_right (violationBoxRadius_pos window).le
  y_valid := le_add_of_nonneg_right (violationBoxRadius_pos window).le

theorem violationBox_proper
    {threshold : Coordinate} {requestedScale : Nat}
    (window : BadWindow threshold requestedScale) :
    (violationBox window).Proper := by
  unfold RFAP.Boxes.Box.Proper violationBox
  constructor
  · calc
      window.source.value.re = window.source.value.re + 0 := by ring1
      _ < window.source.value.re + violationBoxRadius window :=
        RFAP.ConstructiveFraction.add_lt_add_left_direct
          (violationBoxRadius_pos window) _
  · calc
      window.source.value.im = window.source.value.im + 0 := by ring1
      _ < window.source.value.im + violationBoxRadius window :=
        RFAP.ConstructiveFraction.add_lt_add_left_direct
          (violationBoxRadius_pos window) _

@[simp] theorem violationBox_anchor
    {threshold : Coordinate} {requestedScale : Nat}
    (window : BadWindow threshold requestedScale) :
    (violationBox window).anchor = window.source.value := by
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;> rfl

theorem violationBox_diagonalSq
    {threshold : Coordinate} {requestedScale : Nat}
    (window : BadWindow threshold requestedScale) :
    (violationBox window).diagonalSq =
      2 * violationBoxRadius window ^ 2 := by
  unfold violationBox RFAP.Boxes.Box.diagonalSq
  ring1

private theorem two_mul_violationBoxRadius_sq_lt_allowed
    {threshold : Coordinate} {requestedScale : Nat}
    (window : BadWindow threshold requestedScale) :
    2 * violationBoxRadius window ^ 2 < allowedSourceDistanceSq window := by
  have radiusPositive := violationBoxRadius_pos window
  have radiusLeOne : violationBoxRadius window ≤ 1 :=
    min_le_left _ _
  have squareLeRadius :
      violationBoxRadius window ^ 2 ≤ violationBoxRadius window := by
    rw [pow_two]
    calc
      violationBoxRadius window * violationBoxRadius window ≤
          violationBoxRadius window * 1 :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          radiusLeOne radiusPositive.le
      _ = violationBoxRadius window := by ring1
  have radiusLeQuarter :
      violationBoxRadius window ≤
        allowedSourceDistanceSq window * (1 / 4 : Coordinate) :=
    min_le_right _ _
  have doubledRadiusBound :
      2 * violationBoxRadius window ≤
        allowedSourceDistanceSq window * (1 / 2 : Coordinate) := by
    calc
      2 * violationBoxRadius window ≤
          2 * (allowedSourceDistanceSq window * (1 / 4 : Coordinate)) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          radiusLeQuarter (by decide)
      _ = allowedSourceDistanceSq window *
          (2 * (1 / 4 : Coordinate)) := by ring1
      _ = allowedSourceDistanceSq window * (1 / 2 : Coordinate) := by
        rw [show (2 : Coordinate) * (1 / 4) = 1 / 2 by decide]
  calc
    2 * violationBoxRadius window ^ 2 ≤
        2 * violationBoxRadius window :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        squareLeRadius (by decide)
    _ ≤ allowedSourceDistanceSq window * (1 / 2 : Coordinate) :=
      doubledRadiusBound
    _ < allowedSourceDistanceSq window * 1 :=
      RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
        (allowedSourceDistanceSq_pos window) (by decide)
    _ = allowedSourceDistanceSq window := by ring1

/-- Every rational sample in the executable proper box retains this window's
strict sharper-threshold violation. -/
theorem violationBox_uniform
    {threshold : Coordinate} {requestedScale : Nat}
    (window : BadWindow threshold requestedScale) (sample : Gaussian)
    (inside : (violationBox window).Contains sample) :
    1 < threshold * dirichletWindowQuadrance sample
      window.lower window.upper := by
  apply one_lt_threshold_mul_window_of_distance window sample
  calc
    RFAP.ConstructiveGaussian.Gaussian.normSq
          (sample - window.source.value) =
        RFAP.ConstructiveGaussian.Gaussian.normSq
          (sample - (violationBox window).anchor) := by
      rw [violationBox_anchor]
    _ ≤ (violationBox window).diagonalSq :=
      (violationBox window).normSq_sub_anchor_le inside
    _ = 2 * violationBoxRadius window ^ 2 := violationBox_diagonalSq window
    _ < allowedSourceDistanceSq window :=
      two_mul_violationBoxRadius_sq_lt_allowed window

private def minimumViolationRadius
    {threshold : Coordinate} {requestedScale : Nat} :
    List (BadWindow threshold requestedScale) → Coordinate
  | [] => 1
  | window :: remaining =>
      min (violationBoxRadius window) (minimumViolationRadius remaining)

private theorem minimumViolationRadius_pos
    {threshold : Coordinate} {requestedScale : Nat}
    (windows : List (BadWindow threshold requestedScale)) :
    0 < minimumViolationRadius windows := by
  induction windows with
  | nil => exact (show (0 : Coordinate) < 1 by decide)
  | cons window remaining inductionHypothesis =>
      unfold minimumViolationRadius
      exact lt_min (violationBoxRadius_pos window) inductionHypothesis

private theorem minimumViolationRadius_le_of_mem
    {threshold : Coordinate} {requestedScale : Nat}
    {window : BadWindow threshold requestedScale}
    (windows : List (BadWindow threshold requestedScale))
    (member : window ∈ windows) :
    minimumViolationRadius windows ≤ violationBoxRadius window := by
  induction windows with
  | nil => cases member
  | cons head remaining inductionHypothesis =>
      rcases List.mem_cons.mp member with equal | tailMember
      · rw [equal]
        exact min_le_left _ _
      · exact (min_le_right _ _).trans
          (inductionHypothesis tailMember)

/-- Common positive side length obtained by a finite minimum over the run. -/
def runBoxRadius
    {threshold : Coordinate} {requestedScale count : Nat}
    (run : RFAP.CriticalBadWindowRun.SameSourceBadWindowRun
      threshold requestedScale count) : Coordinate :=
  minimumViolationRadius (run.windows.map Subtype.val)

theorem runBoxRadius_pos
    {threshold : Coordinate} {requestedScale count : Nat}
    (run : RFAP.CriticalBadWindowRun.SameSourceBadWindowRun
      threshold requestedScale count) :
    0 < runBoxRadius run :=
  minimumViolationRadius_pos _

private theorem runBoxRadius_le
    {threshold : Coordinate} {requestedScale count : Nat}
    (run : RFAP.CriticalBadWindowRun.SameSourceBadWindowRun
      threshold requestedScale count)
    (window : { window : BadWindow threshold requestedScale //
      window.source = run.source }) (member : window ∈ run.windows) :
    runBoxRadius run ≤ violationBoxRadius window.1 := by
  apply minimumViolationRadius_le_of_mem
  exact QuotientFreeList.mem_map.mpr ⟨window, member, rfl⟩

/-- One proper rational box shared by all exact windows in a finite run. -/
def runViolationBox
    {threshold : Coordinate} {requestedScale count : Nat}
    (run : RFAP.CriticalBadWindowRun.SameSourceBadWindowRun
      threshold requestedScale count) : Box where
  xLower := run.source.value.re
  xUpper := run.source.value.re + runBoxRadius run
  yLower := run.source.value.im
  yUpper := run.source.value.im + runBoxRadius run
  x_valid := le_add_of_nonneg_right (runBoxRadius_pos run).le
  y_valid := le_add_of_nonneg_right (runBoxRadius_pos run).le

theorem runViolationBox_proper
    {threshold : Coordinate} {requestedScale count : Nat}
    (run : RFAP.CriticalBadWindowRun.SameSourceBadWindowRun
      threshold requestedScale count) :
    (runViolationBox run).Proper := by
  unfold RFAP.Boxes.Box.Proper runViolationBox
  constructor
  · calc
      run.source.value.re = run.source.value.re + 0 := by ring1
      _ < run.source.value.re + runBoxRadius run :=
        RFAP.ConstructiveFraction.add_lt_add_left_direct
          (runBoxRadius_pos run) _
  · calc
      run.source.value.im = run.source.value.im + 0 := by ring1
      _ < run.source.value.im + runBoxRadius run :=
        RFAP.ConstructiveFraction.add_lt_add_left_direct
          (runBoxRadius_pos run) _

@[simp] theorem runViolationBox_anchor
    {threshold : Coordinate} {requestedScale count : Nat}
    (run : RFAP.CriticalBadWindowRun.SameSourceBadWindowRun
      threshold requestedScale count) :
    (runViolationBox run).anchor = run.source.value := by
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;> rfl

private theorem runViolationBox_refines
    {threshold : Coordinate} {requestedScale count : Nat}
    (run : RFAP.CriticalBadWindowRun.SameSourceBadWindowRun
      threshold requestedScale count)
    (window : { window : BadWindow threshold requestedScale //
      window.source = run.source }) (member : window ∈ run.windows) :
    (runViolationBox run).Refines (violationBox window.1) := by
  have sourceValueEqual := congrArg RFAP.HurwitzRational.Fraction.value
    window.property
  unfold RFAP.Boxes.Box.Refines runViolationBox violationBox
  dsimp only
  rw [sourceValueEqual]
  have radiusBound := runBoxRadius_le run window member
  have realUpper :
      run.source.value.re + runBoxRadius run ≤
        run.source.value.re + violationBoxRadius window.1 := by
    calc
      run.source.value.re + runBoxRadius run =
          runBoxRadius run + run.source.value.re := by ring1
      _ ≤ violationBoxRadius window.1 + run.source.value.re :=
        RFAP.ConstructiveFraction.add_le_add_right_direct radiusBound _
      _ = run.source.value.re + violationBoxRadius window.1 := by ring1
  have imaginaryUpper :
      run.source.value.im + runBoxRadius run ≤
        run.source.value.im + violationBoxRadius window.1 := by
    calc
      run.source.value.im + runBoxRadius run =
          runBoxRadius run + run.source.value.im := by ring1
      _ ≤ violationBoxRadius window.1 + run.source.value.im :=
        RFAP.ConstructiveFraction.add_le_add_right_direct radiusBound _
      _ = run.source.value.im + violationBoxRadius window.1 := by ring1
  exact ⟨le_rfl, realUpper, le_rfl, imaginaryUpper⟩

/-- Every displayed rational source sample in the common run box preserves
the strict threshold violation of every listed window. -/
theorem runViolationBox_uniform
    {threshold : Coordinate} {requestedScale count : Nat}
    (run : RFAP.CriticalBadWindowRun.SameSourceBadWindowRun
      threshold requestedScale count)
    (sample : Gaussian) (inside : (runViolationBox run).Contains sample)
    (window : { window : BadWindow threshold requestedScale //
      window.source = run.source }) (member : window ∈ run.windows) :
    1 < threshold * dirichletWindowQuadrance sample
      window.1.lower window.1.upper :=
  violationBox_uniform window.1 sample
    ((runViolationBox_refines run window member).contains inside)

/-- Returned robust-threshold half of a finite same-source run certificate.
Consecutive-best robustness is deliberately a separate remaining field of
work rather than being hidden in this record. -/
structure ViolationRobustRun
    (threshold : Coordinate) (requestedScale count : Nat) where
  exact : RFAP.CriticalBadWindowRun.SameSourceBadWindowRun
    threshold requestedScale count
  box : Box
  proper : box.Proper
  sourceAtAnchor : box.anchor = exact.source.value
  uniformViolation : ∀ sample : Gaussian, box.Contains sample →
    ∀ window, window ∈ exact.windows →
      1 < threshold * dirichletWindowQuadrance sample
        window.1.lower window.1.upper

/-- The executable arbitrary-length critical run carries a common proper
rational box on which all strict threshold violations persist. -/
def criticalViolationRobustRun
    {threshold : Coordinate}
    (certificate :
      RFAP.FiniteWindowSharpness.IsSharperWindowThreshold threshold)
    (requestedScale count : Nat) :
    ViolationRobustRun threshold requestedScale count := by
  let run := RFAP.CriticalBadWindowRun.criticalBadWindowRun
    certificate requestedScale count
  exact
    { exact := run
      box := runViolationBox run
      proper := runViolationBox_proper run
      sourceAtAnchor := runViolationBox_anchor run
      uniformViolation := fun sample inside window member =>
        runViolationBox_uniform run sample inside window member }

end RFAP.CriticalRunBox
