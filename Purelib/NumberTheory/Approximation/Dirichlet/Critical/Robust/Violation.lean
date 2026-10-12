module
import Purelib.Data.List.Membership
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.GaussianInt.Pair.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Cast
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Weighted
import Purelib.Data.GaussianInt.Fraction.Basic
import Purelib.Data.GaussianInt.Norm.Basic
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Rounding.Floor
import Purelib.Geometry.Rational.Box.Basic
public import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.NumberTheory.Approximation.Best.Error
public import Purelib.NumberTheory.Approximation.Dirichlet.Critical.Run
import Purelib.NumberTheory.Approximation.Dirichlet.Critical.Sharpness
import Purelib.NumberTheory.Approximation.Dirichlet.Sharpness.BadWindow
import Purelib.NumberTheory.Approximation.Dirichlet.Window.SourceBound

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.GaussianInt.Embedding
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Tactic.Ring

open Purelib.Data

open Purelib.Data.Rat

open Purelib

open Purelib.NumberTheory.Approximation

section
public section

/-!
# Rational robustness boxes for finite critical runs

This module begins the robust-box upgrade of the exact same-source critical
run.  A strict bad-window violation has an explicit positive rational
clearance.  A finite weighted two-leg estimate turns that clearance into an
executable positive squared-distance budget for perturbing the displayed
source while retaining the strict threshold violation.
-/

namespace Purelib.NumberTheory.Approximation.Dirichlet.Critical.Robust.Violation

/-- The exact left-hand side of a bad window's strict threshold inequality. -/
@[expose] def violationValue
    {threshold : Fraction.Rational} {requestedScale : Nat}
    (window : Sharpness.BadWindow threshold requestedScale) : Fraction.Rational :=
  threshold * Fraction.Cast.fromInt (Best.Error.denominatorQuadrance window.upper : Int) *
    Best.Error.errorQuadrance window.source.value window.lower

/-- The direct upper-quadrance reading gives the original exact bad-window threshold expression. -/
theorem violationValue_eq_cast {threshold : Fraction.Rational} {requestedScale : Nat}
    (window : Sharpness.BadWindow threshold requestedScale) : violationValue window =
    threshold * (Best.Error.denominatorQuadrance window.upper : Fraction.Rational) *
      Best.Error.errorQuadrance window.source.value window.lower := by
  rewrite [Fraction.Cast.natCast_eq_fromInt]
  rfl

/-- Positive rational slack in the exact bad-window inequality. -/
@[expose] def violationClearance
    {threshold : Fraction.Rational} {requestedScale : Nat}
    (window : Sharpness.BadWindow threshold requestedScale) : Fraction.Rational :=
  Dirichlet.Critical.Robust.Violation.violationValue window - 1

/-- The retained bad-window threshold expression is strictly greater than one. -/
theorem violationValue_gt_one
    {threshold : Fraction.Rational} {requestedScale : Nat}
    (window : Sharpness.BadWindow threshold requestedScale) :
    1 < Dirichlet.Critical.Robust.Violation.violationValue window := by
  calc
    (1 : Fraction.Rational) < threshold *
        ((Best.Error.denominatorQuadrance window.upper : Fraction.Rational) *
          Best.Error.errorQuadrance window.source.value window.lower) := by
      simpa only [Dirichlet.Window.SourceBound.dirichletWindowQuadrance_eq_cast] using window.violates
    _ = Dirichlet.Critical.Robust.Violation.violationValue window := by
      rewrite [violationValue_eq_cast]
      ring1

/-- Subtracting one from the bad-window threshold expression gives positive clearance. -/
theorem violationClearance_pos
    {threshold : Fraction.Rational} {requestedScale : Nat}
    (window : Sharpness.BadWindow threshold requestedScale) :
    0 < Dirichlet.Critical.Robust.Violation.violationClearance window :=
  Fraction.Order.Arithmetic.sub_pos_direct (Dirichlet.Critical.Robust.Violation.violationValue_gt_one window)

/-- Integer weight large enough to make the weighted perturbation estimate
arbitrarily close to its exact-source value. -/
@[expose] def stabilityWeightNat
    {threshold : Fraction.Rational} {requestedScale : Nat}
    (window : Sharpness.BadWindow threshold requestedScale) : Nat :=
  Data.Rat.Rounding.Floor.ceilNat (2 / Dirichlet.Critical.Robust.Violation.violationClearance window) + 1

/-- The rational cast of the explicit ceiling-based natural stability weight. -/
@[expose] def stabilityWeight
    {threshold : Fraction.Rational} {requestedScale : Nat}
    (window : Sharpness.BadWindow threshold requestedScale) : Fraction.Rational :=
  Fraction.Cast.fromInt (Dirichlet.Critical.Robust.Violation.stabilityWeightNat window : Int)

/-- The direct stability-weight reading is exactly the original natural weight's rational cast. -/
theorem stabilityWeight_eq_cast {threshold : Fraction.Rational} {requestedScale : Nat}
    (window : Sharpness.BadWindow threshold requestedScale) : stabilityWeight window =
    (stabilityWeightNat window : Fraction.Rational) :=
  (Fraction.Cast.natCast_eq_fromInt (stabilityWeightNat window)).symm

/-- The selected stability weight is positive. -/
theorem stabilityWeight_pos
    {threshold : Fraction.Rational} {requestedScale : Nat}
    (window : Sharpness.BadWindow threshold requestedScale) :
    0 < Dirichlet.Critical.Robust.Violation.stabilityWeight window := by
  rewrite [stabilityWeight_eq_cast]
  apply Fraction.Cast.Order.natCast_pos_direct
  unfold Dirichlet.Critical.Robust.Violation.stabilityWeightNat
  exact Nat.zero_lt_succ _

/-- The stability weight times the exact violation clearance exceeds two. -/
theorem two_lt_stabilityWeight_mul_clearance
    {threshold : Fraction.Rational} {requestedScale : Nat}
    (window : Sharpness.BadWindow threshold requestedScale) :
    (2 : Fraction.Rational) <
      Dirichlet.Critical.Robust.Violation.stabilityWeight window *
        Dirichlet.Critical.Robust.Violation.violationClearance window := by
  have clearancePositive := Dirichlet.Critical.Robust.Violation.violationClearance_pos window
  have ratioNonnegative :
      (0 : Fraction.Rational) ≤ 2 / Dirichlet.Critical.Robust.Violation.violationClearance window :=
    (Fraction.Order.Field.div_pos_direct (by decide)
      clearancePositive).le
  have ratioLeCeiling :
      2 / Dirichlet.Critical.Robust.Violation.violationClearance window ≤
        (Data.Rat.Rounding.Floor.ceilNat
          (2 / Dirichlet.Critical.Robust.Violation.violationClearance window) : Fraction.Rational) :=
    Data.Rat.Rounding.Floor.le_natCast_ceilNat_of_nonneg ratioNonnegative
  have ceilingLtWeightNat :
      Data.Rat.Rounding.Floor.ceilNat
          (2 / Dirichlet.Critical.Robust.Violation.violationClearance window) <
            Dirichlet.Critical.Robust.Violation.stabilityWeightNat window := by
    unfold Dirichlet.Critical.Robust.Violation.stabilityWeightNat
    exact Nat.lt_add_one_iff.mpr (Nat.le_refl _)
  have ceilingLtWeight :
      (Data.Rat.Rounding.Floor.ceilNat
          (2 / Dirichlet.Critical.Robust.Violation.violationClearance window) : Fraction.Rational) <
        Dirichlet.Critical.Robust.Violation.stabilityWeight window :=
    (Fraction.Cast.Order.natCast_lt_direct ceilingLtWeightNat).trans_eq (stabilityWeight_eq_cast window).symm
  have ratioLtWeight :
      2 / Dirichlet.Critical.Robust.Violation.violationClearance window <
        Dirichlet.Critical.Robust.Violation.stabilityWeight window :=
    ratioLeCeiling.trans_lt ceilingLtWeight
  exact (Fraction.Order.Field.div_lt_iff_pos clearancePositive).1
    ratioLtWeight

/-- Remaining scaled strictness after paying for the weighted normalization. -/
@[expose] def stabilityMargin
    {threshold : Fraction.Rational} {requestedScale : Nat}
    (window : Sharpness.BadWindow threshold requestedScale) : Fraction.Rational :=
  Dirichlet.Critical.Robust.Violation.stabilityWeight window * Dirichlet.Critical.Robust.Violation.violationClearance
    window - 1

/-- The weighted violation clearance remains positive after subtracting one. -/
theorem stabilityMargin_pos
    {threshold : Fraction.Rational} {requestedScale : Nat}
    (window : Sharpness.BadWindow threshold requestedScale) :
    0 < Dirichlet.Critical.Robust.Violation.stabilityMargin window := by
  apply Fraction.Order.Arithmetic.sub_pos_direct
  exact (show (1 : Fraction.Rational) < 2 by decide).trans
    (Dirichlet.Critical.Robust.Violation.two_lt_stabilityWeight_mul_clearance window)

/-- A threshold admitting a bad-window certificate is positive. -/
private theorem threshold_pos
    {threshold : Fraction.Rational} {requestedScale : Nat}
    (window : Sharpness.BadWindow threshold requestedScale) : 0 < threshold := by
  have exactViolation := window.violates
  have windowNonnegative :
      (0 : Fraction.Rational) ≤ Dirichlet.Window.SourceBound.dirichletWindowQuadrance window.source.value
        window.lower window.upper := by
    rewrite [Dirichlet.Window.SourceBound.dirichletWindowQuadrance_eq_cast]
    exact Fraction.Order.Arithmetic.mul_nonneg_direct
      (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _))
      (Gaussian.Norm.Basic.normSq_nonneg _)
  by_contra thresholdSmall
  have thresholdNonpositive : threshold ≤ 0 := le_of_not_gt thresholdSmall
  have productNonpositive :
      threshold * Dirichlet.Window.SourceBound.dirichletWindowQuadrance window.source.value
        window.lower window.upper ≤ 0 := by
    rw [show (0 : Fraction.Rational) = 0 *
        Dirichlet.Window.SourceBound.dirichletWindowQuadrance window.source.value
          window.lower window.upper by ring1]
    exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      thresholdNonpositive windowNonnegative
  exact (not_lt_of_ge productNonpositive
    ((show (0 : Fraction.Rational) < 1 by decide).trans exactViolation)).elim

/-- The retained upper endpoint has positive denominator quadrance. -/
private theorem upperQuadrance_pos
    {threshold : Fraction.Rational} {requestedScale : Nat}
    (window : Sharpness.BadWindow threshold requestedScale) :
    0 < Best.Error.denominatorQuadrance window.upper :=
  (Nat.zero_le requestedScale).trans_lt window.beyondScale

/-- Coefficient multiplying source squared distance in the weighted loss. -/
@[expose] def stabilityCoefficient
    {threshold : Fraction.Rational} {requestedScale : Nat}
    (window : Sharpness.BadWindow threshold requestedScale) : Fraction.Rational :=
  threshold * Fraction.Cast.fromInt (Best.Error.denominatorQuadrance window.upper : Int) *
    Dirichlet.Critical.Robust.Violation.stabilityWeight window * (1 +
      Dirichlet.Critical.Robust.Violation.stabilityWeight window) *
      Fraction.Cast.fromInt (Best.Error.denominatorQuadrance window.lower : Int)

/-- Direct upper and lower quadrance readings retain the original weighted source-displacement coefficient. -/
theorem stabilityCoefficient_eq_cast {threshold : Fraction.Rational} {requestedScale : Nat}
    (window : Sharpness.BadWindow threshold requestedScale) : stabilityCoefficient window =
    threshold * (Best.Error.denominatorQuadrance window.upper : Fraction.Rational) *
      stabilityWeight window * (1 + stabilityWeight window) *
      (Best.Error.denominatorQuadrance window.lower : Fraction.Rational) := by
  rewrite [Fraction.Cast.natCast_eq_fromInt, Fraction.Cast.natCast_eq_fromInt]
  rfl

/-- The coefficient of squared source displacement in the weighted perturbation loss is positive. -/
theorem stabilityCoefficient_pos
    {threshold : Fraction.Rational} {requestedScale : Nat}
    (window : Sharpness.BadWindow threshold requestedScale) :
    0 < Dirichlet.Critical.Robust.Violation.stabilityCoefficient window := by
  have lowerPositive : 0 < Best.Error.denominatorQuadrance window.lower :=
    window.consecutive.1.1
      |> fun nonzero => GaussianInt.normNat_pos
        nonzero
  rewrite [stabilityCoefficient_eq_cast]
  exact Fraction.Order.Arithmetic.mul_pos_direct
    (Fraction.Order.Arithmetic.mul_pos_direct
      (Fraction.Order.Arithmetic.mul_pos_direct
        (Fraction.Order.Arithmetic.mul_pos_direct
          (Dirichlet.Critical.Robust.Violation.threshold_pos window)
          (Fraction.Cast.Order.natCast_pos_direct
            (Dirichlet.Critical.Robust.Violation.upperQuadrance_pos window)))
        (Dirichlet.Critical.Robust.Violation.stabilityWeight_pos window))
      ((show (0 : Fraction.Rational) < 1 by decide).trans_le
        (le_add_of_nonneg_right (Dirichlet.Critical.Robust.Violation.stabilityWeight_pos window).le)))
    (Fraction.Cast.Order.natCast_pos_direct lowerPositive)

/-- Positive squared source-distance budget retaining the strict violation. -/
@[expose] def allowedSourceDistanceSq
    {threshold : Fraction.Rational} {requestedScale : Nat}
    (window : Sharpness.BadWindow threshold requestedScale) : Fraction.Rational :=
  Dirichlet.Critical.Robust.Violation.stabilityMargin window / (2 *
    Dirichlet.Critical.Robust.Violation.stabilityCoefficient window)

/-- The explicit squared-distance budget preserving threshold violation is positive. -/
theorem allowedSourceDistanceSq_pos
    {threshold : Fraction.Rational} {requestedScale : Nat}
    (window : Sharpness.BadWindow threshold requestedScale) :
    0 < Dirichlet.Critical.Robust.Violation.allowedSourceDistanceSq window := by
  unfold Dirichlet.Critical.Robust.Violation.allowedSourceDistanceSq
  exact Fraction.Order.Field.div_pos_direct
    (Dirichlet.Critical.Robust.Violation.stabilityMargin_pos window)
    (Fraction.Order.Arithmetic.mul_pos_direct (by decide)
      (Dirichlet.Critical.Robust.Violation.stabilityCoefficient_pos window))

/-- The sampled error is the central error plus the source displacement times the embedded denominator. -/
private theorem error_perturbation_identity
    (center sample : Gaussian.Basic.Canonical) (pair : GaussianInt.Pair.Basic.ConvergentPair) :
    Best.Error.error sample pair =
      Best.Error.error center pair +
        (sample - center) * Purelib.Data.GaussianInt.toGaussian pair.denominator := by
  unfold Best.Error.error
  apply Gaussian.Basic.ext <;>
    simp only [Gaussian.Basic.sub_re,
      Gaussian.Basic.sub_im,
      Gaussian.Basic.add_re,
      Gaussian.Basic.add_im,
      Gaussian.Basic.mul_re,
      Gaussian.Basic.mul_im] <;>
    ring1

/-- Adding the negated denominator-scaled displacement to the sampled error recovers the central error. -/
private theorem exactError_sum_identity
    (center sample : Gaussian.Basic.Canonical) (pair : GaussianInt.Pair.Basic.ConvergentPair) :
    Best.Error.error sample pair +
        -((sample - center) * Purelib.Data.GaussianInt.toGaussian pair.denominator) =
      Best.Error.error center pair := by
  rw [Dirichlet.Critical.Robust.Violation.error_perturbation_identity]
  apply Gaussian.Basic.ext <;>
    simp only [Gaussian.Basic.add_re,
      Gaussian.Basic.add_im,
      Gaussian.Basic.neg_re,
      Gaussian.Basic.neg_im] <;>
    ring1

/-- The error displacement quadrance equals the source displacement quadrance times the denominator quadrance. -/
private theorem perturbation_normSq
    (center sample : Gaussian.Basic.Canonical) (pair : GaussianInt.Pair.Basic.ConvergentPair) :
    Data.Gaussian.Norm.Basic.normSq
        ((sample - center) * Purelib.Data.GaussianInt.toGaussian pair.denominator) =
      Data.Gaussian.Norm.Basic.normSq (sample - center) *
        (Best.Error.denominatorQuadrance pair : Fraction.Rational) := by
  rw [Gaussian.Norm.Basic.normSq_mul, GaussianInt.normSq_toGaussian]
  rfl

/-- The explicit distance budget is sound: every rational source within it
retains the strict threshold violation for this fixed displayed pair. -/
theorem one_lt_threshold_mul_window_of_distance
    {threshold : Fraction.Rational} {requestedScale : Nat}
    (window : Sharpness.BadWindow threshold requestedScale) (sample : Gaussian.Basic.Canonical)
    (distanceSmall :
      Data.Gaussian.Norm.Basic.normSq
          (sample - window.source.value) <
        Dirichlet.Critical.Robust.Violation.allowedSourceDistanceSq window) :
    1 < threshold * Dirichlet.Window.SourceBound.dirichletWindowQuadrance sample
      window.lower window.upper := by
  let center := window.source.value
  let exactError := Best.Error.error center window.lower
  let sampleError := Best.Error.error sample window.lower
  let displacement :=
    (sample - center) * GaussianInt.toGaussian window.lower.denominator
  let upperScale := (Best.Error.denominatorQuadrance window.upper : Fraction.Rational)
  let lowerScale := (Best.Error.denominatorQuadrance window.lower : Fraction.Rational)
  let coefficient := threshold * upperScale
  let weight := Dirichlet.Critical.Robust.Violation.stabilityWeight window
  let loss := coefficient * weight * (1 + weight) *
    Data.Gaussian.Norm.Basic.normSq displacement
  have coefficientPositive : 0 < coefficient :=
    Fraction.Order.Arithmetic.mul_pos_direct (Dirichlet.Critical.Robust.Violation.threshold_pos window)
      (Fraction.Cast.Order.natCast_pos_direct
        (Dirichlet.Critical.Robust.Violation.upperQuadrance_pos window))
  have weightPositive : 0 < weight := by
    simpa only [weight] using Dirichlet.Critical.Robust.Violation.stabilityWeight_pos window
  have onePlusWeightPositive : (0 : Fraction.Rational) < 1 + weight :=
    (show (0 : Fraction.Rational) < 1 by decide).trans_le
      (le_add_of_nonneg_right weightPositive.le)
  have stabilityCoefficientIdentity :
      Dirichlet.Critical.Robust.Violation.stabilityCoefficient window =
        coefficient * weight * (1 + weight) * lowerScale := by
    rewrite [stabilityCoefficient_eq_cast]
    dsimp only [coefficient, weight, upperScale, lowerScale]
  have coefficientTimesDistanceLtMargin :
      Dirichlet.Critical.Robust.Violation.stabilityCoefficient window *
          Data.Gaussian.Norm.Basic.normSq (sample - center) <
        Dirichlet.Critical.Robust.Violation.stabilityMargin window := by
    have allowedPositive := Dirichlet.Critical.Robust.Violation.allowedSourceDistanceSq_pos window
    have coefficientPositive' := Dirichlet.Critical.Robust.Violation.stabilityCoefficient_pos window
    calc
      Dirichlet.Critical.Robust.Violation.stabilityCoefficient window *
          Data.Gaussian.Norm.Basic.normSq (sample - center) <
        Dirichlet.Critical.Robust.Violation.stabilityCoefficient window *
          Dirichlet.Critical.Robust.Violation.allowedSourceDistanceSq window :=
          Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
            coefficientPositive' (by
              simpa only [center] using distanceSmall)
      _ = Dirichlet.Critical.Robust.Violation.allowedSourceDistanceSq window *
        Dirichlet.Critical.Robust.Violation.stabilityCoefficient window :=
        Fraction.Field.mul_comm _ _
      _ < Dirichlet.Critical.Robust.Violation.allowedSourceDistanceSq window *
          (2 * Dirichlet.Critical.Robust.Violation.stabilityCoefficient window) := by
        apply Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
          allowedPositive
        calc
          Dirichlet.Critical.Robust.Violation.stabilityCoefficient window =
              1 * Dirichlet.Critical.Robust.Violation.stabilityCoefficient window := by ring1
          _ < 2 * Dirichlet.Critical.Robust.Violation.stabilityCoefficient window :=
            Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct
              (by decide) coefficientPositive'
      _ = Dirichlet.Critical.Robust.Violation.stabilityMargin window := by
        unfold Dirichlet.Critical.Robust.Violation.allowedSourceDistanceSq
        exact Fraction.Field.div_mul_cancel_of_ne _ _
          (Fraction.Field.mul_ne_zero_direct
            (by decide) coefficientPositive'.ne')
  have lossLtMargin : loss < Dirichlet.Critical.Robust.Violation.stabilityMargin window := by
    dsimp only [loss]
    rw [show Data.Gaussian.Norm.Basic.normSq displacement =
        Data.Gaussian.Norm.Basic.normSq (sample - center) *
          lowerScale by
      dsimp only [displacement, lowerScale, center]
      exact Dirichlet.Critical.Robust.Violation.perturbation_normSq _ _ _]
    calc
      coefficient * weight * (1 + weight) *
          (Data.Gaussian.Norm.Basic.normSq (sample - center) *
            lowerScale) =
        Dirichlet.Critical.Robust.Violation.stabilityCoefficient window *
          Data.Gaussian.Norm.Basic.normSq (sample - center) := by
            rw [stabilityCoefficientIdentity]
            ring1
      _ < Dirichlet.Critical.Robust.Violation.stabilityMargin window := coefficientTimesDistanceLtMargin
  have exactValueIdentity :
      Dirichlet.Critical.Robust.Violation.violationValue window =
        coefficient * Data.Gaussian.Norm.Basic.normSq exactError := by
    rewrite [violationValue_eq_cast]
    unfold Best.Error.errorQuadrance
    dsimp only [coefficient, exactError, center, upperScale]
  have marginIdentity :
      Dirichlet.Critical.Robust.Violation.stabilityMargin window =
        coefficient * weight *
            Data.Gaussian.Norm.Basic.normSq exactError -
          (1 + weight) := by
    unfold Dirichlet.Critical.Robust.Violation.stabilityMargin Dirichlet.Critical.Robust.Violation.violationClearance
    rw [exactValueIdentity]
    dsimp only [weight]
    ring1
  have weighted := Gaussian.Norm.Weighted.weighted_normSq_add_le
    sampleError (-displacement) 1 weight
  have weightedErrorBound :
      weight * Data.Gaussian.Norm.Basic.normSq exactError ≤
        (1 + weight) *
            Data.Gaussian.Norm.Basic.normSq sampleError +
          weight * (1 + weight) *
            Data.Gaussian.Norm.Basic.normSq displacement := by
    rw [Dirichlet.Critical.Robust.Violation.exactError_sum_identity center sample window.lower,
      Gaussian.Norm.Basic.normSq_neg] at weighted
    simpa only [sampleError, displacement, exactError] using (show
      weight * Data.Gaussian.Norm.Basic.normSq exactError ≤
        (1 + weight) *
            Data.Gaussian.Norm.Basic.normSq sampleError +
          weight * (1 + weight) *
            Data.Gaussian.Norm.Basic.normSq displacement by
      calc
        weight * Data.Gaussian.Norm.Basic.normSq exactError =
            1 * weight *
              Data.Gaussian.Norm.Basic.normSq exactError := by ring1
        _ ≤ 1 * (1 + weight) *
              Data.Gaussian.Norm.Basic.normSq sampleError +
            weight * (1 + weight) *
              Data.Gaussian.Norm.Basic.normSq displacement :=
          weighted
        _ = _ := by ring1)
  have scaledWeighted :
      coefficient * weight *
          Data.Gaussian.Norm.Basic.normSq exactError ≤
        coefficient * (1 + weight) *
            Data.Gaussian.Norm.Basic.normSq sampleError + loss := by
    have scaled :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        weightedErrorBound coefficientPositive.le
    dsimp only [loss]
    calc
      coefficient * weight *
          Data.Gaussian.Norm.Basic.normSq exactError =
        coefficient *
          (weight * Data.Gaussian.Norm.Basic.normSq exactError) := by
            ring1
      _ ≤ coefficient *
          ((1 + weight) *
              Data.Gaussian.Norm.Basic.normSq sampleError +
            weight * (1 + weight) *
              Data.Gaussian.Norm.Basic.normSq displacement) := scaled
      _ = coefficient * (1 + weight) *
            Data.Gaussian.Norm.Basic.normSq sampleError +
          coefficient * weight * (1 + weight) *
            Data.Gaussian.Norm.Basic.normSq displacement := by ring1
  have exactStrictWithLoss :
      (1 + weight) + loss <
        coefficient * weight *
          Data.Gaussian.Norm.Basic.normSq exactError := by
    calc
      (1 + weight) + loss < (1 + weight) + Dirichlet.Critical.Robust.Violation.stabilityMargin window :=
        Fraction.Order.Arithmetic.add_lt_add_left_direct lossLtMargin _
      _ = coefficient * weight *
          Data.Gaussian.Norm.Basic.normSq exactError := by
        rw [marginIdentity]
        ring1
  have scaledViolationWithLoss :
      (1 + weight) + loss <
        (coefficient *
            Data.Gaussian.Norm.Basic.normSq sampleError) *
          (1 + weight) + loss := by
    calc
      (1 + weight) + loss <
          coefficient * weight *
            Data.Gaussian.Norm.Basic.normSq exactError :=
        exactStrictWithLoss
      _ ≤ coefficient * (1 + weight) *
            Data.Gaussian.Norm.Basic.normSq sampleError + loss :=
        scaledWeighted
      _ = (coefficient *
            Data.Gaussian.Norm.Basic.normSq sampleError) *
          (1 + weight) + loss := by ring1
  have scaledViolation :
      (1 : Fraction.Rational) * (1 + weight) <
        (coefficient *
          Data.Gaussian.Norm.Basic.normSq sampleError) *
            (1 + weight) := by
    have cancelled :=
      Fraction.Order.Arithmetic.lt_of_add_lt_add_right_direct
        scaledViolationWithLoss
    simpa only [Fraction.Field.one_mul] using cancelled
  have violation :
      (1 : Fraction.Rational) <
        coefficient *
          Data.Gaussian.Norm.Basic.normSq sampleError :=
    Fraction.Order.Arithmetic.lt_of_mul_lt_mul_right_direct
      scaledViolation onePlusWeightPositive
  rewrite [Dirichlet.Window.SourceBound.dirichletWindowQuadrance_eq_cast]
  unfold Best.Error.errorQuadrance
  dsimp only [coefficient, sampleError, upperScale] at violation ⊢
  calc
    (1 : Fraction.Rational) < threshold *
        (Best.Error.denominatorQuadrance window.upper : Fraction.Rational) *
          Data.Gaussian.Norm.Basic.normSq
            (Best.Error.error sample window.lower) := violation
    _ = threshold *
        ((Best.Error.denominatorQuadrance window.upper : Fraction.Rational) *
          Data.Gaussian.Norm.Basic.normSq
            (Best.Error.error sample window.lower)) := by
      ring1

/-- Positive rational side length chosen inside one violation's squared
distance budget. -/
@[expose] def violationBoxRadius
    {threshold : Fraction.Rational} {requestedScale : Nat}
    (window : Sharpness.BadWindow threshold requestedScale) : Fraction.Rational :=
  min 1 (Dirichlet.Critical.Robust.Violation.allowedSourceDistanceSq window * (1 / 4 : Fraction.Rational))

/-- The side length selected for the violation box is positive. -/
theorem violationBoxRadius_pos
    {threshold : Fraction.Rational} {requestedScale : Nat}
    (window : Sharpness.BadWindow threshold requestedScale) :
    0 < Dirichlet.Critical.Robust.Violation.violationBoxRadius window := by
  unfold Dirichlet.Critical.Robust.Violation.violationBoxRadius
  apply Fraction.Order.Basic.lt_min (by decide)
  exact Fraction.Order.Arithmetic.mul_pos_direct
    (Dirichlet.Critical.Robust.Violation.allowedSourceDistanceSq_pos window) (by decide)

/-- Proper rational square extending up and right from the exact source. -/
@[expose] def violationBox
    {threshold : Fraction.Rational} {requestedScale : Nat}
    (window : Sharpness.BadWindow threshold requestedScale) : Geometry.Rational.Box
      where
  xLower := window.source.value.re
  xUpper := window.source.value.re + Dirichlet.Critical.Robust.Violation.violationBoxRadius window
  yLower := window.source.value.im
  yUpper := window.source.value.im + Dirichlet.Critical.Robust.Violation.violationBoxRadius window
  x_valid := le_add_of_nonneg_right (Dirichlet.Critical.Robust.Violation.violationBoxRadius_pos window).le
  y_valid := le_add_of_nonneg_right (Dirichlet.Critical.Robust.Violation.violationBoxRadius_pos window).le

/-- The explicit violation box has strictly positive width and height. -/
theorem violationBox_proper
    {threshold : Fraction.Rational} {requestedScale : Nat}
    (window : Sharpness.BadWindow threshold requestedScale) :
    (Dirichlet.Critical.Robust.Violation.violationBox window).Proper := by
  unfold Geometry.Rational.Box.Proper Dirichlet.Critical.Robust.Violation.violationBox
  constructor
  · calc
      window.source.value.re = window.source.value.re + 0 := by ring1
      _ < window.source.value.re + Dirichlet.Critical.Robust.Violation.violationBoxRadius window :=
        Fraction.Order.Arithmetic.add_lt_add_left_direct
          (Dirichlet.Critical.Robust.Violation.violationBoxRadius_pos window) _
  · calc
      window.source.value.im = window.source.value.im + 0 := by ring1
      _ < window.source.value.im + Dirichlet.Critical.Robust.Violation.violationBoxRadius window :=
        Fraction.Order.Arithmetic.add_lt_add_left_direct
          (Dirichlet.Critical.Robust.Violation.violationBoxRadius_pos window) _

/-- The violation box is anchored at the retained exact source. -/
@[simp] theorem violationBox_anchor
    {threshold : Fraction.Rational} {requestedScale : Nat}
    (window : Sharpness.BadWindow threshold requestedScale) :
    (Dirichlet.Critical.Robust.Violation.violationBox window).anchor = window.source.value := by
  apply Gaussian.Basic.ext <;> rfl

/-- The violation box diagonal quadrance is twice the square of its selected side length. -/
theorem violationBox_diagonalSq
    {threshold : Fraction.Rational} {requestedScale : Nat}
    (window : Sharpness.BadWindow threshold requestedScale) :
    (Dirichlet.Critical.Robust.Violation.violationBox window).diagonalSq =
      2 * Dirichlet.Critical.Robust.Violation.violationBoxRadius window ^ 2 := by
  unfold Dirichlet.Critical.Robust.Violation.violationBox Geometry.Rational.Box.diagonalSq
  ring1

/-- The violation box diagonal quadrance lies strictly inside the allowed source-distance budget. -/
private theorem two_mul_violationBoxRadius_sq_lt_allowed
    {threshold : Fraction.Rational} {requestedScale : Nat}
    (window : Sharpness.BadWindow threshold requestedScale) :
    2 * Dirichlet.Critical.Robust.Violation.violationBoxRadius window ^ 2 <
      Dirichlet.Critical.Robust.Violation.allowedSourceDistanceSq window := by
  have radiusPositive := Dirichlet.Critical.Robust.Violation.violationBoxRadius_pos window
  have radiusLeOne : Dirichlet.Critical.Robust.Violation.violationBoxRadius window ≤ 1 :=
    Fraction.Order.Basic.min_le_left _ _
  have squareLeRadius :
      Dirichlet.Critical.Robust.Violation.violationBoxRadius window ^ 2 ≤
        Dirichlet.Critical.Robust.Violation.violationBoxRadius window := by
    rw [pow_two]
    calc
      Dirichlet.Critical.Robust.Violation.violationBoxRadius window *
        Dirichlet.Critical.Robust.Violation.violationBoxRadius window ≤
          Dirichlet.Critical.Robust.Violation.violationBoxRadius window * 1 :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          radiusLeOne radiusPositive.le
      _ = Dirichlet.Critical.Robust.Violation.violationBoxRadius window := by ring1
  have radiusLeQuarter :
      Dirichlet.Critical.Robust.Violation.violationBoxRadius window ≤
        Dirichlet.Critical.Robust.Violation.allowedSourceDistanceSq window * (1 / 4 : Fraction.Rational) :=
    Fraction.Order.Basic.min_le_right _ _
  have doubledRadiusBound :
      2 * Dirichlet.Critical.Robust.Violation.violationBoxRadius window ≤
        Dirichlet.Critical.Robust.Violation.allowedSourceDistanceSq window * (1 / 2 : Fraction.Rational) := by
    calc
      2 * Dirichlet.Critical.Robust.Violation.violationBoxRadius window ≤
          2 * (Dirichlet.Critical.Robust.Violation.allowedSourceDistanceSq window * (1 / 4 : Fraction.Rational)) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          radiusLeQuarter (by decide)
      _ = Dirichlet.Critical.Robust.Violation.allowedSourceDistanceSq window *
          (2 * (1 / 4 : Fraction.Rational)) := by ring1
      _ = Dirichlet.Critical.Robust.Violation.allowedSourceDistanceSq window * (1 / 2 : Fraction.Rational) := by
        rw [show (2 : Fraction.Rational) * (1 / 4) = 1 / 2 by decide]
  calc
    2 * Dirichlet.Critical.Robust.Violation.violationBoxRadius window ^ 2 ≤
        2 * Dirichlet.Critical.Robust.Violation.violationBoxRadius window :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        squareLeRadius (by decide)
    _ ≤ Dirichlet.Critical.Robust.Violation.allowedSourceDistanceSq window * (1 / 2 : Fraction.Rational) :=
      doubledRadiusBound
    _ < Dirichlet.Critical.Robust.Violation.allowedSourceDistanceSq window * 1 :=
      Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
        (Dirichlet.Critical.Robust.Violation.allowedSourceDistanceSq_pos window) (by decide)
    _ = Dirichlet.Critical.Robust.Violation.allowedSourceDistanceSq window := by ring1

/-- Every rational sample in the executable proper box retains this window's
strict sharper-threshold violation. -/
theorem violationBox_uniform
    {threshold : Fraction.Rational} {requestedScale : Nat}
    (window : Sharpness.BadWindow threshold requestedScale) (sample : Gaussian.Basic.Canonical)
    (inside : (Dirichlet.Critical.Robust.Violation.violationBox window).Contains sample) :
    1 < threshold * Dirichlet.Window.SourceBound.dirichletWindowQuadrance sample
      window.lower window.upper := by
  apply Dirichlet.Critical.Robust.Violation.one_lt_threshold_mul_window_of_distance window sample
  calc
    Data.Gaussian.Norm.Basic.normSq
          (sample - window.source.value) =
        Data.Gaussian.Norm.Basic.normSq
          (sample - (Dirichlet.Critical.Robust.Violation.violationBox window).anchor) := by
      rw [Dirichlet.Critical.Robust.Violation.violationBox_anchor]
    _ ≤ (Dirichlet.Critical.Robust.Violation.violationBox window).diagonalSq :=
      (Dirichlet.Critical.Robust.Violation.violationBox window).normSq_sub_anchor_le inside
    _ = 2 * Dirichlet.Critical.Robust.Violation.violationBoxRadius window ^ 2 :=
      Dirichlet.Critical.Robust.Violation.violationBox_diagonalSq window
    _ < Dirichlet.Critical.Robust.Violation.allowedSourceDistanceSq window :=
      Dirichlet.Critical.Robust.Violation.two_mul_violationBoxRadius_sq_lt_allowed window

/-- The recursive minimum of a finite list of violation-box radii, capped by one. -/
private def minimumViolationRadius
    {threshold : Fraction.Rational} {requestedScale : Nat} :
    List (Sharpness.BadWindow threshold requestedScale) → Fraction.Rational
  | [] => 1
  | window :: remaining =>
      min (Dirichlet.Critical.Robust.Violation.violationBoxRadius window)
        (Purelib.NumberTheory.Approximation.Dirichlet.Critical.Robust.Violation.minimumViolationRadius remaining)

/-- The exposed finite minimum of violation-box radii, with value one on the empty list.

Each retained window contributes its own rational side length; recursive minima give one common bound without changing
the windows. -/
@[expose] def minimumRunViolationRadius
    {threshold : Fraction.Rational} {requestedScale : Nat} :
    List (Sharpness.BadWindow threshold requestedScale) → Fraction.Rational
  | [] => 1
  | window :: remaining =>
      min (Dirichlet.Critical.Robust.Violation.violationBoxRadius window)
        (Purelib.NumberTheory.Approximation.Dirichlet.Critical.Robust.Violation.minimumRunViolationRadius remaining)

/-- The exposed run-radius computation agrees with the private finite minimum. -/
private theorem minimumRunViolationRadius_eq
    {threshold : Fraction.Rational} {requestedScale : Nat}
    (windows : List (Sharpness.BadWindow threshold requestedScale)) :
    Dirichlet.Critical.Robust.Violation.minimumRunViolationRadius windows =
      Dirichlet.Critical.Robust.Violation.minimumViolationRadius windows := by
  induction windows with
  | nil => rfl
  | cons window remaining ih =>
      change min (Dirichlet.Critical.Robust.Violation.violationBoxRadius window)
        (Dirichlet.Critical.Robust.Violation.minimumRunViolationRadius remaining) =
        min (Dirichlet.Critical.Robust.Violation.violationBoxRadius window)
          (Dirichlet.Critical.Robust.Violation.minimumViolationRadius remaining)
      rw [ih]

/-- The finite minimum of positive violation-box radii is positive. -/
private theorem minimumViolationRadius_pos
    {threshold : Fraction.Rational} {requestedScale : Nat}
    (windows : List (Sharpness.BadWindow threshold requestedScale)) :
    0 < Dirichlet.Critical.Robust.Violation.minimumViolationRadius windows := by
  induction windows with
  | nil => exact (show (0 : Fraction.Rational) < 1 by decide)
  | cons window remaining inductionHypothesis =>
      unfold Dirichlet.Critical.Robust.Violation.minimumViolationRadius
      exact Fraction.Order.Basic.lt_min (Dirichlet.Critical.Robust.Violation.violationBoxRadius_pos window)
        inductionHypothesis

/-- The finite minimum is no larger than the radius of any listed window. -/
private theorem minimumViolationRadius_le_of_mem
    {threshold : Fraction.Rational} {requestedScale : Nat}
    {window : Sharpness.BadWindow threshold requestedScale}
    (windows : List (Sharpness.BadWindow threshold requestedScale))
    (member : window ∈ windows) :
    Dirichlet.Critical.Robust.Violation.minimumViolationRadius windows ≤
      Dirichlet.Critical.Robust.Violation.violationBoxRadius window := by
  induction windows with
  | nil => cases member
  | cons head remaining inductionHypothesis =>
      rcases Data.List.Membership.mem_cons.mp member with equal | tailMember
      · rw [equal]
        exact Fraction.Order.Basic.min_le_left _ _
      · exact (Fraction.Order.Basic.min_le_right _ _).trans
          (inductionHypothesis tailMember)

/-- Common positive side length obtained by a finite minimum over the run. -/
@[expose] def runBoxRadius
    {threshold : Fraction.Rational} {requestedScale count : Nat}
    (run : Dirichlet.Critical.Run.SameSourceBadWindowRun
      threshold requestedScale count) : Fraction.Rational :=
  Dirichlet.Critical.Robust.Violation.minimumRunViolationRadius (run.windows.map Subtype.val)

/-- The common box radius of a finite same-source run is positive. -/
theorem runBoxRadius_pos
    {threshold : Fraction.Rational} {requestedScale count : Nat}
    (run : Dirichlet.Critical.Run.SameSourceBadWindowRun
      threshold requestedScale count) :
    0 < Dirichlet.Critical.Robust.Violation.runBoxRadius run :=
  by
    unfold Dirichlet.Critical.Robust.Violation.runBoxRadius
    rw [Dirichlet.Critical.Robust.Violation.minimumRunViolationRadius_eq]
    exact Dirichlet.Critical.Robust.Violation.minimumViolationRadius_pos _

/-- The common run radius is bounded by each retained window radius. -/
private theorem runBoxRadius_le
    {threshold : Fraction.Rational} {requestedScale count : Nat}
    (run : Dirichlet.Critical.Run.SameSourceBadWindowRun
      threshold requestedScale count)
    (window : { window : Sharpness.BadWindow threshold requestedScale //
      window.source = run.source }) (member : window ∈ run.windows) :
    Dirichlet.Critical.Robust.Violation.runBoxRadius run ≤ Dirichlet.Critical.Robust.Violation.violationBoxRadius
      window.1 := by
  unfold Dirichlet.Critical.Robust.Violation.runBoxRadius
  rw [Dirichlet.Critical.Robust.Violation.minimumRunViolationRadius_eq]
  apply Dirichlet.Critical.Robust.Violation.minimumViolationRadius_le_of_mem
  exact Data.List.Map.mem_map.mpr ⟨window, member, rfl⟩

/-- One proper rational box shared by all exact windows in a finite run. -/
@[expose] def runViolationBox
    {threshold : Fraction.Rational} {requestedScale count : Nat}
    (run : Dirichlet.Critical.Run.SameSourceBadWindowRun
      threshold requestedScale count) : Geometry.Rational.Box where
  xLower := run.source.value.re
  xUpper := run.source.value.re + Dirichlet.Critical.Robust.Violation.runBoxRadius run
  yLower := run.source.value.im
  yUpper := run.source.value.im + Dirichlet.Critical.Robust.Violation.runBoxRadius run
  x_valid := le_add_of_nonneg_right (Dirichlet.Critical.Robust.Violation.runBoxRadius_pos run).le
  y_valid := le_add_of_nonneg_right (Dirichlet.Critical.Robust.Violation.runBoxRadius_pos run).le

/-- The common run violation box has strictly positive width and height. -/
theorem runViolationBox_proper
    {threshold : Fraction.Rational} {requestedScale count : Nat}
    (run : Dirichlet.Critical.Run.SameSourceBadWindowRun
      threshold requestedScale count) :
    (Dirichlet.Critical.Robust.Violation.runViolationBox run).Proper := by
  unfold Geometry.Rational.Box.Proper Dirichlet.Critical.Robust.Violation.runViolationBox
  constructor
  · calc
      run.source.value.re = run.source.value.re + 0 := by ring1
      _ < run.source.value.re + Dirichlet.Critical.Robust.Violation.runBoxRadius run :=
        Fraction.Order.Arithmetic.add_lt_add_left_direct
          (Dirichlet.Critical.Robust.Violation.runBoxRadius_pos run) _
  · calc
      run.source.value.im = run.source.value.im + 0 := by ring1
      _ < run.source.value.im + Dirichlet.Critical.Robust.Violation.runBoxRadius run :=
        Fraction.Order.Arithmetic.add_lt_add_left_direct
          (Dirichlet.Critical.Robust.Violation.runBoxRadius_pos run) _

/-- The common violation box is anchored at the exact shared source of the run. -/
@[simp] theorem runViolationBox_anchor
    {threshold : Fraction.Rational} {requestedScale count : Nat}
    (run : Dirichlet.Critical.Run.SameSourceBadWindowRun
      threshold requestedScale count) :
    (Dirichlet.Critical.Robust.Violation.runViolationBox run).anchor = run.source.value := by
  apply Gaussian.Basic.ext <;> rfl

/-- The common run box refines the violation box of each listed window.

The retained source equality identifies their anchors and the finite radius minimum bounds both upper coordinates. -/
private theorem runViolationBox_refines
    {threshold : Fraction.Rational} {requestedScale count : Nat}
    (run : Dirichlet.Critical.Run.SameSourceBadWindowRun
      threshold requestedScale count)
    (window : { window : Sharpness.BadWindow threshold requestedScale //
      window.source = run.source }) (member : window ∈ run.windows) :
    (Dirichlet.Critical.Robust.Violation.runViolationBox run).Refines (Dirichlet.Critical.Robust.Violation.violationBox
      window.1) := by
  have sourceValueEqual := congrArg GaussianInt.Fraction.value
    window.property
  unfold Geometry.Rational.Box.Refines Dirichlet.Critical.Robust.Violation.runViolationBox
    Dirichlet.Critical.Robust.Violation.violationBox
  dsimp only
  rw [sourceValueEqual]
  have radiusBound := Dirichlet.Critical.Robust.Violation.runBoxRadius_le run window member
  have realUpper :
      run.source.value.re + Dirichlet.Critical.Robust.Violation.runBoxRadius run ≤
        run.source.value.re + Dirichlet.Critical.Robust.Violation.violationBoxRadius window.1 := by
    calc
      run.source.value.re + Dirichlet.Critical.Robust.Violation.runBoxRadius run =
          Dirichlet.Critical.Robust.Violation.runBoxRadius run + run.source.value.re := by ring1
      _ ≤ Dirichlet.Critical.Robust.Violation.violationBoxRadius window.1 + run.source.value.re :=
        Fraction.Order.Arithmetic.add_le_add_right_direct radiusBound _
      _ = run.source.value.re + Dirichlet.Critical.Robust.Violation.violationBoxRadius window.1 := by ring1
  have imaginaryUpper :
      run.source.value.im + Dirichlet.Critical.Robust.Violation.runBoxRadius run ≤
        run.source.value.im + Dirichlet.Critical.Robust.Violation.violationBoxRadius window.1 := by
    calc
      run.source.value.im + Dirichlet.Critical.Robust.Violation.runBoxRadius run =
          Dirichlet.Critical.Robust.Violation.runBoxRadius run + run.source.value.im := by ring1
      _ ≤ Dirichlet.Critical.Robust.Violation.violationBoxRadius window.1 + run.source.value.im :=
        Fraction.Order.Arithmetic.add_le_add_right_direct radiusBound _
      _ = run.source.value.im + Dirichlet.Critical.Robust.Violation.violationBoxRadius window.1 := by ring1
  exact ⟨le_rfl, realUpper, le_rfl, imaginaryUpper⟩

/-- Every displayed rational source sample in the common run box preserves
the strict threshold violation of every listed window. -/
theorem runViolationBox_uniform
    {threshold : Fraction.Rational} {requestedScale count : Nat}
    (run : Dirichlet.Critical.Run.SameSourceBadWindowRun
      threshold requestedScale count)
    (sample : Gaussian.Basic.Canonical) (inside : (Dirichlet.Critical.Robust.Violation.runViolationBox run).Contains
      sample)
    (window : { window : Sharpness.BadWindow threshold requestedScale //
      window.source = run.source }) (member : window ∈ run.windows) :
    1 < threshold * Dirichlet.Window.SourceBound.dirichletWindowQuadrance sample
      window.1.lower window.1.upper :=
  Dirichlet.Critical.Robust.Violation.violationBox_uniform window.1 sample
    ((Dirichlet.Critical.Robust.Violation.runViolationBox_refines run window member).contains inside)

set_option genInjectivity false in
/-- A finite bad-window run with one proper rational box preserving every threshold violation.

The record retains the exact source and windows, identifies the source with the box anchor, and certifies the
inequalities uniformly for all samples in the box. -/
structure ViolationRobustRun
    (threshold : Fraction.Rational) (requestedScale count : Nat) where
  /-- The retained exact same-source bad-window run, including its length and strict scale order. -/ exact :
    Dirichlet.Critical.Run.SameSourceBadWindowRun
    threshold requestedScale count
  /-- The common rational box on which the window inequalities remain violated. -/ box :
    Geometry.Rational.Box
  /-- The common box has strictly positive width and height. -/ proper : box.Proper
  /-- The box anchor is exactly the retained run source. -/ sourceAtAnchor : box.anchor = exact.source.value
  /-- Every sample in the box violates the threshold inequality for every retained window. -/ uniformViolation : ∀
    sample : Gaussian.Basic.Canonical, box.Contains sample →
    ∀ window, window ∈ exact.windows →
      1 < threshold * Dirichlet.Window.SourceBound.dirichletWindowQuadrance sample
        window.1.lower window.1.upper

constructive_injectivity ViolationRobustRun

/-- The executable arbitrary-length critical run carries a common proper
rational box on which all strict threshold violations persist. -/
@[expose] def criticalViolationRobustRun
    {threshold : Fraction.Rational}
    (certificate :
      Dirichlet.Critical.Sharpness.IsSharperWindowThreshold threshold)
    (requestedScale count : Nat) :
    Dirichlet.Critical.Robust.Violation.ViolationRobustRun threshold requestedScale count := by
  let run := Dirichlet.Critical.Run.criticalBadWindowRun
    certificate requestedScale count
  exact
    { exact := run
      box := Dirichlet.Critical.Robust.Violation.runViolationBox run
      proper := Dirichlet.Critical.Robust.Violation.runViolationBox_proper run
      sourceAtAnchor := Dirichlet.Critical.Robust.Violation.runViolationBox_anchor run
      uniformViolation := fun sample inside window member =>
        Dirichlet.Critical.Robust.Violation.runViolationBox_uniform run sample inside window member }

end Purelib.NumberTheory.Approximation.Dirichlet.Critical.Robust.Violation

end
