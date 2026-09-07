import mathlib.Tactic.QuotientFreeRing
import CCL.Progressive.Exp

/-!
# Automatic finite range reduction for the progressive exponential

This module makes the local construction a total exponential operator on
arithmetic CCL names.  One finite input ball from the CCL accuracy sidechannel
supplies a rational norm bound.  A logarithmic bounded scan chooses a
displayed natural exponent `k` for which division by `2^k` puts every
candidate in the unit disk.  The local exponential CCL name is then squared
exactly `k` times by the already proved CCL arithmetic operation.  The result
is again a productive CCL name.  No magnitude limit, completed input value,
or infinite functional equation is used; the bare raw bitstream is not asked
to provide quantitative accuracy by itself.
-/

namespace CCL.ProgressiveExpRange

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Named := CCL.ProgressiveTransducer.Named

open RFAP.ConstructiveGaussian.Gaussian

/-- A finite squared-norm bound for every candidate at the supplied state. -/
def inputBound (input : Named) : Coordinate :=
  2 * ((input.process.ball input.state).radiusSq +
    normSq (input.process.ball input.state).center)

theorem inputBound_nonneg (input : Named) : 0 ≤ inputBound input :=
  RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
    (add_nonneg (input.process.ball input.state).radiusSq_nonneg
      (normSq_nonneg _))

theorem possible_normSq_le_inputBound (input : Named) {value : Gaussian}
    (possible : input.process.Possible input.state value) :
    normSq value ≤ inputBound input := by
  let center := (input.process.ball input.state).center
  have inside := input.process.possible_inside possible
  have identity : value = (value - center) + center := by
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [sub_re, sub_im, add_re, add_im] <;> ring1
  rw [identity]
  exact (normSq_add_le_two _ _).trans
    (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      (add_le_add inside le_rfl) (by decide))

/-- Computed dyadic range exponent. -/
def rangeExponent (input : Named) : Nat :=
  CCL.FiniteGeometric.firstQuarterBelow (inputBound input) 0 1

theorem rangeExponent_accurate (input : Named) :
    CCL.FiniteGeometric.quarterRadius (inputBound input)
      (rangeExponent input) < 1 :=
  CCL.FiniteGeometric.firstQuarterBelow_accurate
    (inputBound input) (inputBound_nonneg input) 0 1 (by decide)

def dyadicDenominator (input : Named) : Coordinate :=
  (2 : Coordinate) ^ rangeExponent input

theorem dyadicDenominator_pos (input : Named) :
    0 < dyadicDenominator input :=
  RFAP.ConstructiveFraction.pow_pos_direct (by decide) (rangeExponent input)

def inverseDyadic (input : Named) : Gaussian :=
  ⟨1 / dyadicDenominator input, 0⟩

theorem normSq_inverseDyadic (input : Named) :
    normSq (inverseDyadic input) =
      CCL.FiniteGeometric.quarterRadius 1
        (rangeExponent input) := by
  change (1 / dyadicDenominator input) ^ 2 + 0 ^ 2 =
    1 / (4 : Coordinate) ^ rangeExponent input
  rw [show (0 : Coordinate) ^ 2 = 0 by decide,
    RFAP.ConstructiveFraction.add_comm _ 0,
    RFAP.ConstructiveFraction.zero_add]
  rw [pow_two]
  calc
    1 / dyadicDenominator input * (1 / dyadicDenominator input) =
        (1 * 1) / (dyadicDenominator input * dyadicDenominator input) :=
      RFAP.ConstructiveFraction.div_mul_div_direct _ _ _ _
    _ = 1 / (4 : Coordinate) ^ rangeExponent input := by
      rw [RFAP.ConstructiveFraction.one_mul]
      congr 1
      rw [dyadicDenominator, ← mul_pow]
      congr 1

def scaledInput (input : Named) : Named :=
  CCL.ProgressiveTransducer.Named.mul
    (CCL.ProgressiveTransducer.Named.exact (inverseDyadic input))
    input

/-- The automatically scaled input satisfies the local unit-disk contract. -/
theorem scaledDomain (input : Named) :
    CCL.ProgressiveExp.UnitDisk (scaledInput input) where
  possible_unit := by
    intro value possible
    rcases possible with ⟨scaleValue, sourceValue,
      scalePossible, sourcePossible, rfl⟩
    change scaleValue = inverseDyadic input at scalePossible
    subst scaleValue
    rw [normSq_mul, normSq_inverseDyadic]
    calc
      CCL.FiniteGeometric.quarterRadius 1 (rangeExponent input) *
          normSq sourceValue ≤
        CCL.FiniteGeometric.quarterRadius 1 (rangeExponent input) *
          inputBound input :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          (possible_normSq_le_inputBound input sourcePossible)
          (CCL.FiniteGeometric.quarterRadius_nonneg (by decide) _)
      _ = CCL.FiniteGeometric.quarterRadius (inputBound input)
          (rangeExponent input) := by
        rw [CCL.FiniteGeometric.quarterRadius_eq_mul_pow,
          CCL.FiniteGeometric.quarterRadius_eq_mul_pow]
        ring1
      _ ≤ 1 := (rangeExponent_accurate input).le

/-- Repeated finite squaring of a progressive arithmetic name. -/
def squareIterate : Nat → Named → Named
  | 0, value => value
  | exponent + 1, value =>
      let previous := squareIterate exponent value
      CCL.ProgressiveTransducer.Named.mul previous previous

/-- Total CCL exponential entry point: an arbitrary arithmetic CCL name is
mapped to a productive arithmetic CCL name for its finite exponential
recurrence. -/
def named (input : Named) : Named :=
  squareIterate (rangeExponent input)
    (CCL.ProgressiveExp.named (scaledInput input)
      (scaledDomain input))

theorem productive (input : Named) (count : Nat) :
    (named input).machine.emitted.IsPrefix
        (CCL.ProgressiveTransducer.advance
          (named input).machine count).emitted ∧
      (CCL.ProgressiveTransducer.advance
          (named input).machine count).emitted.length = count :=
  (named input).productive count

end CCL.ProgressiveExpRange
