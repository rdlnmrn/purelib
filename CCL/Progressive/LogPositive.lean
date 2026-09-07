import mathlib.Tactic.QuotientFreeRing
import CCL.Progressive.LogRange

/-!
# Automatic positive-real charting for a CCL logarithm

The input certificate supplies a displayed positive rational lower bound for
the real coordinate of every candidate at the current finite state.  One
explicit refinement makes the current ball small relative to that bound.
The rational real coordinate of the refined ball centre is then normalized
by a bounded dyadic scan, and every explicitly possible candidate at the
refined state is proved to land in the overlapping local logarithm chart.
The geometric ball may of course contain irrelevant non-real points; the
separate positive-real certificate excludes those from the process semantics.

This is branch data and finite error accounting only.  It neither selects a
point common to all refinements nor asserts a completed logarithm.  Its
purpose is to make positive-real logarithm an automatic CCL-to-CCL operator
on this certified domain: chart preparation, local logarithm, the finite
`log 2` correction, and every correction addition remain arithmetic CCL
names.
-/

namespace CCL.ProgressiveLogPositive

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Named := CCL.ProgressiveTransducer.Named
abbrev Direction := CCL.PositiveDyadic.Direction

open RFAP.ConstructiveGaussian.Gaussian

/-- Finite positive-real branch information at one displayed input state. -/
structure PositiveReal (input : Named) where
  lower : Coordinate
  lowerPositive : 0 < lower
  possible_real_lower : ∀ {value : Gaussian},
    input.process.Possible input.state value →
      value.im = 0 ∧ lower ≤ value.re

namespace PositiveReal

def exact (value : Coordinate) (positive : 0 < value) :
    PositiveReal (CCL.ProgressiveTransducer.Named.exact ⟨value, 0⟩) where
  lower := value
  lowerPositive := positive
  possible_real_lower := by
    intro candidate possible
    change candidate = ⟨value, 0⟩ at possible
    rw [possible]
    exact ⟨rfl, le_rfl⟩

end PositiveReal

def refinementDenominator : Coordinate := (2 * 2) * (2 * 2)

theorem refinementDenominator_pos : 0 < refinementDenominator := by
  unfold refinementDenominator
  exact RFAP.ConstructiveFraction.mul_pos_direct
    (RFAP.ConstructiveFraction.mul_pos_direct (by decide) (by decide))
    (RFAP.ConstructiveFraction.mul_pos_direct (by decide) (by decide))

def refinementSlack {input : Named} (positive : PositiveReal input) : Coordinate :=
  positive.lower / refinementDenominator

theorem refinementSlack_pos {input : Named} (positive : PositiveReal input) :
    0 < refinementSlack positive :=
  RFAP.ConstructiveFraction.div_pos_direct positive.lowerPositive
    refinementDenominator_pos

def refinementTarget {input : Named} (positive : PositiveReal input) : Coordinate :=
  refinementSlack positive ^ 2

theorem refinementTarget_pos {input : Named} (positive : PositiveReal input) :
    0 < refinementTarget positive :=
  RFAP.ConstructiveFraction.pow_pos_direct (refinementSlack_pos positive) 2

def refinedState {input : Named} (positive : PositiveReal input) :
    input.process.State :=
  input.process.refine input.state (refinementTarget positive)
    (refinementTarget_pos positive)

def refinedInput {input : Named} (positive : PositiveReal input) : Named :=
  { process := input.process
    state := refinedState positive }

theorem refined_possible_at_start {input : Named} (positive : PositiveReal input)
    {value : Gaussian}
    (possible : input.process.Possible (refinedState positive) value) :
    input.process.Possible input.state value :=
  input.process.refine_persists input.state (refinementTarget positive)
    (refinementTarget_pos positive) possible

theorem refined_possible_real_lower {input : Named}
    (positive : PositiveReal input) {value : Gaussian}
    (possible : input.process.Possible (refinedState positive) value) :
    value.im = 0 ∧ positive.lower ≤ value.re :=
  positive.possible_real_lower (refined_possible_at_start positive possible)

def refinedCenter {input : Named} (positive : PositiveReal input) : Gaussian :=
  (input.process.ball (refinedState positive)).center

private theorem re_sub_sq_le_normSq (value center : Gaussian) :
    (value.re - center.re) ^ 2 ≤ normSq (value - center) := by
  rw [normSq]
  simp only [sub_re, sub_im]
  exact le_add_of_nonneg_right
    (RFAP.ConstructiveFraction.sq_nonneg_direct (value.im - center.im))

theorem candidate_deviation_sq {input : Named}
    (positive : PositiveReal input) {value : Gaussian}
    (possible : input.process.Possible (refinedState positive) value) :
    (value.re - (refinedCenter positive).re) ^ 2 ≤
      refinementSlack positive ^ 2 := by
  exact (re_sub_sq_le_normSq value (refinedCenter positive)).trans
    ((input.process.possible_inside possible).trans
      (input.process.accurate input.state (refinementTarget positive)
        (refinementTarget_pos positive)).le)

theorem candidate_deviation {input : Named} (positive : PositiveReal input)
    {value : Gaussian}
    (possible : input.process.Possible (refinedState positive) value) :
    -refinementSlack positive ≤ value.re - (refinedCenter positive).re ∧
      value.re - (refinedCenter positive).re ≤ refinementSlack positive := by
  have squares := candidate_deviation_sq positive possible
  exact
    ⟨RFAP.ConstructiveFraction.neg_le_of_sq_le_sq_direct
        (refinementSlack_pos positive).le squares,
      RFAP.ConstructiveFraction.le_of_sq_le_sq_direct
        (refinementSlack_pos positive).le squares⟩

theorem refinementSlack_mul_eight {input : Named}
    (positive : PositiveReal input) :
    refinementSlack positive * 8 = positive.lower / 2 := by
  apply RFAP.ConstructiveFraction.mul_right_cancel_of_ne (c := 2) (by decide)
  calc
    (refinementSlack positive * 8) * 2 =
        refinementSlack positive * refinementDenominator := by
      unfold refinementDenominator
      ring1
    _ = positive.lower :=
      RFAP.ConstructiveFraction.div_mul_cancel_of_ne positive.lower
        refinementDenominator refinementDenominator_pos.ne'
    _ = (positive.lower / 2) * 2 :=
      (RFAP.ConstructiveFraction.div_mul_cancel_of_ne positive.lower 2
        (by decide)).symm

theorem refinementSlack_le_half {input : Named} (positive : PositiveReal input) :
    refinementSlack positive ≤ positive.lower / 2 := by
  calc
    refinementSlack positive = refinementSlack positive * 1 :=
      (RFAP.ConstructiveFraction.mul_one_direct _).symm
    _ ≤ refinementSlack positive * 8 :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct (by decide)
        (refinementSlack_pos positive).le
    _ = positive.lower / 2 := refinementSlack_mul_eight positive

private theorem two_halves (value : Coordinate) : value / 2 + value / 2 = value := by
  calc
    value / 2 + value / 2 = (value / 2) * 2 := by ring1
    _ = value := RFAP.ConstructiveFraction.div_mul_cancel_of_ne value 2
      (by decide)

theorem half_lower_le_refinedCenter {input : Named}
    (positive : PositiveReal input) :
    positive.lower / 2 ≤ (refinedCenter positive).re := by
  let witness := (input.process.witness (refinedState positive)).val
  have witnessPossible :
      input.process.Possible (refinedState positive) witness :=
    (input.process.witness (refinedState positive)).property
  have witnessLower : positive.lower ≤ witness.re :=
    (refined_possible_real_lower positive witnessPossible).2
  have deviationUpper :
      witness.re - (refinedCenter positive).re ≤ refinementSlack positive :=
    (candidate_deviation positive witnessPossible).2
  have lowerLeCenterSlack :
      positive.lower ≤
        (refinedCenter positive).re + refinementSlack positive := by
    calc
      positive.lower ≤ witness.re := witnessLower
      _ = (witness.re - (refinedCenter positive).re) +
          (refinedCenter positive).re := by ring1
      _ ≤ refinementSlack positive + (refinedCenter positive).re :=
        RFAP.ConstructiveFraction.add_le_add_right_direct deviationUpper _
      _ = (refinedCenter positive).re + refinementSlack positive := by ring1
  apply RFAP.ConstructiveFraction.le_of_add_le_add_right_direct
    (c := refinementSlack positive)
  calc
    positive.lower / 2 + refinementSlack positive =
        refinementSlack positive + positive.lower / 2 := by ring1
    _ ≤ positive.lower / 2 + positive.lower / 2 :=
      RFAP.ConstructiveFraction.add_le_add_right_direct
        (refinementSlack_le_half positive) _
    _ = positive.lower := two_halves positive.lower
    _ ≤ (refinedCenter positive).re + refinementSlack positive :=
      lowerLeCenterSlack

theorem refinedCenter_pos {input : Named} (positive : PositiveReal input) :
    0 < (refinedCenter positive).re :=
  (RFAP.ConstructiveFraction.div_pos_direct positive.lowerPositive
    (by decide)).trans_le (half_lower_le_refinedCenter positive)

def centerNormalization {input : Named} (positive : PositiveReal input) :
    CCL.PositiveDyadic.Normalization (refinedCenter positive).re :=
  CCL.PositiveDyadic.normalize (refinedCenter positive).re
    (refinedCenter_pos positive)

theorem scaledSlack_le_quarter {input : Named} (positive : PositiveReal input) :
    CCL.PositiveDyadic.factor
          (centerNormalization positive).direction
          (centerNormalization positive).exponent *
        refinementSlack positive ≤ 1 / 4 := by
  let normalization := centerNormalization positive
  let scalar := CCL.PositiveDyadic.factor
    normalization.direction normalization.exponent
  have scalarPositive : 0 < scalar :=
    CCL.PositiveDyadic.factor_pos _ _
  apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct
    (c := (8 : Coordinate))
  · calc
      (scalar * refinementSlack positive) * 8 =
          scalar * (refinementSlack positive * 8) := by ring1
      _ = scalar * (positive.lower / 2) := by
        rw [refinementSlack_mul_eight]
      _ ≤ scalar * (refinedCenter positive).re :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          (half_lower_le_refinedCenter positive) scalarPositive.le
      _ = CCL.PositiveDyadic.normalized
          (refinedCenter positive).re normalization.direction
            normalization.exponent :=
        (CCL.PositiveDyadic.normalized_eq_factor_mul _ _ _).symm
      _ ≤ 3 / 2 := normalization.upper
      _ ≤ 2 := by decide
      _ = (1 / 4 : Coordinate) * 8 := by decide
  · decide

theorem automaticLocalChart {input : Named} (positive : PositiveReal input) :
    CCL.ProgressiveLog.Chart
      (CCL.ProgressiveLogRange.scaledInput
        (refinedInput positive) (centerNormalization positive).direction
          (centerNormalization positive).exponent) where
  possible_real_chart := by
    intro value possible
    rcases possible with ⟨scaleValue, sourceValue,
      scalePossible, sourcePossible, rfl⟩
    change scaleValue =
      CCL.ProgressiveLogRange.dyadicFactor
        (centerNormalization positive).direction
        (centerNormalization positive).exponent at scalePossible
    subst scaleValue
    let normalization := centerNormalization positive
    let scalar := CCL.PositiveDyadic.factor
      normalization.direction normalization.exponent
    have sourceData := refined_possible_real_lower positive sourcePossible
    have deviation := candidate_deviation positive sourcePossible
    have scalarPositive : 0 < scalar :=
      CCL.PositiveDyadic.factor_pos _ _
    have scaledDeviationLower :
        -(scalar * refinementSlack positive) ≤
          scalar * sourceValue.re - scalar * (refinedCenter positive).re := by
      have scaled := RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        deviation.1 scalarPositive.le
      calc
        -(scalar * refinementSlack positive) =
            scalar * (-refinementSlack positive) := by ring1
        _ ≤ scalar * (sourceValue.re - (refinedCenter positive).re) := scaled
        _ = scalar * sourceValue.re - scalar * (refinedCenter positive).re := by
          ring1
    have scaledDeviationUpper :
        scalar * sourceValue.re - scalar * (refinedCenter positive).re ≤
          scalar * refinementSlack positive := by
      have scaled := RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        deviation.2 scalarPositive.le
      calc
        scalar * sourceValue.re - scalar * (refinedCenter positive).re =
            scalar * (sourceValue.re - (refinedCenter positive).re) := by
          ring1
        _ ≤ scalar * refinementSlack positive := scaled
    have centerIdentity :
        scalar * (refinedCenter positive).re =
          CCL.PositiveDyadic.normalized
            (refinedCenter positive).re normalization.direction
              normalization.exponent :=
      (CCL.PositiveDyadic.normalized_eq_factor_mul _ _ _).symm
    have lower : 1 / 2 ≤ scalar * sourceValue.re := by
      calc
        (1 / 2 : Coordinate) = 3 / 4 - 1 / 4 := by decide
        _ ≤ CCL.PositiveDyadic.normalized
              (refinedCenter positive).re normalization.direction
                normalization.exponent -
            scalar * refinementSlack positive :=
          RFAP.ConstructiveFraction.sub_le_sub_direct normalization.lower (scaledSlack_le_quarter positive)
        _ = scalar * (refinedCenter positive).re -
            scalar * refinementSlack positive := by rw [centerIdentity]
        _ ≤ scalar * sourceValue.re := by
          apply RFAP.ConstructiveFraction.le_of_add_le_add_right_direct
            (c := -(scalar * (refinedCenter positive).re))
          calc
            (scalar * (refinedCenter positive).re -
                scalar * refinementSlack positive) +
                -(scalar * (refinedCenter positive).re) =
                -(scalar * refinementSlack positive) := by ring1
            _ ≤ scalar * sourceValue.re -
                scalar * (refinedCenter positive).re := scaledDeviationLower
            _ = scalar * sourceValue.re +
                -(scalar * (refinedCenter positive).re) := by ring1
    have upper : scalar * sourceValue.re ≤ 2 := by
      calc
        scalar * sourceValue.re ≤
            scalar * (refinedCenter positive).re +
              scalar * refinementSlack positive := by
          apply RFAP.ConstructiveFraction.le_of_add_le_add_right_direct
            (c := -(scalar * (refinedCenter positive).re))
          calc
            scalar * sourceValue.re +
                -(scalar * (refinedCenter positive).re) =
                scalar * sourceValue.re -
                  scalar * (refinedCenter positive).re := by ring1
            _ ≤ scalar * refinementSlack positive := scaledDeviationUpper
            _ = (scalar * (refinedCenter positive).re +
                scalar * refinementSlack positive) +
                -(scalar * (refinedCenter positive).re) := by ring1
        _ = CCL.PositiveDyadic.normalized
              (refinedCenter positive).re normalization.direction
                normalization.exponent +
            scalar * refinementSlack positive := by rw [centerIdentity]
        _ ≤ 3 / 2 + 1 / 4 :=
          add_le_add normalization.upper (scaledSlack_le_quarter positive)
        _ ≤ 2 := by decide
    exact
      ⟨CCL.ProgressiveLogRange.dyadicFactor_mul_im_of_real
          normalization.direction normalization.exponent sourceData.1,
        by
          rw [CCL.ProgressiveLogRange.dyadicFactor_mul_re]
          exact lower,
        by
          rw [CCL.ProgressiveLogRange.dyadicFactor_mul_re]
          exact upper⟩

def automaticChart {input : Named} (positive : PositiveReal input) :
    CCL.ProgressiveLogRange.DyadicChart (refinedInput positive) :=
  { direction := (centerNormalization positive).direction
    exponent := (centerNormalization positive).exponent
    localChart := automaticLocalChart positive }

/-- Total positive-real logarithm entry point from a finite lower-bound
certificate. -/
def named (input : Named) (positive : PositiveReal input) : Named :=
  CCL.ProgressiveLogRange.named
    (refinedInput positive) (automaticChart positive)

theorem productive (input : Named) (positive : PositiveReal input)
    (count : Nat) :
    (named input positive).machine.emitted.IsPrefix
        (CCL.ProgressiveTransducer.advance
          (named input positive).machine count).emitted ∧
      (CCL.ProgressiveTransducer.advance
          (named input positive).machine count).emitted.length = count :=
  (named input positive).productive count

end CCL.ProgressiveLogPositive
