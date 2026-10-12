module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order
public import Purelib.Measure.Distribution.Moments.Basic
import Purelib.Measure.Distribution.Moments.Covariance
import Purelib.Measure.Distribution.Stability
import Purelib.Measure.Distribution.Expectation
import Purelib.Measure.Weighted.Basic
import Purelib.Measure.Weighted.Integral
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Measure.Distribution.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

section
@[expose] public section

/-!
# One-sided finite moment inequalities

Cantelli's inequality improves two-sided Chebyshev for a displayed one-sided
deviation event.  The proof below is entirely finite: compare the centered
observable with the event indicator, apply the already finite covariance
Cauchy--Schwarz inequality, and cancel one explicitly positive rational
probability when necessary.
-/

namespace Purelib.Measure

namespace Distribution

open Purelib.Data.Rat
/-- An event whose selected occurrences exceed the mean by a positive threshold satisfies the multiplied one-sided
variance bound.

The original event probability times variance plus threshold squared is at most the original variance; the proof
includes the zero-probability case explicitly. -/
theorem cantelli_mul_probability_le_variance {α : Type}
    (distribution : Distribution α) (event : α → Bool)
    (value : α → Fraction.Rational) (threshold : Fraction.Rational)
    (positive : 0 < threshold)
    (selectedDeviation : ∀ atom, atom ∈ distribution.atoms →
      event atom.item = true →
        threshold ≤ value atom.item - distribution.expectation value) :
    (distribution.variance value + threshold ^ 2) *
        distribution.probability event ≤
      distribution.variance value := by
  let centeredIndicator : α → Fraction.Rational := fun item =>
    (value item - distribution.expectation value) * indicator event item
  have centeredIndicator_nonnegative : ∀ atom,
      atom ∈ distribution.atoms → 0 ≤ centeredIndicator atom.item := by
    intro atom atomMember
    cases selected : event atom.item
    · simp only [centeredIndicator, indicator, selected, mul_zero]
      exact le_rfl
    · simp only [centeredIndicator, indicator, selected, mul_one]
      exact positive.le.trans
        (selectedDeviation atom atomMember selected)
  have centeredIndicator_selected : ∀ atom,
      atom ∈ distribution.atoms → event atom.item = true →
        threshold ≤ centeredIndicator atom.item := by
    intro atom atomMember selected
    simp only [centeredIndicator, indicator, selected, mul_one]
    exact selectedDeviation atom atomMember selected
  have thresholdCross :
      threshold * distribution.probability event ≤
        distribution.expectation centeredIndicator :=
    threshold_mul_eventWeight_le_expectationWeight distribution.atoms event
      centeredIndicator threshold centeredIndicator_nonnegative
      centeredIndicator_selected
  have covarianceEq :
      distribution.covariance value (indicator event) =
        distribution.expectation centeredIndicator := by
    calc
      distribution.covariance value (indicator event) =
          distribution.expectation (fun item =>
            value item * indicator event item -
              distribution.expectation value * indicator event item) := by
        rw [distribution.covariance_eq_productMoment_sub_means,
          distribution.expectation_indicator, distribution.expectation_sub,
          distribution.expectation_scale,
          distribution.expectation_indicator]
      _ = distribution.expectation centeredIndicator :=
        distribution.expectation_congr _ _ (fun item => by
          dsimp only [centeredIndicator]
          ring1)
  have thresholdCovariance :
      threshold * distribution.probability event ≤
        distribution.covariance value (indicator event) := by
    rw [covarianceEq]
    exact thresholdCross
  have scaledNonnegative :
      0 ≤ threshold * distribution.probability event :=
    Fraction.Order.Arithmetic.mul_nonneg_direct positive.le
      (distribution.probability_nonneg event)
  have squaredLower :
      (threshold * distribution.probability event) ^ 2 ≤
        distribution.covariance value (indicator event) ^ 2 :=
    Fraction.Order.Arithmetic.pow_le_pow_direct scaledNonnegative
      thresholdCovariance 2
  have indicatorSquare := distribution.expectation_congr
    (fun item => indicator event item ^ 2) (indicator event) (fun item => by
    cases selected : event item <;>
      simp only [indicator, selected] <;> ring1)
  have indicatorVariance :
      distribution.variance (indicator event) =
        distribution.probability event *
          (1 - distribution.probability event) := by
    rw [distribution.variance_eq_secondMoment_sub_sq,
      indicatorSquare, distribution.expectation_indicator]
    ring1
  have covarianceUpper :=
    distribution.covariance_sq_le_variance_mul value (indicator event)
  rw [indicatorVariance] at covarianceUpper
  have combined :
      (threshold * distribution.probability event) ^ 2 ≤
        distribution.variance value *
          (distribution.probability event *
            (1 - distribution.probability event)) :=
    squaredLower.trans covarianceUpper
  by_cases probabilityZero : distribution.probability event = 0
  · rw [probabilityZero, mul_zero]
    exact distribution.variance_nonneg value
  · have probabilityPositive : 0 < distribution.probability event :=
      lt_of_le_of_ne (distribution.probability_nonneg event)
        (Ne.symm probabilityZero)
    have multiplied :
        ((distribution.variance value + threshold ^ 2) *
            distribution.probability event) *
              distribution.probability event ≤
          distribution.variance value * distribution.probability event := by
      calc
        ((distribution.variance value + threshold ^ 2) *
              distribution.probability event) *
            distribution.probability event =
            (threshold * distribution.probability event) ^ 2 +
              distribution.variance value *
                distribution.probability event ^ 2 := by
          ring1
        _ ≤ distribution.variance value *
              (distribution.probability event *
                (1 - distribution.probability event)) +
            distribution.variance value *
              distribution.probability event ^ 2 :=
          add_le_add combined le_rfl
        _ = distribution.variance value *
            distribution.probability event := by
          ring1
    apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct
      (c := distribution.probability event)
    · exact multiplied
    · exact probabilityPositive

/-- Positive upper deviation on every selected original occurrence bounds event probability by variance divided by
variance plus threshold squared. -/
theorem cantelli_bound {α : Type}
    (distribution : Distribution α) (event : α → Bool)
    (value : α → Fraction.Rational) (threshold : Fraction.Rational)
    (positive : 0 < threshold)
    (selectedDeviation : ∀ atom, atom ∈ distribution.atoms →
      event atom.item = true →
        threshold ≤ value atom.item - distribution.expectation value) :
    distribution.probability event ≤
      distribution.variance value /
        (distribution.variance value + threshold ^ 2) := by
  have denominatorPositive :
      0 < distribution.variance value + threshold ^ 2 :=
    lt_of_lt_of_le
      (Fraction.Order.Arithmetic.pow_pos_direct positive 2)
      (le_add_of_nonneg_left (distribution.variance_nonneg value))
  apply (Fraction.Order.Field.le_div_iff_pos denominatorPositive).2
  calc
    distribution.probability event *
          (distribution.variance value + threshold ^ 2) =
        (distribution.variance value + threshold ^ 2) *
          distribution.probability event := by
      ring1
    _ ≤ distribution.variance value :=
      distribution.cantelli_mul_probability_le_variance event value
        threshold positive selectedDeviation

/-- Positive lower deviation on every selected original occurrence bounds event probability by variance divided by
variance plus threshold squared. -/
theorem cantelli_lower_bound {α : Type}
    (distribution : Distribution α) (event : α → Bool)
    (value : α → Fraction.Rational) (threshold : Fraction.Rational)
    (positive : 0 < threshold)
    (selectedDeviation : ∀ atom, atom ∈ distribution.atoms →
      event atom.item = true →
        threshold ≤ distribution.expectation value - value atom.item) :
    distribution.probability event ≤
      distribution.variance value /
        (distribution.variance value + threshold ^ 2) := by
  let negated : α → Fraction.Rational := fun item => -value item
  have negatedMean : distribution.expectation negated =
      -distribution.expectation value := by
    calc
      distribution.expectation negated =
          distribution.expectation (fun item =>
            (-1 : Fraction.Rational) * value item) :=
        distribution.expectation_congr _ _ (fun item => by
          dsimp only [negated]
          ring1)
      _ = (-1 : Fraction.Rational) * distribution.expectation value :=
        distribution.expectation_scale (-1) value
      _ = -distribution.expectation value := by ring1
  have selectedNegated : ∀ atom, atom ∈ distribution.atoms →
      event atom.item = true →
        threshold ≤ negated atom.item - distribution.expectation negated := by
    intro atom atomMember selected
    rw [negatedMean]
    dsimp only [negated]
    have lower := selectedDeviation atom atomMember selected
    calc
      threshold ≤ distribution.expectation value - value atom.item := lower
      _ = -value atom.item - -distribution.expectation value := by
        ring1
  have upper := distribution.cantelli_bound event negated threshold positive
    selectedNegated
  have negatedVariance : distribution.variance negated =
      distribution.variance value := by
    calc
      distribution.variance negated =
          distribution.variance (fun item =>
            (-1 : Fraction.Rational) * value item) :=
        distribution.variance_congr _ _ (fun item => by
          dsimp only [negated]
          ring1)
      _ = (-1 : Fraction.Rational) ^ 2 * distribution.variance value :=
        distribution.variance_scale (-1) value
      _ = distribution.variance value := by ring1
  rw [negatedVariance] at upper
  exact upper
end Distribution

end Purelib.Measure

end
