module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Data.Rat.Fraction.Compatibility
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order
import Purelib.Measure.Distribution.Moments.Basic
import Purelib.Measure.Distribution.Basic
public import Purelib.Measure.Distribution.Expectation
import Purelib.Measure.Distribution.Lp.L2
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Measure.Weighted.Basic
import Purelib.Measure.Weighted.Integral
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
/-- A nonnegative observable whose complement values stay below a mean fraction satisfies the multiplied Paley–Zygmund
bound.

For a fraction between zero and one, the squared complementary mean fraction is at most the second moment times the
supplied event's probability. -/
theorem paleyZygmund_mul {α : Type}
    (distribution : Distribution α) (event : α → Bool)
    (value : α → Fraction.Rational) (fraction : Fraction.Rational)
    (fractionNonnegative : 0 ≤ fraction) (fractionAtMostOne : fraction ≤ 1)
    (valueNonnegative : ∀ atom, atom ∈ distribution.atoms →
      0 ≤ value atom.item)
    (outsideUpper : ∀ atom, atom ∈ distribution.atoms →
      event atom.item = false →
        value atom.item ≤ fraction * distribution.expectation value) :
    (1 - fraction) ^ 2 * distribution.expectation value ^ 2 ≤
      distribution.expectation (fun item => value item ^ 2) *
        distribution.probability event := by
  let selectedValue : α → Fraction.Rational := fun item =>
    value item * indicator event item
  have meanNonnegative : 0 ≤ distribution.expectation value :=
    distribution.expectation_nonneg value valueNonnegative
  have fractionMeanNonnegative :
      0 ≤ fraction * distribution.expectation value :=
    Fraction.Order.Arithmetic.mul_nonneg_direct fractionNonnegative
      meanNonnegative
  have pointwise : ∀ atom, atom ∈ distribution.atoms →
      value atom.item ≤ selectedValue atom.item +
        fraction * distribution.expectation value := by
    intro atom atomMember
    cases selected : event atom.item
    · simp only [selectedValue, indicator, selected, mul_zero, zero_add]
      exact outsideUpper atom atomMember selected
    · simp only [selectedValue, indicator, selected, mul_one]
      exact le_add_of_nonneg_right fractionMeanNonnegative
  have averaged := distribution.expectation_mono value
    (fun item => selectedValue item +
      fraction * distribution.expectation value) pointwise
  rw [distribution.expectation_add,
    distribution.expectation_constant] at averaged
  have selectedLower :
      (1 - fraction) * distribution.expectation value ≤
        distribution.expectation selectedValue := by
    have shifted := Fraction.Order.Arithmetic.sub_le_sub_right_direct averaged
      (fraction * distribution.expectation value)
    calc
      (1 - fraction) * distribution.expectation value =
          distribution.expectation value -
            fraction * distribution.expectation value := by
        ring1
      _ ≤ (distribution.expectation selectedValue +
            fraction * distribution.expectation value) -
          fraction * distribution.expectation value := shifted
      _ = distribution.expectation selectedValue := by
        ring1
  have complementNonnegative : 0 ≤ 1 - fraction :=
    Fraction.Order.Arithmetic.sub_nonneg_direct fractionAtMostOne
  have selectedLowerNonnegative :
      0 ≤ (1 - fraction) * distribution.expectation value :=
    Fraction.Order.Arithmetic.mul_nonneg_direct complementNonnegative
      meanNonnegative
  have squaredLower :
      ((1 - fraction) * distribution.expectation value) ^ 2 ≤
        distribution.expectation selectedValue ^ 2 :=
    Fraction.Order.Arithmetic.pow_le_pow_direct selectedLowerNonnegative
      selectedLower 2
  have productPointwise : (fun item =>
      value item * indicator event item) = selectedValue := rfl
  have cauchy := distribution.productExpectation_sq_le_poweredL2_mul
    value (indicator event)
  rw [productPointwise] at cauchy
  have indicatorSquare := distribution.expectation_congr
    (fun item => indicator event item ^ 2) (indicator event) (fun item => by
    cases selected : event item <;>
      simp only [indicator, selected] <;> ring1)
  have valueL2 : distribution.poweredL2 value =
      distribution.expectation (fun item => value item ^ 2) := rfl
  have indicatorL2 : distribution.poweredL2 (indicator event) =
      distribution.probability event := by
    calc
      distribution.poweredL2 (indicator event) =
          distribution.expectation (fun item => indicator event item ^ 2) :=
        rfl
      _ = distribution.expectation (indicator event) := by
        rw [indicatorSquare]
      _ = distribution.probability event :=
        distribution.expectation_indicator event
  rw [valueL2, indicatorL2] at cauchy
  calc
    (1 - fraction) ^ 2 * distribution.expectation value ^ 2 =
        ((1 - fraction) * distribution.expectation value) ^ 2 := by
      ring1
    _ ≤ distribution.expectation selectedValue ^ 2 := squaredLower
    _ ≤ distribution.expectation (fun item => value item ^ 2) *
        distribution.probability event := cauchy

/-- Decide whether an observable strictly exceeds the supplied fraction of its original expectation. -/
def aboveFractionOfMeanEvent {α : Type} (distribution : Distribution α)
    (value : α → Fraction.Rational) (fraction : Fraction.Rational) : α → Bool :=
  fun item => decide
    (fraction * distribution.expectation value < value item)

/-- For a nonnegative observable of positive mean, bound below the probability of exceeding a fraction of that mean.

The fraction lies between zero and one, and the lower bound divides the squared complementary mean fraction by the exact
second moment. -/
theorem paleyZygmund_bound {α : Type}
    (distribution : Distribution α) (value : α → Fraction.Rational)
    (fraction : Fraction.Rational)
    (fractionNonnegative : 0 ≤ fraction) (fractionAtMostOne : fraction ≤ 1)
    (valueNonnegative : ∀ atom, atom ∈ distribution.atoms →
      0 ≤ value atom.item)
    (meanPositive : 0 < distribution.expectation value) :
    (1 - fraction) ^ 2 * distribution.expectation value ^ 2 /
        distribution.expectation (fun item => value item ^ 2) ≤
      distribution.probability
        (distribution.aboveFractionOfMeanEvent value fraction) := by
  have secondMomentPositive :
      0 < distribution.expectation (fun item => value item ^ 2) := by
    exact (Fraction.Order.Arithmetic.pow_pos_direct meanPositive 2).trans_le
      (distribution.expectation_sq_le_secondMoment value)
  apply (Fraction.Order.Field.div_le_iff_pos secondMomentPositive).2
  have multiplicative := distribution.paleyZygmund_mul
    (distribution.aboveFractionOfMeanEvent value fraction) value fraction
    fractionNonnegative fractionAtMostOne valueNonnegative
    (by
      intro atom atomMember outside
      unfold aboveFractionOfMeanEvent at outside
      exact Fraction.Order.Arithmetic.le_of_not_gt_direct
        (decide_eq_false_iff_not.mp outside))
  calc
    (1 - fraction) ^ 2 * distribution.expectation value ^ 2 ≤
        distribution.expectation (fun item => value item ^ 2) *
          distribution.probability
            (distribution.aboveFractionOfMeanEvent value fraction) :=
      multiplicative
    _ = distribution.probability
          (distribution.aboveFractionOfMeanEvent value fraction) *
        distribution.expectation (fun item => value item ^ 2) := by
      ring1

end Distribution

end Purelib.Measure

end
