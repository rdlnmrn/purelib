module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Measure.Content.AbsoluteContinuity.Basic
import Purelib.Measure.Content.Basic
import Purelib.Measure.Content.Integral
import Purelib.Measure.Content.Operations

public import Purelib.Measure.Content.Normalization.Basic
import Purelib.Measure.Distribution.Equivalence
import Purelib.Measure.Distribution.Basic
import Purelib.Data.List.Event
import Purelib.Measure.Distribution.Expectation
import Purelib.Measure.Distribution.Kernel.Basic
import Purelib.Measure.Distribution.Mixture.Basic
public import Purelib.Measure.Distribution.Conditioning.Mean
import Purelib.Measure.Weighted.Basic
import Purelib.Measure.Distribution.Conditioning.Basic
import Purelib.Measure.Content.Equivalence
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

/-!
# Operations commuting with finite normalization

Positive finite contents normalize by one explicit rational total.  Exact
pushforward commutes with that calculation at the level of every executable
event and rational observable, even when the resulting atom tables are laid
out through different constructors.
-/

@[expose] public section

namespace Purelib.Measure

namespace Content

section
open Purelib.Data.Rat
/-- The sum of two positive rationals is positive. -/
private theorem add_pos_direct {left right : Fraction.Rational}
    (leftPositive : 0 < left) (rightPositive : 0 < right) :
    0 < left + right := by
  simpa only [zero_add] using
    Fraction.Order.Arithmetic.add_lt_add_direct
      leftPositive rightPositive

/-- Dividing numerator and denominator by the same nonzero rational preserves their quotient. -/
private theorem div_div_same_right
    (numerator denominator common : Fraction.Rational) (commonNonzero : common ≠ 0) :
    (numerator / common) / (denominator / common) =
      numerator / denominator := by
  calc
    (numerator / common) / (denominator / common) =
        (common⁻¹ * numerator) / (common⁻¹ * denominator) := by
      simp only [Fraction.Field.div_eq_mul_inv_direct]
      rw [Fraction.Field.mul_comm numerator common⁻¹,
        Fraction.Field.mul_comm denominator common⁻¹]
    _ = numerator / denominator :=
      Fraction.Field.mul_div_mul_left_direct common⁻¹
        numerator denominator
        (Fraction.Field.inv_ne_zero_direct commonNonzero)

end

section
open Purelib
open Purelib.Data.Rat
/-- Retain the left total's fraction of a positive combined content total as a certified mixing coefficient. -/
def appendMixingWeight {α : Type} (left right : Measure.Content α)
    (sumPositive : 0 < left.total + right.total) : MixingWeight where
  coefficient := left.total / (left.total + right.total)
  nonnegative := Fraction.Order.Field.div_nonneg_direct
    (totalWeight_nonneg left.atoms) sumPositive.le
  atMostOne := by
    apply (Fraction.Order.Field.div_le_iff_pos sumPositive).2
    rw [Fraction.Field.one_mul]
    exact le_add_of_nonneg_right (totalWeight_nonneg right.atoms)

/-- The complementary append coefficient equals the right total's fraction of the same combined total. -/
theorem appendMixingWeight_complement {α : Type}
    (left right : Measure.Content α)
    (sumPositive : 0 < left.total + right.total) :
    (appendMixingWeight left right sumPositive).complement =
      right.total / (left.total + right.total) := by
  let sum := left.total + right.total
  have sumNonzero : sum ≠ 0 := sumPositive.ne'
  have cancels : sum * sum⁻¹ = 1 :=
    Fraction.Field.mul_inv_cancel sum sumNonzero
  change 1 - left.total * sum⁻¹ = right.total * sum⁻¹
  rw [← cancels]
  calc
    sum * sum⁻¹ - left.total * sum⁻¹ =
        (sum - left.total) * sum⁻¹ := (sub_mul _ _ _).symm
    _ = right.total * sum⁻¹ := by
      congr 1
      dsimp only [sum]
      ring1

end

open Purelib.Data.Rat in
/-- A nonzero component's total fraction times its normalized reading equals that reading divided by combined total. -/
private theorem contentFraction_mul_normalized
    (total value combined : Fraction.Rational) (totalNonzero : total ≠ 0) :
    (total / combined) * (value / total) = value / combined := by
  change (total * combined⁻¹) * (value * total⁻¹) = value * combined⁻¹
  calc
    (total * combined⁻¹) * (value * total⁻¹) =
        (total * combined⁻¹) * (total⁻¹ * value) := by
      rw [Fraction.Field.mul_comm value total⁻¹]
    _ = (total * total⁻¹) * (combined⁻¹ * value) :=
      Fraction.Field.mul_pair_swap _ _ _ _
    _ = 1 * (combined⁻¹ * value) := by
      rw [Fraction.Field.mul_inv_cancel total totalNonzero]
    _ = combined⁻¹ * value := Fraction.Field.one_mul _
    _ = value * combined⁻¹ := Fraction.Field.mul_comm _ _

open Purelib in
/-- Mapping positive-mass content before normalization is evaluation equivalent to mapping its original normalized law.
-/
theorem map_normalize_evaluationEquivalent {α β : Type}
    (content : Measure.Content α) (positive : 0 < content.total)
    (function : α → β) :
    Distribution.EvaluationEquivalent
      ((content.map function).normalize (by
        rw [content.map_total]
        exact positive))
      ((content.normalize positive).map function) where
  probability_eq event := by
    rw [Content.normalize_probability,
      content.map_measure,
      content.map_total,
      Distribution.map_probability,
      Content.normalize_probability]
  expectation_eq value := by
    rw [Content.normalize_expectation,
      content.map_integral,
      content.map_total,
      Distribution.map_expectation,
      Content.normalize_expectation]

open Purelib
open Purelib.Data.Rat
/-- The normalized law's conditional mean is the original restricted integral divided by original event mass. -/
theorem normalize_conditionalMean {α : Type}
    (content : Measure.Content α) (positive : 0 < content.total)
    (event : α → Bool) (value : α → Fraction.Rational) :
    (content.normalize positive).conditionalMean event value =
      (content.restrict event).integral value / content.measure event := by
  unfold Distribution.conditionalMean Distribution.eventIntegral
  rw [Content.normalize_expectation,
    Content.normalize_probability,
    ← content.restrict_integral event value]
  exact div_div_same_right _ _ content.total positive.ne'

/-- Normalizing a positive-mass event restriction is evaluation equivalent to conditioning the original normalized law
on that event. -/
theorem restrict_normalize_evaluationEquivalent {α : Type}
    (content : Measure.Content α) (positive : 0 < content.total)
    (event : α → Bool) (measurePositive : 0 < content.measure event) :
    Distribution.EvaluationEquivalent
      ((content.restrict event).normalize (by
        rw [content.restrict_total]
        exact measurePositive))
      ((content.normalize positive).conditioned event (by
        rw [Content.normalize_probability]
        exact Fraction.Order.Field.div_pos_direct
          measurePositive positive)) := by
  apply Distribution.EvaluationEquivalent.of_expectation_eq
  intro value
  rw [Content.normalize_expectation,
    content.restrict_total,
    Distribution.conditioned_expectation_eq_conditionalMean,
    content.normalize_conditionalMean positive event value]

/-- Normalizing the product of two positive-mass contents is evaluation equivalent to the product of their exact
normalized laws. -/
theorem product_normalize_evaluationEquivalent {α β : Type}
    (left : Measure.Content α) (right : Measure.Content β)
    (leftPositive : 0 < left.total) (rightPositive : 0 < right.total) :
    Distribution.EvaluationEquivalent
      ((left.product right).normalize (by
        rw [left.product_total]
        exact Fraction.Order.Arithmetic.mul_pos_direct
          leftPositive rightPositive))
      ((left.normalize leftPositive).product
        (right.normalize rightPositive)) := by
  apply Distribution.EvaluationEquivalent.of_expectation_eq
  intro value
  let iterated := left.integral (fun leftItem =>
    right.integral (fun rightItem => value (leftItem, rightItem)))
  calc
    ((left.product right).normalize (by
        rw [left.product_total]
        exact Fraction.Order.Arithmetic.mul_pos_direct
          leftPositive rightPositive)).expectation value =
        iterated / (left.total * right.total) := by
      rw [Content.normalize_expectation,
        left.product_total, left.product_integral]
    _ =
        (right.total⁻¹ * iterated) / left.total := by
      calc
        iterated / (left.total * right.total) =
        iterated * (left.total * right.total)⁻¹ := rfl
        _ = iterated * (left.total⁻¹ * right.total⁻¹) := by
          rw [Fraction.Field.inv_mul_direct]
        _ = (iterated * left.total⁻¹) * right.total⁻¹ :=
          (Fraction.Field.mul_assoc _ _ _).symm
        _ = right.total⁻¹ * (iterated * left.total⁻¹) :=
          Fraction.Field.mul_comm _ _
        _ = (right.total⁻¹ * iterated) * left.total⁻¹ :=
          (Fraction.Field.mul_assoc _ _ _).symm
        _ = (right.total⁻¹ * iterated) / left.total := rfl
    _ = left.integral (fun leftItem =>
          right.total⁻¹ * right.integral
            (fun rightItem => value (leftItem, rightItem))) /
        left.total := by
      rw [left.integral_scale]
    _ = left.integral (fun leftItem =>
          right.integral (fun rightItem => value (leftItem, rightItem)) /
            right.total) / left.total := by
      apply congrArg (fun numerator => numerator / left.total)
      apply left.integral_congr
      intro leftItem
      rw [Fraction.Field.div_eq_mul_inv_direct,
        Fraction.Field.mul_comm]
    _ = (left.normalize leftPositive).expectation (fun leftItem =>
          right.integral (fun rightItem => value (leftItem, rightItem)) /
            right.total) :=
      (Content.normalize_expectation left leftPositive _).symm
    _ = (left.normalize leftPositive).expectation (fun leftItem =>
          (right.normalize rightPositive).expectation
            (fun rightItem => value (leftItem, rightItem))) := by
      apply (left.normalize leftPositive).expectation_congr
      intro leftItem
      exact (Content.normalize_expectation right rightPositive _).symm
    _ = ((left.normalize leftPositive).product
          (right.normalize rightPositive)).expectation value :=
      (Distribution.product_expectation_iterated
        (left.normalize leftPositive) (right.normalize rightPositive)
        value).symm

/-- Normalizing appended positive-mass contents is evaluation equivalent to mixing their normalized laws by the exact
original mass fractions.

The comparison retains both original inputs, their individual positive totals and the mixing coefficient computed from
those same totals. -/
theorem append_normalize_evaluationEquivalent {α : Type}
    (left right : Measure.Content α)
    (leftPositive : 0 < left.total) (rightPositive : 0 < right.total) :
    Distribution.EvaluationEquivalent
      ((left.append right).normalize (by
        rw [left.append_total]
        simpa only [zero_add] using
          Fraction.Order.Arithmetic.add_lt_add_direct
            leftPositive rightPositive))
      ((left.normalize leftPositive).mixture
        (right.normalize rightPositive)
        (appendMixingWeight left right (by
          simpa only [zero_add] using
            Fraction.Order.Arithmetic.add_lt_add_direct
              leftPositive rightPositive))) := by
  let sumPositive := add_pos_direct leftPositive rightPositive
  apply Distribution.EvaluationEquivalent.of_expectation_eq
  intro value
  rw [Content.normalize_expectation,
    left.append_integral, left.append_total,
    Distribution.mixture_expectation,
    Content.normalize_expectation,
    Content.normalize_expectation,
    appendMixingWeight_complement left right sumPositive]
  change
    (left.integral value + right.integral value) /
        (left.total + right.total) =
      (left.total / (left.total + right.total)) *
          (left.integral value / left.total) +
        (right.total / (left.total + right.total)) *
          (right.integral value / right.total)
  rw [contentFraction_mul_normalized left.total (left.integral value)
      (left.total + right.total) leftPositive.ne',
    contentFraction_mul_normalized right.total (right.integral value)
      (left.total + right.total) rightPositive.ne']
  change (left.integral value + right.integral value) *
      (left.total + right.total)⁻¹ =
    left.integral value * (left.total + right.total)⁻¹ +
      right.integral value * (left.total + right.total)⁻¹
  exact add_mul _ _ _

end Content

end Purelib.Measure
