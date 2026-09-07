import mathlib.Tactic.QuotientFreeRing
import FiniteMeasure.Normalization
import FiniteMeasure.ContentOperations
import FiniteMeasure.ContentIntegral
import FiniteMeasure.DistributionEquivalence
import FiniteMeasure.PartitionExpectation

/-!
# Operations commuting with finite normalization

Positive finite contents normalize by one explicit rational total.  Exact
pushforward commutes with that calculation at the level of every executable
event and rational observable, even when the resulting atom tables are laid
out through different constructors.
-/

namespace FiniteMeasure

namespace FiniteContent

private theorem add_pos_direct {left right : Coordinate}
    (leftPositive : 0 < left) (rightPositive : 0 < right) :
    0 < left + right := by
  simpa only [zero_add] using
    RFAP.ConstructiveFraction.add_lt_add_direct
      leftPositive rightPositive

private theorem div_div_same_right
    (numerator denominator common : Coordinate) (commonNonzero : common ≠ 0) :
    (numerator / common) / (denominator / common) =
      numerator / denominator := by
  calc
    (numerator / common) / (denominator / common) =
        (common⁻¹ * numerator) / (common⁻¹ * denominator) := by
      simp only [RFAP.ConstructiveFraction.div_eq_mul_inv_direct]
      rw [RFAP.ConstructiveFraction.mul_comm numerator common⁻¹,
        RFAP.ConstructiveFraction.mul_comm denominator common⁻¹]
    _ = numerator / denominator :=
      RFAP.ConstructiveFraction.mul_div_mul_left_direct common⁻¹
        numerator denominator
        (RFAP.ConstructiveFraction.inv_ne_zero_direct commonNonzero)

/-- Rational coefficient contributed by the left side of a positive
concatenated finite content. -/
def appendMixingWeight {α : Type} (left right : FiniteContent α)
    (sumPositive : 0 < left.total + right.total) : MixingWeight where
  coefficient := left.total / (left.total + right.total)
  nonnegative := RFAP.ConstructiveFraction.div_nonneg_direct
    (totalWeight_nonneg left.atoms) sumPositive.le
  atMostOne := by
    apply (RFAP.ConstructiveFraction.div_le_iff_pos sumPositive).2
    rw [RFAP.ConstructiveFraction.one_mul]
    exact le_add_of_nonneg_right (totalWeight_nonneg right.atoms)

theorem appendMixingWeight_complement {α : Type}
    (left right : FiniteContent α)
    (sumPositive : 0 < left.total + right.total) :
    (appendMixingWeight left right sumPositive).complement =
      right.total / (left.total + right.total) := by
  let sum := left.total + right.total
  have sumNonzero : sum ≠ 0 := sumPositive.ne'
  have cancels : sum * sum⁻¹ = 1 :=
    RFAP.ConstructiveFraction.mul_inv_cancel sum sumNonzero
  change 1 - left.total * sum⁻¹ = right.total * sum⁻¹
  rw [← cancels]
  calc
    sum * sum⁻¹ - left.total * sum⁻¹ =
        (sum - left.total) * sum⁻¹ := (sub_mul _ _ _).symm
    _ = right.total * sum⁻¹ := by
      congr 1
      dsimp only [sum]
      ring1

private theorem contentFraction_mul_normalized
    (total value combined : Coordinate) (totalNonzero : total ≠ 0) :
    (total / combined) * (value / total) = value / combined := by
  change (total * combined⁻¹) * (value * total⁻¹) = value * combined⁻¹
  calc
    (total * combined⁻¹) * (value * total⁻¹) =
        (total * combined⁻¹) * (total⁻¹ * value) := by
      rw [RFAP.ConstructiveFraction.mul_comm value total⁻¹]
    _ = (total * total⁻¹) * (combined⁻¹ * value) :=
      RFAP.ConstructiveFraction.mul_pair_swap _ _ _ _
    _ = 1 * (combined⁻¹ * value) := by
      rw [RFAP.ConstructiveFraction.mul_inv_cancel total totalNonzero]
    _ = combined⁻¹ * value := RFAP.ConstructiveFraction.one_mul _
    _ = value * combined⁻¹ := RFAP.ConstructiveFraction.mul_comm _ _

/-- Normalize after mapping a positive finite content, or map its normalized
distribution first: every exact finite evaluation agrees. -/
theorem map_normalize_evaluationEquivalent {α β : Type}
    (content : FiniteContent α) (positive : 0 < content.total)
    (function : α → β) :
    Distribution.EvaluationEquivalent
      ((content.map function).normalize (by
        rw [content.map_total]
        exact positive))
      ((content.normalize positive).map function) where
  probability_eq event := by
    rw [FiniteContent.normalize_probability,
      content.map_measure,
      content.map_total,
      Distribution.map_probability,
      FiniteContent.normalize_probability]
  expectation_eq value := by
    rw [FiniteContent.normalize_expectation,
      content.map_integral,
      content.map_total,
      Distribution.map_expectation,
      FiniteContent.normalize_expectation]

/-- Conditional mean under a normalized finite content cancels the common
displayed content total exactly. -/
theorem normalize_conditionalMean {α : Type}
    (content : FiniteContent α) (positive : 0 < content.total)
    (event : α → Bool) (value : α → Coordinate) :
    (content.normalize positive).conditionalMean event value =
      (content.restrict event).integral value / content.measure event := by
  unfold Distribution.conditionalMean Distribution.eventIntegral
  rw [FiniteContent.normalize_expectation,
    FiniteContent.normalize_probability,
    ← content.restrict_integral event value]
  exact div_div_same_right _ _ content.total positive.ne'

/-- Restrict then normalize, or normalize then condition on the same
positive-content executable event: every exact finite evaluation agrees. -/
theorem restrict_normalize_evaluationEquivalent {α : Type}
    (content : FiniteContent α) (positive : 0 < content.total)
    (event : α → Bool) (measurePositive : 0 < content.measure event) :
    Distribution.EvaluationEquivalent
      ((content.restrict event).normalize (by
        rw [content.restrict_total]
        exact measurePositive))
      ((content.normalize positive).conditioned event (by
        rw [FiniteContent.normalize_probability]
        exact RFAP.ConstructiveFraction.div_pos_direct
          measurePositive positive)) := by
  apply Distribution.EvaluationEquivalent.of_expectation_eq
  intro value
  rw [FiniteContent.normalize_expectation,
    content.restrict_total,
    Distribution.conditioned_expectation_eq_conditionalMean,
    content.normalize_conditionalMean positive event value]

/-- Normalizing a positive product content agrees with taking the explicit
finite product of the two normalized component distributions. -/
theorem product_normalize_evaluationEquivalent {α β : Type}
    (left : FiniteContent α) (right : FiniteContent β)
    (leftPositive : 0 < left.total) (rightPositive : 0 < right.total) :
    Distribution.EvaluationEquivalent
      ((left.product right).normalize (by
        rw [left.product_total]
        exact RFAP.ConstructiveFraction.mul_pos_direct
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
        exact RFAP.ConstructiveFraction.mul_pos_direct
          leftPositive rightPositive)).expectation value =
        iterated / (left.total * right.total) := by
      rw [FiniteContent.normalize_expectation,
        left.product_total, left.product_integral]
    _ =
        (right.total⁻¹ * iterated) / left.total := by
      calc
        iterated / (left.total * right.total) =
        iterated * (left.total * right.total)⁻¹ := rfl
        _ = iterated * (left.total⁻¹ * right.total⁻¹) := by
          rw [RFAP.ConstructiveFraction.inv_mul_direct]
        _ = (iterated * left.total⁻¹) * right.total⁻¹ :=
          (RFAP.ConstructiveFraction.mul_assoc _ _ _).symm
        _ = right.total⁻¹ * (iterated * left.total⁻¹) :=
          RFAP.ConstructiveFraction.mul_comm _ _
        _ = (right.total⁻¹ * iterated) * left.total⁻¹ :=
          (RFAP.ConstructiveFraction.mul_assoc _ _ _).symm
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
      rw [RFAP.ConstructiveFraction.div_eq_mul_inv_direct,
        RFAP.ConstructiveFraction.mul_comm]
    _ = (left.normalize leftPositive).expectation (fun leftItem =>
          right.integral (fun rightItem => value (leftItem, rightItem)) /
            right.total) :=
      (FiniteContent.normalize_expectation left leftPositive _).symm
    _ = (left.normalize leftPositive).expectation (fun leftItem =>
          (right.normalize rightPositive).expectation
            (fun rightItem => value (leftItem, rightItem))) := by
      apply (left.normalize leftPositive).expectation_congr
      intro leftItem
      exact (FiniteContent.normalize_expectation right rightPositive _).symm
    _ = ((left.normalize leftPositive).product
          (right.normalize rightPositive)).expectation value :=
      (Distribution.product_expectation_iterated
        (left.normalize leftPositive) (right.normalize rightPositive)
        value).symm

/-- Normalizing concatenated positive contents agrees with the rational
mixture of their separately normalized finite laws. -/
theorem append_normalize_evaluationEquivalent {α : Type}
    (left right : FiniteContent α)
    (leftPositive : 0 < left.total) (rightPositive : 0 < right.total) :
    Distribution.EvaluationEquivalent
      ((left.append right).normalize (by
        rw [left.append_total]
        exact add_pos_direct leftPositive rightPositive))
      ((left.normalize leftPositive).mixture
        (right.normalize rightPositive)
        (appendMixingWeight left right
          (add_pos_direct leftPositive rightPositive))) := by
  let sumPositive := add_pos_direct leftPositive rightPositive
  apply Distribution.EvaluationEquivalent.of_expectation_eq
  intro value
  rw [FiniteContent.normalize_expectation,
    left.append_integral, left.append_total,
    Distribution.mixture_expectation,
    FiniteContent.normalize_expectation,
    FiniteContent.normalize_expectation,
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

end FiniteContent

end FiniteMeasure
