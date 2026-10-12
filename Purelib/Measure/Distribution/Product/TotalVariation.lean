module
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.Expectation
import Purelib.Measure.Distribution.Kernel.Basic
import Purelib.Measure.Distribution.Kernel.TotalVariation
public import Purelib.Measure.Distribution.TotalVariation.Basic
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic

import Purelib.Data.Rat.Distance.Basic
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order
import Purelib.Measure.Distribution.Stability
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic

section
@[expose] public section

/-!
# Product and finite-sample total variation bounds

Tensoring two finite rational laws with a common probability factor preserves
total variation exactly.  Changing both factors costs at most the sum of the
two component distances.  Iterating this finite tensorization gives the
explicit `n * TV` bound for exactly `n` IID samples.
-/

namespace Purelib.Measure

namespace Distribution

/-- Adding the same independent right marginal cannot increase total variation distance. -/
theorem totalVariationDistance_product_common_right_le
    {α β : Type} [DecidableEq α] [DecidableEq β]
    (left right : Distribution α) (common : Distribution β) :
    (left.product common).totalVariationDistance (right.product common) ≤
      left.totalVariationDistance right := by
  unfold Distribution.product
  exact left.totalVariationDistance_bind_le right fun leftValue =>
    common.map fun rightValue => (leftValue, rightValue)

section
open Purelib.Data.Rat
/-- Adding the same independent right marginal preserves total variation distance exactly. -/
theorem totalVariationDistance_product_common_right_eq
    {α β : Type} [DecidableEq α] [DecidableEq β]
    (left right : Distribution α) (common : Distribution β) :
    (left.product common).totalVariationDistance (right.product common) =
      left.totalVariationDistance right := by
  apply Fraction.Order.Basic.Compatibility.le_antisymm
  · exact left.totalVariationDistance_product_common_right_le right common
  · let event := left.totalVariationEvent right
    let rectangle : α × β → Bool := fun pair =>
      event pair.1 && true
    calc
      left.totalVariationDistance right =
          left.probability event - right.probability event :=
        (left.probability_sub_at_totalVariationEvent right).symm
      _ = (left.product common).probability rectangle -
          (right.product common).probability rectangle := by
        rw [left.product_probability_rectangle common event (fun _ => true),
          right.product_probability_rectangle common event (fun _ => true),
          common.probability_true]
        ring1
      _ ≤ Distance.rationalSeparation
          ((left.product common).probability rectangle)
          ((right.product common).probability rectangle) :=
        Fraction.Order.Basic.le_max_left _ _
      _ ≤ (left.product common).totalVariationDistance
          (right.product common) :=
        (left.product common).probability_separation_le_totalVariationDistance
          (right.product common) rectangle

/-- Adding the same independent left marginal cannot increase total variation distance. -/
theorem totalVariationDistance_product_common_left_le
    {α β : Type} [DecidableEq α] [DecidableEq β]
    (common : Distribution α) (left right : Distribution β) :
    (common.product left).totalVariationDistance (common.product right) ≤
      left.totalVariationDistance right := by
  let event := (common.product left).totalVariationEvent
    (common.product right)
  let sectionDifference : α → Fraction.Rational := fun leftValue =>
    left.probability (fun rightValue => event (leftValue, rightValue)) -
      right.probability (fun rightValue => event (leftValue, rightValue))
  have sectionBound : ∀ leftValue,
      sectionDifference leftValue ≤ left.totalVariationDistance right := by
    intro leftValue
    exact (Fraction.Order.Basic.le_max_left _ _).trans
      (left.probability_separation_le_totalVariationDistance right
        (fun rightValue => event (leftValue, rightValue)))
  calc
    (common.product left).totalVariationDistance (common.product right) =
        (common.product left).probability event -
          (common.product right).probability event :=
      ((common.product left).probability_sub_at_totalVariationEvent
        (common.product right)).symm
    _ = common.expectation sectionDifference := by
      rw [common.product_probability_iterated left,
        common.product_probability_iterated right,
        common.expectation_sub]
    _ ≤ common.expectation
        (fun _ => left.totalVariationDistance right) :=
      common.expectation_mono sectionDifference
        (fun _ => left.totalVariationDistance right)
        (fun atom member => sectionBound atom.item)
    _ = left.totalVariationDistance right :=
      common.expectation_constant _

/-- Adding the same independent left marginal preserves total variation distance exactly. -/
theorem totalVariationDistance_product_common_left_eq
    {α β : Type} [DecidableEq α] [DecidableEq β]
    (common : Distribution α) (left right : Distribution β) :
    (common.product left).totalVariationDistance (common.product right) =
      left.totalVariationDistance right := by
  apply Fraction.Order.Basic.Compatibility.le_antisymm
  · exact common.totalVariationDistance_product_common_left_le left right
  · let event := left.totalVariationEvent right
    let rectangle : α × β → Bool := fun pair =>
      true && event pair.2
    calc
      left.totalVariationDistance right =
          left.probability event - right.probability event :=
        (left.probability_sub_at_totalVariationEvent right).symm
      _ = (common.product left).probability rectangle -
          (common.product right).probability rectangle := by
        rw [common.product_probability_rectangle left (fun _ => true) event,
          common.product_probability_rectangle right (fun _ => true) event,
          common.probability_true]
        ring1
      _ ≤ Distance.rationalSeparation
          ((common.product left).probability rectangle)
          ((common.product right).probability rectangle) :=
        Fraction.Order.Basic.le_max_left _ _
      _ ≤ (common.product left).totalVariationDistance
          (common.product right) :=
        (common.product left).probability_separation_le_totalVariationDistance
          (common.product right) rectangle

end

/-- The total variation distance between two product laws is bounded by the sum of their corresponding marginal
distances. -/
theorem totalVariationDistance_product_le_add
    {α β : Type} [DecidableEq α] [DecidableEq β]
    (leftFirst leftSecond : Distribution α)
    (rightFirst rightSecond : Distribution β) :
    (leftFirst.product rightFirst).totalVariationDistance
        (leftSecond.product rightSecond) ≤
      leftFirst.totalVariationDistance leftSecond +
        rightFirst.totalVariationDistance rightSecond := by
  calc
    (leftFirst.product rightFirst).totalVariationDistance
          (leftSecond.product rightSecond) ≤
        (leftFirst.product rightFirst).totalVariationDistance
            (leftSecond.product rightFirst) +
          (leftSecond.product rightFirst).totalVariationDistance
            (leftSecond.product rightSecond) :=
      (leftFirst.product rightFirst).totalVariationDistance_triangle
        (leftSecond.product rightFirst) (leftSecond.product rightSecond)
    _ = leftFirst.totalVariationDistance leftSecond +
        rightFirst.totalVariationDistance rightSecond := by
      rw [leftFirst.totalVariationDistance_product_common_right_eq
          leftSecond rightFirst,
        leftSecond.totalVariationDistance_product_common_left_eq
          rightFirst rightSecond]
end Distribution

end Purelib.Measure

end
