import mathlib.Tactic.QuotientFreeRing
import FiniteMeasure.TotalVariationDistance
import FiniteMeasure.Sampling

/-!
# Product and finite-sample total variation bounds

Tensoring two finite rational laws with a common probability factor preserves
total variation exactly.  Changing both factors costs at most the sum of the
two component distances.  Iterating this finite tensorization gives the
explicit `n * TV` bound for exactly `n` IID samples.
-/

namespace FiniteMeasure

namespace Distribution

/-- Changing the left coordinate while retaining a common right factor
cannot increase total variation. -/
theorem totalVariationDistance_product_common_right_le
    {α β : Type} [DecidableEq α] [DecidableEq β]
    (left right : Distribution α) (common : Distribution β) :
    (left.product common).totalVariationDistance (right.product common) ≤
      left.totalVariationDistance right := by
  unfold Distribution.product
  exact left.totalVariationDistance_bind_le right fun leftValue =>
    common.map fun rightValue => (leftValue, rightValue)

/-- A common right probability factor preserves total variation exactly. -/
theorem totalVariationDistance_product_common_right_eq
    {α β : Type} [DecidableEq α] [DecidableEq β]
    (left right : Distribution α) (common : Distribution β) :
    (left.product common).totalVariationDistance (right.product common) =
      left.totalVariationDistance right := by
  apply RFAP.ConstructiveFraction.le_antisymm
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
      _ ≤ rationalSeparation
          ((left.product common).probability rectangle)
          ((right.product common).probability rectangle) :=
        le_max_left _ _
      _ ≤ (left.product common).totalVariationDistance
          (right.product common) :=
        (left.product common).probability_separation_le_totalVariationDistance
          (right.product common) rectangle

/-- Changing the right coordinate while retaining a common left factor
cannot increase total variation. -/
theorem totalVariationDistance_product_common_left_le
    {α β : Type} [DecidableEq α] [DecidableEq β]
    (common : Distribution α) (left right : Distribution β) :
    (common.product left).totalVariationDistance (common.product right) ≤
      left.totalVariationDistance right := by
  let event := (common.product left).totalVariationEvent
    (common.product right)
  let sectionDifference : α → Coordinate := fun leftValue =>
    left.probability (fun rightValue => event (leftValue, rightValue)) -
      right.probability (fun rightValue => event (leftValue, rightValue))
  have sectionBound : ∀ leftValue,
      sectionDifference leftValue ≤ left.totalVariationDistance right := by
    intro leftValue
    exact (le_max_left _ _).trans
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

/-- A common left probability factor preserves total variation exactly. -/
theorem totalVariationDistance_product_common_left_eq
    {α β : Type} [DecidableEq α] [DecidableEq β]
    (common : Distribution α) (left right : Distribution β) :
    (common.product left).totalVariationDistance (common.product right) =
      left.totalVariationDistance right := by
  apply RFAP.ConstructiveFraction.le_antisymm
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
      _ ≤ rationalSeparation
          ((common.product left).probability rectangle)
          ((common.product right).probability rectangle) :=
        le_max_left _ _
      _ ≤ (common.product left).totalVariationDistance
          (common.product right) :=
        (common.product left).probability_separation_le_totalVariationDistance
          (common.product right) rectangle

/-- Finite tensorization: changing both independent coordinates costs at
most the sum of their total variation distances. -/
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

/-- Exactly `count` IID draws amplify total variation by at most the
displayed rational factor `count`. -/
theorem iidSamples_totalVariationDistance_le
    {α : Type} [DecidableEq α] (left right : Distribution α) :
    ∀ count : Nat,
      (left.iidSamples count).totalVariationDistance
          (right.iidSamples count) ≤
        (count : Coordinate) * left.totalVariationDistance right
  | 0 => by
      have zero : (left.iidSamples 0).totalVariationDistance
          (right.iidSamples 0) = 0 := by
        apply (left.iidSamples 0).totalVariationDistance_eq_zero_iff_evaluationEquivalent
          (right.iidSamples 0) |>.2
        rw [left.iidSamples_zero, right.iidSamples_zero]
        exact EvaluationEquivalent.refl (Distribution.pure [])
      rw [zero, Nat.cast_zero, zero_mul]
  | count + 1 => by
      rw [left.iidSamples_succ, right.iidSamples_succ]
      calc
        ((left.product (left.iidSamples count)).map fun pair =>
              pair.1 :: pair.2).totalVariationDistance
            ((right.product (right.iidSamples count)).map fun pair =>
              pair.1 :: pair.2) ≤
          (left.product (left.iidSamples count)).totalVariationDistance
            (right.product (right.iidSamples count)) :=
          (left.product (left.iidSamples count)).totalVariationDistance_map_le
            (right.product (right.iidSamples count))
            (fun pair => pair.1 :: pair.2)
        _ ≤ left.totalVariationDistance right +
            (left.iidSamples count).totalVariationDistance
              (right.iidSamples count) :=
          left.totalVariationDistance_product_le_add right
            (left.iidSamples count) (right.iidSamples count)
        _ ≤ left.totalVariationDistance right +
            (count : Coordinate) * left.totalVariationDistance right :=
          RFAP.ConstructiveFraction.add_le_add_direct le_rfl
            (iidSamples_totalVariationDistance_le left right count)
        _ = ((count + 1 : Nat) : Coordinate) *
            left.totalVariationDistance right := by
          rw [Nat.cast_add, Nat.cast_one]
          ring1

end Distribution

end FiniteMeasure
