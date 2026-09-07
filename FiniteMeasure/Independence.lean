import mathlib.Tactic.QuotientFreeRing
import FiniteMeasure.Moments
import FiniteMeasure.Stochastic
import FiniteMeasure.Conditioning
import FiniteMeasure.EventAlgebra

/-!
# Independence of finite rational events

Independence is an exact rational multiplication identity between three
finite event evaluations.  Event families remain displayed lists.
-/

namespace FiniteMeasure

/-- Exact independence of two executable events on one finite rational
distribution. -/
def Distribution.IndependentEvents {α : Type}
    (distribution : Distribution α) (left right : α → Bool) : Prop :=
  distribution.probability (intersectionEvent left right) =
    distribution.probability left * distribution.probability right

theorem Distribution.independentEvents_symm {α : Type}
    (distribution : Distribution α) {left right : α → Bool}
    (independent : distribution.IndependentEvents left right) :
    distribution.IndependentEvents right left := by
  unfold IndependentEvents at independent ⊢
  calc
    distribution.probability (intersectionEvent right left) =
        distribution.probability (intersectionEvent left right) :=
      distribution.probability_congr _ _ (fun item => by
        unfold intersectionEvent
        cases left item <;> cases right item <;> rfl)
    _ = distribution.probability left * distribution.probability right :=
      independent
    _ = distribution.probability right * distribution.probability left := by
      ring1

/-- Intersecting an event with an event and its complement partitions its
finite rational probability exactly. -/
theorem Distribution.probability_intersection_add_complement
    {α : Type} (distribution : Distribution α)
    (left right : α → Bool) :
    distribution.probability (intersectionEvent left right) +
        distribution.probability
          (intersectionEvent left (complementEvent right)) =
      distribution.probability left := by
  unfold probability
  induction distribution.atoms with
  | nil =>
      simp only [eventWeight]
      ring1
  | cons atom remaining inductionHypothesis =>
      cases leftSelected : left atom.item <;>
        cases rightSelected : right atom.item <;>
        simp only [eventWeight, intersectionEvent, complementEvent,
          leftSelected, rightSelected, Bool.false_and, Bool.true_and,
          Bool.not_false, Bool.not_true, zero_add] <;>
        rw [← inductionHypothesis] <;>
        ring1

/-- Independence is preserved by complementing the right event. -/
theorem Distribution.independentEvents_complement_right {α : Type}
    (distribution : Distribution α) {left right : α → Bool}
    (independent : distribution.IndependentEvents left right) :
    distribution.IndependentEvents left (complementEvent right) := by
  unfold IndependentEvents at independent ⊢
  have split := distribution.probability_intersection_add_complement
    left right
  have complement := distribution.probability_add_complement right
  have complementSub :
      distribution.probability (complementEvent right) =
        1 - distribution.probability right := by
    calc
      distribution.probability (complementEvent right) =
          distribution.probability right +
              distribution.probability (complementEvent right) -
            distribution.probability right := by
        ring1
      _ = 1 - distribution.probability right := by
        rw [complement]
  calc
    distribution.probability
          (intersectionEvent left (complementEvent right)) =
        distribution.probability
            (intersectionEvent left (complementEvent right)) +
          distribution.probability (intersectionEvent left right) -
            distribution.probability (intersectionEvent left right) := by
      ring1
    _ = distribution.probability left -
          distribution.probability (intersectionEvent left right) := by
      rw [add_comm, split]
    _ = distribution.probability left -
          distribution.probability left *
            distribution.probability right := by
      rw [independent]
    _ = distribution.probability left *
          distribution.probability (complementEvent right) := by
      rw [complementSub]
      ring1

/-- Independence is preserved by complementing the left event. -/
theorem Distribution.independentEvents_complement_left {α : Type}
    (distribution : Distribution α) {left right : α → Bool}
    (independent : distribution.IndependentEvents left right) :
    distribution.IndependentEvents (complementEvent left) right :=
  distribution.independentEvents_symm
    (distribution.independentEvents_complement_right
      (distribution.independentEvents_symm independent))

/-- Independence is preserved by complementing both events. -/
theorem Distribution.independentEvents_complements {α : Type}
    (distribution : Distribution α) {left right : α → Bool}
    (independent : distribution.IndependentEvents left right) :
    distribution.IndependentEvents
      (complementEvent left) (complementEvent right) :=
  distribution.independentEvents_complement_right
    (distribution.independentEvents_complement_left independent)

/-- For a positive conditioning event, independence makes conditioning leave
the other event's probability unchanged. -/
theorem Distribution.conditionalProbability_eq_of_independent
    {α : Type} (distribution : Distribution α) {event condition : α → Bool}
    (positive : 0 < distribution.probability condition)
    (independent : distribution.IndependentEvents event condition) :
    distribution.conditionalProbability event condition positive =
      distribution.probability event := by
  unfold conditionalProbability
  apply RFAP.ConstructiveFraction.le_antisymm
  · apply (RFAP.ConstructiveFraction.div_le_iff_pos positive).2
    exact independent.le
  · apply (RFAP.ConstructiveFraction.le_div_iff_pos positive).2
    exact independent.ge

/-- Conversely, unchanged conditional probability at a positive event is
exactly the multiplication identity defining independence. -/
theorem Distribution.independent_of_conditionalProbability_eq
    {α : Type} (distribution : Distribution α) {event condition : α → Bool}
    (positive : 0 < distribution.probability condition)
    (unchanged : distribution.conditionalProbability event condition positive =
      distribution.probability event) :
    distribution.IndependentEvents event condition := by
  unfold IndependentEvents
  calc
    distribution.probability (intersectionEvent event condition) =
        distribution.conditionalProbability event condition positive *
          distribution.probability condition :=
      (distribution.conditionalProbability_mul_condition
        event condition positive).symm
    _ = distribution.probability event *
          distribution.probability condition := by
      rw [unchanged]

/-- Product-coordinate events are independent by the exact finite rectangle
probability calculation. -/
theorem Distribution.product_independentEvents_coordinates
    {α β : Type} (left : Distribution α) (right : Distribution β)
    (leftEvent : α → Bool) (rightEvent : β → Bool) :
    (left.product right).IndependentEvents
      (fun pair => leftEvent pair.1)
      (fun pair => rightEvent pair.2) := by
  unfold IndependentEvents
  change (left.product right).probability
      (fun pair => leftEvent pair.1 && rightEvent pair.2) =
    (left.product right).probability (fun pair => leftEvent pair.1) *
      (left.product right).probability (fun pair => rightEvent pair.2)
  have leftMarginal :
      (left.product right).probability (fun pair => leftEvent pair.1) =
        left.probability leftEvent := by
    calc
      (left.product right).probability (fun pair => leftEvent pair.1) =
          (left.product right).probability
            (fun pair => leftEvent pair.1 && true) :=
        (left.product right).probability_congr _ _ (fun pair => by
          simp only [Bool.and_true])
      _ = left.probability leftEvent * right.probability (fun _ => true) :=
        left.product_probability_rectangle right leftEvent (fun _ => true)
      _ = left.probability leftEvent := by
        rw [right.probability_true, mul_one]
  have rightMarginal :
      (left.product right).probability (fun pair => rightEvent pair.2) =
        right.probability rightEvent := by
    calc
      (left.product right).probability (fun pair => rightEvent pair.2) =
          (left.product right).probability
            (fun pair => true && rightEvent pair.2) :=
        (left.product right).probability_congr _ _ (fun pair => by
          simp only [Bool.true_and])
      _ = left.probability (fun _ => true) * right.probability rightEvent :=
        left.product_probability_rectangle right (fun _ => true) rightEvent
      _ = right.probability rightEvent := by
        rw [left.probability_true, one_mul]
  rw [left.product_probability_rectangle right leftEvent rightEvent,
    leftMarginal, rightMarginal]

/-- Product of two rational event indicators is the indicator of their
intersection, hence its expectation is the intersection probability. -/
theorem Distribution.expectation_indicator_mul_indicator
    {α : Type} (distribution : Distribution α)
    (left right : α → Bool) :
    distribution.expectation (fun item =>
      indicator left item * indicator right item) =
      distribution.probability (intersectionEvent left right) := by
  calc
    distribution.expectation (fun item =>
        indicator left item * indicator right item) =
        distribution.expectation (indicator (intersectionEvent left right)) :=
      distribution.expectation_congr _ _ (fun item => by
        unfold indicator intersectionEvent
        cases left item <;> cases right item <;> rfl)
    _ = distribution.probability (intersectionEvent left right) :=
      distribution.expectation_indicator _

/-- Independent events have zero exact rational covariance between their
indicators. -/
theorem Distribution.covariance_indicators_eq_zero_of_independent
    {α : Type} (distribution : Distribution α)
    {left right : α → Bool}
    (independent : distribution.IndependentEvents left right) :
    distribution.covariance (indicator left) (indicator right) = 0 := by
  rw [distribution.covariance_eq_productMoment_sub_means,
    distribution.expectation_indicator_mul_indicator,
    distribution.expectation_indicator,
    distribution.expectation_indicator,
    independent, sub_self]

/-- Conversely, zero indicator covariance is exactly event independence in
the finite rational setting. -/
theorem Distribution.independentEvents_of_covariance_indicators_eq_zero
    {α : Type} (distribution : Distribution α)
    {left right : α → Bool}
    (zero : distribution.covariance (indicator left) (indicator right) = 0) :
    distribution.IndependentEvents left right := by
  rw [distribution.covariance_eq_productMoment_sub_means,
    distribution.expectation_indicator_mul_indicator,
    distribution.expectation_indicator,
    distribution.expectation_indicator] at zero
  exact sub_eq_zero.mp zero

/-- Recursive certificate of pairwise independence for one displayed finite
event family. -/
def Distribution.PairwiseIndependentEvents {α : Type}
    (distribution : Distribution α) : List (α → Bool) → Prop
  | [] => True
  | event :: remaining =>
      (∀ candidate, candidate ∈ remaining →
        distribution.IndependentEvents event candidate) ∧
      distribution.PairwiseIndependentEvents remaining

/-- Every event of one finitely presented algebra is independent of every
event of the other.  Both quantifiers range over explicit finite code types. -/
def Distribution.IndependentEventAlgebras {α : Type}
    (distribution : Distribution α)
    (left right : FiniteEventAlgebra α) : Prop :=
  ∀ leftCode rightCode,
    distribution.IndependentEvents
      (left.evaluate leftCode) (right.evaluate rightCode)

/-- The coordinate pullbacks of arbitrary finite event algebras are
independent under the explicit product distribution. -/
theorem Distribution.product_independentEventAlgebras
    {α β : Type} (left : Distribution α) (right : Distribution β)
    (leftAlgebra : FiniteEventAlgebra α)
    (rightAlgebra : FiniteEventAlgebra β) :
    (left.product right).IndependentEventAlgebras
      (leftAlgebra.comap fun pair : α × β => pair.1)
      (rightAlgebra.comap fun pair : α × β => pair.2) := by
  intro leftCode rightCode
  exact left.product_independentEvents_coordinates right
    (leftAlgebra.evaluate leftCode) (rightAlgebra.evaluate rightCode)

end FiniteMeasure
