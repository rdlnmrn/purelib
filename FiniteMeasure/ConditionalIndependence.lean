import FiniteMeasure.Independence
import FiniteMeasure.PartitionExpectation

/-!
# Conditional independence on displayed finite events and partitions

Conditioning is already an executable rational reweighting.  Conditional
independence is therefore ordinary finite independence in that reweighted
atom table.  A partition version requires the identity separately on every
displayed positive cell.
-/

namespace FiniteMeasure

namespace Distribution

/-- Two events are conditionally independent given one explicitly positive
conditioning event when they are independent in the finite conditioned
distribution. -/
def ConditionallyIndependentEvents {α : Type}
    (distribution : Distribution α) (left right condition : α → Bool)
    (positive : 0 < distribution.probability condition) : Prop :=
  (distribution.conditioned condition positive).IndependentEvents left right

/-- Conditional independence is exactly the multiplication identity for
three rational conditional probabilities. -/
theorem conditionallyIndependentEvents_iff {α : Type}
    (distribution : Distribution α) (left right condition : α → Bool)
    (positive : 0 < distribution.probability condition) :
    distribution.ConditionallyIndependentEvents left right condition positive ↔
      distribution.conditionalProbability
          (intersectionEvent left right) condition positive =
        distribution.conditionalProbability left condition positive *
          distribution.conditionalProbability right condition positive := by
  unfold ConditionallyIndependentEvents IndependentEvents
  rw [distribution.conditioned_probability condition
      (intersectionEvent left right) positive,
    distribution.conditioned_probability condition left positive,
    distribution.conditioned_probability condition right positive]

theorem conditionallyIndependentEvents_symm {α : Type}
    (distribution : Distribution α) {left right condition : α → Bool}
    {positive : 0 < distribution.probability condition}
    (independent : distribution.ConditionallyIndependentEvents
      left right condition positive) :
    distribution.ConditionallyIndependentEvents
      right left condition positive :=
  (distribution.conditioned condition positive).independentEvents_symm
    independent

theorem conditionallyIndependentEvents_complement_right {α : Type}
    (distribution : Distribution α) {left right condition : α → Bool}
    {positive : 0 < distribution.probability condition}
    (independent : distribution.ConditionallyIndependentEvents
      left right condition positive) :
    distribution.ConditionallyIndependentEvents
      left (complementEvent right) condition positive :=
  (distribution.conditioned condition positive)
    |>.independentEvents_complement_right independent

theorem conditionallyIndependentEvents_complement_left {α : Type}
    (distribution : Distribution α) {left right condition : α → Bool}
    {positive : 0 < distribution.probability condition}
    (independent : distribution.ConditionallyIndependentEvents
      left right condition positive) :
    distribution.ConditionallyIndependentEvents
      (complementEvent left) right condition positive :=
  (distribution.conditioned condition positive)
    |>.independentEvents_complement_left independent

theorem conditionallyIndependentEvents_complements {α : Type}
    (distribution : Distribution α) {left right condition : α → Bool}
    {positive : 0 < distribution.probability condition}
    (independent : distribution.ConditionallyIndependentEvents
      left right condition positive) :
    distribution.ConditionallyIndependentEvents
      (complementEvent left) (complementEvent right) condition positive :=
  (distribution.conditioned condition positive)
    |>.independentEvents_complements independent

/-- Conditional independence factors the conditional mean of the two event
indicators. -/
theorem conditionalMean_indicator_mul_indicator_of_independent
    {α : Type} (distribution : Distribution α)
    (left right condition : α → Bool)
    (positive : 0 < distribution.probability condition)
    (independent : distribution.ConditionallyIndependentEvents
      left right condition positive) :
    distribution.conditionalMean condition (fun item =>
        indicator left item * indicator right item) =
      distribution.conditionalProbability left condition positive *
        distribution.conditionalProbability right condition positive := by
  calc
    distribution.conditionalMean condition (fun item =>
          indicator left item * indicator right item) =
        (distribution.conditioned condition positive).expectation
          (fun item => indicator left item * indicator right item) :=
      (distribution.conditioned_expectation_eq_conditionalMean
        condition positive _).symm
    _ = (distribution.conditioned condition positive).probability
          (intersectionEvent left right) :=
      (distribution.conditioned condition positive)
        |>.expectation_indicator_mul_indicator left right
    _ = (distribution.conditioned condition positive).probability left *
          (distribution.conditioned condition positive).probability right :=
      independent
    _ = distribution.conditionalProbability left condition positive *
          distribution.conditionalProbability right condition positive := by
      rw [distribution.conditioned_probability condition left positive,
        distribution.conditioned_probability condition right positive]

/-- Conditional independence gives zero covariance of the two indicators in
the explicitly conditioned finite distribution. -/
theorem conditional_covariance_indicators_eq_zero {α : Type}
    (distribution : Distribution α) (left right condition : α → Bool)
    (positive : 0 < distribution.probability condition)
    (independent : distribution.ConditionallyIndependentEvents
      left right condition positive) :
    (distribution.conditioned condition positive).covariance
      (indicator left) (indicator right) = 0 :=
  (distribution.conditioned condition positive)
    |>.covariance_indicators_eq_zero_of_independent independent

end Distribution

namespace PositiveEventPartition

/-- Conditional independence relative to a displayed finite partition means
independence after conditioning on every positive partition cell. -/
def ConditionallyIndependentEvents {α : Type}
    {distribution : Distribution α}
    (partition : PositiveEventPartition distribution)
    (left right : α → Bool) : Prop :=
  ∀ condition, ∀ member : condition ∈ partition.events,
    distribution.ConditionallyIndependentEvents left right condition
      (partition.positive condition member)

theorem conditionallyIndependentEvents_symm {α : Type}
    {distribution : Distribution α}
    (partition : PositiveEventPartition distribution)
    {left right : α → Bool}
    (independent : partition.ConditionallyIndependentEvents left right) :
    partition.ConditionallyIndependentEvents right left := by
  intro condition member
  exact distribution.conditionallyIndependentEvents_symm
    (independent condition member)

theorem conditionallyIndependentEvents_complements {α : Type}
    {distribution : Distribution α}
    (partition : PositiveEventPartition distribution)
    {left right : α → Bool}
    (independent : partition.ConditionallyIndependentEvents left right) :
    partition.ConditionallyIndependentEvents
      (complementEvent left) (complementEvent right) := by
  intro condition member
  exact distribution.conditionallyIndependentEvents_complements
    (independent condition member)

theorem conditionalProbability_intersection_eq_mul {α : Type}
    {distribution : Distribution α}
    (partition : PositiveEventPartition distribution)
    {left right : α → Bool}
    (independent : partition.ConditionallyIndependentEvents left right)
    (condition : α → Bool) (member : condition ∈ partition.events) :
    distribution.conditionalProbability (intersectionEvent left right)
        condition (partition.positive condition member) =
      distribution.conditionalProbability left condition
          (partition.positive condition member) *
        distribution.conditionalProbability right condition
          (partition.positive condition member) :=
  (distribution.conditionallyIndependentEvents_iff left right condition
    (partition.positive condition member)).mp
      (independent condition member)

theorem conditional_covariance_indicators_eq_zero {α : Type}
    {distribution : Distribution α}
    (partition : PositiveEventPartition distribution)
    {left right : α → Bool}
    (independent : partition.ConditionallyIndependentEvents left right)
    (condition : α → Bool) (member : condition ∈ partition.events) :
    (distribution.conditioned condition
      (partition.positive condition member)).covariance
        (Distribution.indicator left) (Distribution.indicator right) = 0 :=
  distribution.conditional_covariance_indicators_eq_zero left right condition
    (partition.positive condition member) (independent condition member)

end PositiveEventPartition

end FiniteMeasure
