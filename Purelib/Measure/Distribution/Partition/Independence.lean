module

public import Purelib.Measure.Distribution.Conditioning.Independence
import Purelib.Measure.Distribution.Moments.Covariance
import Purelib.Data.Rat.Fraction
import Purelib.Measure.Weighted.Integral
import Purelib.Measure.Weighted.Event
public import Purelib.Measure.Distribution.Partition.Positive
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.Conditioning.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Measure.Distribution.Conditioning.Probability

section
@[expose] public section

/-!
# Conditional independence on displayed finite events and partitions

Conditioning is already an executable rational reweighting.  Conditional
independence is therefore ordinary finite independence in that reweighted
atom table.  A partition version requires the identity separately on every
displayed positive cell.
-/

namespace Purelib.Measure

namespace Distribution
end Distribution

namespace PositiveEventPartition

/-- Require the two events to be independent under conditioning on every retained positive partition cell. -/
def ConditionallyIndependentEvents {α : Type}
    {distribution : Distribution α}
    (partition : PositiveEventPartition distribution)
    (left right : α → Bool) : Prop :=
  ∀ condition, ∀ member : condition ∈ partition.events,
    distribution.ConditionallyIndependentEvents left right condition
      (partition.positive condition member)

/-- Reversing the events preserves independence on every retained partition cell. -/
theorem conditionallyIndependentEvents_symm {α : Type}
    {distribution : Distribution α}
    (partition : PositiveEventPartition distribution)
    {left right : α → Bool}
    (independent : partition.ConditionallyIndependentEvents left right) :
    partition.ConditionallyIndependentEvents right left := by
  intro condition member
  exact distribution.conditionallyIndependentEvents_symm
    (independent condition member)

/-- Complementing both events preserves independence on every retained partition cell. -/
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

/-- Cellwise conditional independence factors the conditional intersection probability on each retained cell. -/
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

/-- Cellwise conditional independence makes the indicator covariance vanish under every retained cell's conditioned law.
-/
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

end Purelib.Measure

end
