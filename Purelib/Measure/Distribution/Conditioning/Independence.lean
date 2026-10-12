module
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.Conditioning.Basic
public import Purelib.Measure.Distribution.Conditioning.Mean
import Purelib.Measure.Distribution.Conditioning.Probability
public import Purelib.Measure.Distribution.Independence.Basic
import Purelib.Measure.Weighted.Event
import Purelib.Measure.Weighted.Integral
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Data.Rat.Fraction.Order
import Purelib.Measure.Distribution.Moments.Covariance
import Purelib.Measure.Content.Basic
import Purelib.Measure.Classified.Basic
import Purelib.Measure.Filtration.Basic
import Purelib.Measure.Distribution.Partition.Basic
import Purelib.Measure.Distribution.Partition.Positive
import Purelib.Measure.EventAlgebra.Simple.Basic
import Purelib.Measure.Event.Chain
import Purelib.Approximation.OneSided.Basic
import Purelib.Measure.Classified.FixedLawProcess
import Purelib.Approximation.OneSided.Located
import Purelib.Measure.Distribution.Independence.Moments
import Purelib.Measure.EventAlgebra.Basic
import Purelib.Measure.Distribution.Expectation
import Purelib.Measure.Weighted.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction
import Mathlib.Order.Basic

section
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

open Purelib
/-- Require the two original Boolean events to be independent under the retained positive-event conditioned law. -/
def ConditionallyIndependentEvents {α : Type}
    (distribution : Measure.Distribution α) (left right condition : α → Bool)
    (positive : 0 < distribution.probability condition) : Prop :=
  (distribution.conditioned condition positive).IndependentEvents left right

/-- Conditional independence is equivalent to conditional intersection probability factoring into the two conditional
probabilities. -/
theorem conditionallyIndependentEvents_iff {α : Type}
    (distribution : Measure.Distribution α) (left right condition : α → Bool)
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

/-- Reversing the two events preserves their independence under the same retained conditioning. -/
theorem conditionallyIndependentEvents_symm {α : Type}
    (distribution : Measure.Distribution α) {left right condition : α → Bool}
    {positive : 0 < distribution.probability condition}
    (independent : distribution.ConditionallyIndependentEvents
      left right condition positive) :
    distribution.ConditionallyIndependentEvents
      right left condition positive :=
  (distribution.conditioned condition positive).independentEvents_symm
    independent

/-- Complementing the right event preserves independence under the same retained conditioning. -/
theorem conditionallyIndependentEvents_complement_right {α : Type}
    (distribution : Measure.Distribution α) {left right condition : α → Bool}
    {positive : 0 < distribution.probability condition}
    (independent : distribution.ConditionallyIndependentEvents
      left right condition positive) :
    distribution.ConditionallyIndependentEvents
      left (complementEvent right) condition positive :=
  (distribution.conditioned condition positive)
    |>.independentEvents_complement_right independent

/-- Complementing the left event preserves independence under the same retained conditioning. -/
theorem conditionallyIndependentEvents_complement_left {α : Type}
    (distribution : Measure.Distribution α) {left right condition : α → Bool}
    {positive : 0 < distribution.probability condition}
    (independent : distribution.ConditionallyIndependentEvents
      left right condition positive) :
    distribution.ConditionallyIndependentEvents
      (complementEvent left) right condition positive :=
  (distribution.conditioned condition positive)
    |>.independentEvents_complement_left independent

/-- Complementing both events preserves independence under the same retained conditioning. -/
theorem conditionallyIndependentEvents_complements {α : Type}
    (distribution : Measure.Distribution α) {left right condition : α → Bool}
    {positive : 0 < distribution.probability condition}
    (independent : distribution.ConditionallyIndependentEvents
      left right condition positive) :
    distribution.ConditionallyIndependentEvents
      (complementEvent left) (complementEvent right) condition positive :=
  (distribution.conditioned condition positive)
    |>.independentEvents_complements independent

/-- Conditionally independent indicators have product conditional mean equal to the product of their original
conditional probabilities. -/
theorem conditionalMean_indicator_mul_indicator_of_independent
    {α : Type} (distribution : Measure.Distribution α)
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

/-- Conditionally independent events have zero indicator covariance under the retained conditioned law. -/
theorem conditional_covariance_indicators_eq_zero {α : Type}
    (distribution : Measure.Distribution α) (left right condition : α → Bool)
    (positive : 0 < distribution.probability condition)
    (independent : distribution.ConditionallyIndependentEvents
      left right condition positive) :
    (distribution.conditioned condition positive).covariance
      (indicator left) (indicator right) = 0 :=
  (distribution.conditioned condition positive)
    |>.covariance_indicators_eq_zero_of_independent independent

end Distribution

namespace PositiveEventPartition
end PositiveEventPartition

end Purelib.Measure

end

end

section
@[expose] public section

/-!
# Independence of finite rational events

Independence is an exact rational multiplication identity between three
finite event evaluations.  Event families remain displayed lists.
-/

namespace Purelib.Measure

open Purelib in
open Purelib.Data.Rat in
/-- Conditioning an event on an independent positive-probability event preserves its original probability. -/
theorem Distribution.conditionalProbability_eq_of_independent
    {α : Type} (distribution : Measure.Distribution α) {event condition : α → Bool}
    (positive : 0 < distribution.probability condition)
    (independent : distribution.IndependentEvents event condition) :
    distribution.conditionalProbability event condition positive =
      distribution.probability event := by
  unfold conditionalProbability
  apply Fraction.Order.Basic.Compatibility.le_antisymm
  · apply (Fraction.Order.Field.div_le_iff_pos positive).2
    exact independent.le
  · apply (Fraction.Order.Field.le_div_iff_pos positive).2
    exact independent.ge

open Purelib in
/-- If positive-event conditioning preserves an event's original probability, the two original events are independent.
-/
theorem Distribution.independent_of_conditionalProbability_eq
    {α : Type} (distribution : Measure.Distribution α) {event condition : α → Bool}
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
end Purelib.Measure

end
