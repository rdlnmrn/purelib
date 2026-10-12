module
import Purelib.Measure.Distribution.AlmostEverywhere
import Purelib.Measure.Distribution.Basic
public import Purelib.Measure.Distribution.Conditioning.Basic
import Purelib.Measure.Distribution.Expectation
import Purelib.Measure.Distribution.Kernel.Basic
import Purelib.Measure.Distribution.Stability
import Purelib.Measure.Event.Family
public import Purelib.Measure.Event.IndicatorFamily
public import Purelib.Measure.Weighted.AlmostEverywhere
import Purelib.Measure.Weighted.Integral
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order
import Purelib.Measure.Content.Basic
import Purelib.Measure.Content.EssentialBound.Basic
import Purelib.Measure.Distribution.Content
import Purelib.Data.List.Event
import Purelib.Measure.Weighted.Basic
import Purelib.Measure.Distribution.Partition.Positive
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Order.Basic

section
/-!
# Conditional expectation over displayed finite partitions

This module proves the finite rational form of the law of total expectation.
Every partition cell is an executable Boolean event, every sum is a displayed
list sum, and positivity of conditioning cells is carried explicitly.  No
sigma-algebra, completion, or limiting conditional expectation is formed.
-/

public section

namespace Purelib.Measure
namespace Distribution

section
open Purelib
open Purelib.Data.Rat
/-- Take original expectation of the observable multiplied by the exact event indicator. -/
@[expose] def eventIntegral {α : Type} (distribution : Measure.Distribution α)
    (event : α → Bool) (value : α → Fraction.Rational) : Fraction.Rational :=
  distribution.expectation fun item => indicator event item * value item

/-- Pointwise equal observables have equal integrals over the same event. -/
theorem eventIntegral_congr {α : Type} (distribution : Measure.Distribution α)
    (event : α → Bool) (left right : α → Fraction.Rational)
    (pointwise : ∀ item, left item = right item) :
    distribution.eventIntegral event left =
      distribution.eventIntegral event right := by
  unfold eventIntegral
  exact distribution.expectation_congr _ _ (fun item =>
    congrArg (fun value => indicator event item * value) (pointwise item))

/-- Integration over the retained event preserves addition of observables. -/
theorem eventIntegral_add {α : Type} (distribution : Measure.Distribution α)
    (event : α → Bool) (left right : α → Fraction.Rational) :
    distribution.eventIntegral event (fun item => left item + right item) =
      distribution.eventIntegral event left +
        distribution.eventIntegral event right := by
  unfold eventIntegral
  calc
    distribution.expectation (fun item =>
        indicator event item * (left item + right item)) =
        distribution.expectation (fun item =>
          indicator event item * left item +
            indicator event item * right item) :=
      distribution.expectation_congr _ _ (fun item => by ring1)
    _ = distribution.expectation (fun item =>
          indicator event item * left item) +
        distribution.expectation (fun item =>
          indicator event item * right item) :=
      distribution.expectation_add _ _

/-- Integration over the retained event preserves subtraction of observables. -/
theorem eventIntegral_sub {α : Type} (distribution : Measure.Distribution α)
    (event : α → Bool) (left right : α → Fraction.Rational) :
    distribution.eventIntegral event (fun item => left item - right item) =
      distribution.eventIntegral event left -
        distribution.eventIntegral event right := by
  unfold eventIntegral
  calc
    distribution.expectation (fun item =>
        indicator event item * (left item - right item)) =
        distribution.expectation (fun item =>
          indicator event item * left item -
            indicator event item * right item) :=
      distribution.expectation_congr _ _ (fun item => by ring1)
    _ = distribution.expectation (fun item =>
          indicator event item * left item) -
        distribution.expectation (fun item =>
          indicator event item * right item) :=
      distribution.expectation_sub _ _

/-- Scaling an observable scales its integral over the retained event. -/
theorem eventIntegral_scale {α : Type} (distribution : Measure.Distribution α)
    (event : α → Bool) (factor : Fraction.Rational)
    (value : α → Fraction.Rational) :
    distribution.eventIntegral event (fun item => factor * value item) =
      factor * distribution.eventIntegral event value := by
  unfold eventIntegral
  calc
    distribution.expectation (fun item =>
        indicator event item * (factor * value item)) =
        distribution.expectation (fun item =>
          factor * (indicator event item * value item)) :=
      distribution.expectation_congr _ _ (fun item => by ring1)
    _ = factor * distribution.expectation (fun item =>
          indicator event item * value item) :=
      distribution.expectation_scale _ _

/-- A constant's event integral is its value times the original event probability. -/
theorem eventIntegral_constant {α : Type} (distribution : Measure.Distribution α)
    (event : α → Bool) (constant : Fraction.Rational) :
    distribution.eventIntegral event (fun _ => constant) =
      distribution.probability event * constant := by
  unfold eventIntegral
  exact distribution.expectation_indicator_mul_constant event constant

/-- Summing event integrals is expectation against the indicator sum of the exact event list. -/
theorem eventIntegrals_sum {α : Type} (distribution : Measure.Distribution α)
    (value : α → Fraction.Rational) :
    ∀ events : List (α → Bool),
      (events.map fun event => distribution.eventIntegral event value).sum =
        distribution.expectation fun item =>
          sumIndicators events item * value item
  | [] => by
      simp only [-eq_self, -iff_self, List.map_nil, List.sum_nil]
      calc
        0 = distribution.expectation (fun _ => 0) :=
          (distribution.expectation_constant 0).symm
        _ = distribution.expectation (fun item =>
              sumIndicators [] item * value item) :=
          distribution.expectation_congr _ _ (fun item => by
            simp only [-eq_self, -iff_self, sumIndicators, zero_mul]
            rfl)
  | event :: remaining => by
      rw [List.map_cons, List.sum_cons,
        eventIntegrals_sum distribution value remaining]
      unfold eventIntegral
      rw [← distribution.expectation_add]
      exact distribution.expectation_congr _ _ (fun item => by
        simp only [-eq_self, -iff_self, sumIndicators]
        ring1)

/-- For disjoint events and a nonnegative observable on retained atoms, the sum of event integrals is bounded by its
full expectation. -/
theorem eventIntegrals_sum_le_expectation_of_disjoint_nonnegative
    {α : Type} (distribution : Measure.Distribution α)
    (events : List (α → Bool)) (value : α → Fraction.Rational)
    (disjoint : MutuallyDisjointOn distribution.atoms events)
    (nonnegative : ∀ atom, atom ∈ distribution.atoms →
      0 ≤ value atom.item) :
    (events.map fun event => distribution.eventIntegral event value).sum ≤
      distribution.expectation value := by
  calc
    (events.map fun event => distribution.eventIntegral event value).sum =
        distribution.expectation (fun item =>
          sumIndicators events item * value item) :=
      distribution.eventIntegrals_sum value events
    _ = distribution.expectation (fun item =>
          indicator (unionEvents events) item * value item) := by
      apply distribution.expectation_congr_off_zero
      intro atom member
      apply Or.inr
      change sumIndicators events atom.item * value atom.item =
        indicator (unionEvents events) atom.item * value atom.item
      rw [sumIndicators_eq_indicator_unionEvents_of_disjoint
        distribution.atoms disjoint atom member]
    _ ≤ distribution.expectation value := by
      apply distribution.expectation_mono
      intro atom member
      cases selected : unionEvents events atom.item
      · simp only [-eq_self, -iff_self, indicator, selected, zero_mul]
        exact nonnegative atom member
      · simp only [-eq_self, -iff_self, indicator, selected, one_mul]
        exact le_rfl

/-- Divide the exact event integral by the original event probability.

The formula is defined for every event using rational division. Positive-probability hypotheses are supplied separately
when interpreting it as a conditioned expectation or cancelling the denominator. -/
@[expose] def conditionalMean {α : Type} (distribution : Measure.Distribution α)
    (event : α → Bool) (value : α → Fraction.Rational) : Fraction.Rational :=
  distribution.eventIntegral event value /
    distribution.probability event

/-- Pointwise equal observables have equal conditional means on the same event. -/
theorem conditionalMean_congr {α : Type} (distribution : Measure.Distribution α)
    (event : α → Bool) (left right : α → Fraction.Rational)
    (pointwise : ∀ item, left item = right item) :
    distribution.conditionalMean event left =
      distribution.conditionalMean event right := by
  unfold conditionalMean
  exact congrArg (fun numerator =>
      numerator / distribution.probability event)
    (distribution.eventIntegral_congr event left right pointwise)

/-- Conditioning on the supplied positive-probability event gives its original conditional mean as the new expectation.
-/
theorem conditioned_expectation_eq_conditionalMean {α : Type}
    (distribution : Measure.Distribution α) (event : α → Bool)
    (positive : 0 < distribution.probability event)
    (value : α → Fraction.Rational) :
    (distribution.conditioned event positive).expectation value =
      distribution.conditionalMean event value := by
  rw [distribution.conditioned_expectation event positive value]
  calc
    distribution.expectation (fun item =>
        distribution.conditioningDensity event positive item * value item) =
        distribution.expectation (fun item =>
          (distribution.probability event)⁻¹ *
            (Distribution.indicator event item * value item)) :=
      distribution.expectation_congr _ _ (fun item => by
        unfold conditioningDensity
        calc
          (Distribution.indicator event item *
                (distribution.probability event)⁻¹) * value item =
              ((distribution.probability event)⁻¹ *
                Distribution.indicator event item) * value item := by
            rw [Fraction.Field.mul_comm
              (Distribution.indicator event item)
              (distribution.probability event)⁻¹]
          _ = (distribution.probability event)⁻¹ *
                (Distribution.indicator event item * value item) :=
            Fraction.Field.mul_assoc _ _ _)
    _ = (distribution.probability event)⁻¹ *
          distribution.expectation (fun item =>
            Distribution.indicator event item * value item) :=
      distribution.expectation_scale _ _
    _ = distribution.conditionalMean event value := by
      unfold conditionalMean eventIntegral
      exact Fraction.Field.mul_comm _ _

/-- A nonnegative observable on the original atoms has nonnegative event integral. -/
theorem eventIntegral_nonneg {α : Type}
    (distribution : Measure.Distribution α) (event : α → Bool)
    (value : α → Fraction.Rational)
    (nonnegative : ∀ atom, atom ∈ distribution.atoms →
      0 ≤ value atom.item) :
    0 ≤ distribution.eventIntegral event value := by
  unfold eventIntegral
  apply distribution.expectation_nonneg
  intro atom member
  apply Fraction.Order.Arithmetic.mul_nonneg_direct
  · cases selected : event atom.item <;>
      simp only [-eq_self, -iff_self, indicator, selected] <;> decide
  · exact nonnegative atom member

/-- Pointwise order on retained occurrences selected by the event gives order of event integrals. -/
theorem eventIntegral_mono_on_event {α : Type}
    (distribution : Measure.Distribution α) (event : α → Bool)
    (lower upper : α → Fraction.Rational)
    (pointwise : ∀ atom, atom ∈ distribution.atoms →
      event atom.item = true → lower atom.item ≤ upper atom.item) :
    distribution.eventIntegral event lower ≤
      distribution.eventIntegral event upper := by
  unfold eventIntegral
  apply distribution.expectation_mono
  intro atom member
  cases selected : event atom.item
  · simp only [-eq_self, -iff_self, indicator, selected, zero_mul]
    exact le_rfl
  · simpa only [-eq_self, -iff_self, indicator, selected, one_mul] using
      pointwise atom member selected

/-- A nonnegative observable has nonnegative conditional mean on a positive-probability event. -/
theorem conditionalMean_nonneg {α : Type}
    (distribution : Measure.Distribution α) (event : α → Bool)
    (positive : 0 < distribution.probability event)
    (value : α → Fraction.Rational)
    (nonnegative : ∀ atom, atom ∈ distribution.atoms →
      0 ≤ value atom.item) :
    0 ≤ distribution.conditionalMean event value := by
  unfold conditionalMean
  exact Fraction.Order.Field.div_nonneg_direct
    (distribution.eventIntegral_nonneg event value nonnegative) positive.le

/-- The conditional-mean formula preserves addition of observables for the same event. -/
theorem conditionalMean_add {α : Type} (distribution : Measure.Distribution α)
    (event : α → Bool) (left right : α → Fraction.Rational) :
    distribution.conditionalMean event (fun item => left item + right item) =
      distribution.conditionalMean event left +
        distribution.conditionalMean event right := by
  unfold conditionalMean
  rw [distribution.eventIntegral_add]
  change (distribution.eventIntegral event left +
      distribution.eventIntegral event right) *
        (distribution.probability event)⁻¹ =
    distribution.eventIntegral event left *
        (distribution.probability event)⁻¹ +
      distribution.eventIntegral event right *
        (distribution.probability event)⁻¹
  exact add_mul _ _ _

/-- The conditional-mean formula preserves subtraction of observables for the same event. -/
theorem conditionalMean_sub {α : Type} (distribution : Measure.Distribution α)
    (event : α → Bool) (left right : α → Fraction.Rational) :
    distribution.conditionalMean event (fun item => left item - right item) =
      distribution.conditionalMean event left -
        distribution.conditionalMean event right := by
  unfold conditionalMean
  rw [distribution.eventIntegral_sub]
  change (distribution.eventIntegral event left -
      distribution.eventIntegral event right) *
        (distribution.probability event)⁻¹ =
    distribution.eventIntegral event left *
        (distribution.probability event)⁻¹ -
      distribution.eventIntegral event right *
        (distribution.probability event)⁻¹
  exact sub_mul _ _ _

/-- Pointwise order on original atoms gives order of conditional means on a positive-probability event. -/
theorem conditionalMean_mono {α : Type}
    (distribution : Measure.Distribution α) (event : α → Bool)
    (positive : 0 < distribution.probability event)
    (lower upper : α → Fraction.Rational)
    (pointwise : ∀ atom, atom ∈ distribution.atoms →
      lower atom.item ≤ upper atom.item) :
    distribution.conditionalMean event lower ≤
      distribution.conditionalMean event upper := by
  have differenceNonnegative := distribution.conditionalMean_nonneg event
    positive (fun item => upper item - lower item) (by
      intro atom member
      exact Fraction.Order.Arithmetic.sub_nonneg_direct (pointwise atom member))
  rw [distribution.conditionalMean_sub] at differenceNonnegative
  exact Fraction.Order.Arithmetic.le_of_sub_nonneg_direct differenceNonnegative

/-- Order only on selected original occurrences suffices for conditional-mean monotonicity on a positive-probability
event. -/
theorem conditionalMean_mono_on_event {α : Type}
    (distribution : Measure.Distribution α) (event : α → Bool)
    (positive : 0 < distribution.probability event)
    (lower upper : α → Fraction.Rational)
    (pointwise : ∀ atom, atom ∈ distribution.atoms →
      event atom.item = true → lower atom.item ≤ upper atom.item) :
    distribution.conditionalMean event lower ≤
      distribution.conditionalMean event upper := by
  have numeratorOrder := distribution.eventIntegral_mono_on_event event
    lower upper pointwise
  unfold conditionalMean
  change distribution.eventIntegral event lower *
      (distribution.probability event)⁻¹ ≤
    distribution.eventIntegral event upper *
      (distribution.probability event)⁻¹
  exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    numeratorOrder
    (Fraction.Order.Field.inv_pos_direct positive).le

/-- Scaling an observable scales its conditional mean on the same event. -/
theorem conditionalMean_scale {α : Type} (distribution : Measure.Distribution α)
    (event : α → Bool) (factor : Fraction.Rational)
    (value : α → Fraction.Rational) :
    distribution.conditionalMean event (fun item => factor * value item) =
      factor * distribution.conditionalMean event value := by
  unfold conditionalMean
  rw [distribution.eventIntegral_scale]
  change (factor * distribution.eventIntegral event value) *
      (distribution.probability event)⁻¹ =
    factor * (distribution.eventIntegral event value *
      (distribution.probability event)⁻¹)
  exact Fraction.Field.mul_assoc _ _ _

/-- Multiplying the conditional mean by positive event probability recovers the original event integral. -/
theorem probability_mul_conditionalMean {α : Type}
    (distribution : Measure.Distribution α) (event : α → Bool)
    (value : α → Fraction.Rational)
    (positive : 0 < distribution.probability event) :
    distribution.probability event *
        distribution.conditionalMean event value =
      distribution.eventIntegral event value := by
  calc
    distribution.probability event *
          distribution.conditionalMean event value =
        (distribution.eventIntegral event value /
            distribution.probability event) *
          distribution.probability event := by
      unfold conditionalMean
      ring1
    _ = distribution.eventIntegral event value :=
      Fraction.Field.div_mul_cancel_of_ne _ _ positive.ne'

/-- A constant observable retains its value as conditional mean on a positive-probability event. -/
theorem conditionalMean_constant {α : Type}
    (distribution : Measure.Distribution α) (event : α → Bool)
    (positive : 0 < distribution.probability event)
    (constant : Fraction.Rational) :
    distribution.conditionalMean event (fun _ => constant) = constant := by
  unfold conditionalMean eventIntegral
  rw [distribution.expectation_indicator_mul_constant]
  apply Fraction.Field.mul_right_cancel_of_ne positive.ne'
  calc
    ((distribution.probability event * constant) /
          distribution.probability event) * distribution.probability event =
        distribution.probability event * constant :=
      Fraction.Field.div_mul_cancel_of_ne _ _ positive.ne'
    _ = constant * distribution.probability event := by ring1
end

end Distribution

end Purelib.Measure

end

section
section
public section

/-!
# Essential bounds under finite conditional expectation

Conditional averaging ignores displayed zero-weight rows and preserves every
explicit essential magnitude ceiling.  Consequently the computed finite
essential maximum cannot increase.  This is the constructive finite
`L∞`-contraction theorem; no supremum or completed function space is used.
-/

namespace Purelib.Measure

namespace Distribution

open Purelib
open Purelib.Data.Rat
/-- Order away from zero-weight original occurrences gives order of event integrals. -/
theorem eventIntegral_mono_off_zero {α : Type}
    (distribution : Measure.Distribution α) (event : α → Bool)
    (lower upper : α → Fraction.Rational)
    (pointwise : ∀ atom, atom ∈ distribution.atoms →
      atom.weight = 0 ∨ lower atom.item ≤ upper atom.item) :
    distribution.eventIntegral event lower ≤
      distribution.eventIntegral event upper := by
  unfold eventIntegral
  apply distribution.toContent.integral_mono_off_zero
  intro atom member
  rcases pointwise atom member with zero | bounded
  · exact Or.inl zero
  · apply Or.inr
    cases selected : event atom.item
    · simp only [-eq_self, -iff_self, indicator, selected, zero_mul]
      exact le_rfl
    · simpa only [-eq_self, -iff_self, indicator, selected, one_mul] using bounded

/-- Order away from zero-weight occurrences gives order of conditional means on a positive-probability event. -/
theorem conditionalMean_mono_off_zero {α : Type}
    (distribution : Measure.Distribution α) (event : α → Bool)
    (positive : 0 < distribution.probability event)
    (lower upper : α → Fraction.Rational)
    (pointwise : ∀ atom, atom ∈ distribution.atoms →
      atom.weight = 0 ∨ lower atom.item ≤ upper atom.item) :
    distribution.conditionalMean event lower ≤
      distribution.conditionalMean event upper := by
  have numeratorOrder :=
    distribution.eventIntegral_mono_off_zero event lower upper pointwise
  unfold conditionalMean
  change distribution.eventIntegral event lower *
      (distribution.probability event)⁻¹ ≤
    distribution.eventIntegral event upper *
      (distribution.probability event)⁻¹
  exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    numeratorOrder
    (Fraction.Order.Field.inv_pos_direct positive).le
end Distribution

namespace PositiveEventPartition
end PositiveEventPartition

end Purelib.Measure

end

end

section
/-!
# Explicit finite partition refinement

A refinement here is finite data.  For every displayed coarse cell it gives
a displayed list of finer cells, proves those cells belong to the finer
partition and are disjoint, and certifies on every displayed atom that their
Boolean union is the coarse cell.  This suffices for an exact finite tower
law for conditional expectation.

There is no filtration over an infinite index and no limiting martingale.
-/

public section

namespace Purelib.Measure

namespace Distribution

open Purelib
open Purelib.Data.Rat
/-- Events agreeing away from zero-weight occurrences give the same integral of the retained observable. -/
theorem eventIntegral_congr_off_zero {α : Type}
    (distribution : Measure.Distribution α) (left right : α → Bool)
    (value : α → Fraction.Rational)
    (equal : EqualOffZeroWeightOn distribution.atoms left right) :
    distribution.eventIntegral left value =
      distribution.eventIntegral right value := by
  unfold eventIntegral
  apply distribution.expectation_congr_off_zero
  intro atom member
  rcases equal atom member with zero | same
  · exact Or.inl zero
  · apply Or.inr
    change indicator left atom.item * value atom.item =
      indicator right atom.item * value atom.item
    unfold indicator
    rw [same]

/-- The integral over a union of events disjoint on original atoms is the sum of their exact event integrals. -/
theorem eventIntegral_unionEvents_of_disjoint {α : Type}
    (distribution : Measure.Distribution α) (events : List (α → Bool))
    (value : α → Fraction.Rational)
    (disjoint : MutuallyDisjointOn distribution.atoms events) :
    distribution.eventIntegral (unionEvents events) value =
      (events.map fun event =>
        distribution.eventIntegral event value).sum := by
  rw [distribution.eventIntegrals_sum]
  unfold eventIntegral
  apply distribution.expectation_congr_off_zero
  intro atom member
  apply Or.inr
  change Distribution.indicator (unionEvents events) atom.item *
      value atom.item = sumIndicators events atom.item * value atom.item
  rw [sumIndicators_eq_indicator_unionEvents_of_disjoint
    distribution.atoms disjoint atom member]

end Distribution

end Purelib.Measure

end
