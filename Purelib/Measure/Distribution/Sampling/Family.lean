module
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.Expectation
import Purelib.Measure.Distribution.Kernel.Basic
import Purelib.Measure.Distribution.Sampling.Basic
import Purelib.Measure.Distribution.Sampling.Deviation
public import Purelib.Measure.Distribution.Sampling.Request
import Purelib.Measure.Sampling.Statistic
import Purelib.Data.Rat.Fraction
import Purelib.Data.List.Map
import Purelib.Data.Rat.Distance.Power
import Purelib.Data.Rat.Fraction.Order.Arithmetic

public import Purelib.Approximation.Rational.Budget.FiniteFamily
import Purelib.Data.List.Rat.Sum
public import Purelib.Data.Rat.Distance.Basic
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order
import Purelib.Measure.Distribution.EventFamily
public import Purelib.Measure.Event.Family
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic

section
/-!
# Simultaneous finite event-frequency sampling

One explicit finite iid sample can estimate every event probability in a
displayed finite event list.  The requested failure budget is split over
`events.length + 1`, each event uses the uniform Bernoulli variance bound, and
finite subadditivity controls the union of all deviation events.

This is the finite constructive core of a uniform empirical-frequency bound;
there is no infinite event class, supremum, or asymptotic empirical process.
-/

@[expose] public section

namespace Purelib.Measure

namespace Distribution

open Purelib.Approximation.Rational in
open Purelib.Data.Rat in
/-- Compute a common sample count using the failure share assigned to each event in the exact finite family. -/
def requiredEventFamilyFrequencySampleCount {α : Type}
    (events : List (α → Bool))
    (threshold failure : Fraction.Rational) : Nat :=
  requiredEventFrequencySampleCount threshold
    (Budget.eventFamilyFailureShare events failure)

section
open Purelib.Data.Rat
/-- Select sample lists where at least one original family event's frequency has a threshold deviation. -/
def simultaneousEventFrequencyDeviation {α : Type}
    (source : Distribution α) (events : List (α → Bool))
    (count : Nat) (threshold : Fraction.Rational) : List α → Bool :=
  unionEvents (events.map fun event =>
    eventFrequencyDeviation source count event threshold)

/-- Require squared empirical-frequency error below threshold squared for every event in the exact family. -/
def EventFamilyFrequenciesAccurate {α : Type}
    (source : Distribution α) (events : List (α → Bool))
    (count : Nat) (threshold : Fraction.Rational) (sample : List α) : Prop :=
  ∀ event, event ∈ events →
    (eventFrequency count event sample - source.probability event) ^ 2 <
      threshold ^ 2

/-- Require empirical-frequency separation below the threshold for every event in the exact family. -/
def EventFamilyFrequenciesWithin {α : Type}
    (source : Distribution α) (events : List (α → Bool))
    (count : Nat) (threshold : Fraction.Rational) (sample : List α) : Prop :=
  ∀ event, event ∈ events →
    Distance.rationalSeparation (eventFrequency count event sample)
      (source.probability event) < threshold

end

open Purelib.Data.List in
open Purelib.Data.Rat in
/-- Outside the exact simultaneous deviation event, every original family frequency satisfies the squared-error bound.
-/
theorem eventFamilyFrequenciesAccurate_of_outside
    {α : Type} (source : Distribution α) (events : List (α → Bool))
    (count : Nat) (threshold : Fraction.Rational) (sample : List α)
    (outside : simultaneousEventFrequencyDeviation source events count
      threshold sample = false) :
    EventFamilyFrequenciesAccurate source events count threshold sample := by
  intro event member
  have deviationMember :
      eventFrequencyDeviation source count event threshold ∈
        events.map fun candidate =>
          eventFrequencyDeviation source count candidate threshold :=
    Map.mem_map.mpr ⟨event, member, rfl⟩
  have deviationFalse :
      eventFrequencyDeviation source count event threshold sample = false :=
    event_eq_false_of_mem_of_unionEvents_eq_false
      (events.map fun candidate =>
        eventFrequencyDeviation source count candidate threshold)
      (eventFrequencyDeviation source count event threshold)
      deviationMember sample outside
  have notLarge : ¬threshold ^ 2 ≤
      (eventFrequency count event sample - source.probability event) ^ 2 := by
    unfold eventFrequencyDeviation sampleMeanDeviation at deviationFalse
    have raw := decide_eq_false_iff_not.mp deviationFalse
    rw [source.expectation_indicator] at raw
    exact raw
  exact Fraction.Order.Arithmetic.lt_of_not_ge_direct notLarge

open Purelib.Data.Rat in
/-- At a positive threshold, being outside the simultaneous deviation event gives strict separation bounds for the
entire original event family. -/
theorem eventFamilyFrequenciesWithin_of_outside
    {α : Type} (source : Distribution α) (events : List (α → Bool))
    (count : Nat) (threshold : Fraction.Rational) (thresholdPositive : 0 < threshold)
    (sample : List α)
    (outside : simultaneousEventFrequencyDeviation source events count
      threshold sample = false) :
    EventFamilyFrequenciesWithin source events count threshold sample := by
  have squared := eventFamilyFrequenciesAccurate_of_outside source events
    count threshold sample outside
  intro event member
  apply Distance.rationalSeparation_lt_of_sq_lt_sq thresholdPositive
  rw [Distance.NaturalLp.rationalSeparation_sq]
  exact squared event member

open Purelib.Approximation.Rational in
open Purelib.Data.List in
open Purelib.Data.Rat in
open Purelib.Data in
/-- The common requested sample count makes simultaneous deviation probability smaller than the positive failure
tolerance.

The finite union bound uses the exact original event list and its retained per-event failure share, including repeated
events. -/
theorem iidSamples_simultaneousEventFrequency_deviationProbability_lt_requested
    {α : Type} (source : Distribution α)
    (events : List (α → Bool))
    (threshold : Fraction.Rational) (thresholdPositive : 0 < threshold)
    (failure : Fraction.Rational) (failurePositive : 0 < failure) :
    (source.iidSamples
        (requiredEventFamilyFrequencySampleCount
          events threshold failure)).probability
      (simultaneousEventFrequencyDeviation source events
        (requiredEventFamilyFrequencySampleCount events threshold failure)
        threshold) < failure := by
  let share := Budget.eventFamilyFailureShare events failure
  let count := requiredEventFamilyFrequencySampleCount events threshold failure
  let sampleLaw := source.iidSamples count
  let deviations : List (List α → Bool) := events.map fun event =>
    eventFrequencyDeviation source count event threshold
  have sharePositive : 0 < share :=
    Budget.eventFamilyFailureShare_positive events failurePositive
  calc
    sampleLaw.probability (unionEvents deviations) ≤
        (deviations.map sampleLaw.probability).sum :=
      sampleLaw.probability_unionEvents_le_sum deviations
    _ ≤ (events.length : Fraction.Rational) * share := by
      change (((events.map fun event =>
          eventFrequencyDeviation source count event threshold).map
            sampleLaw.probability).sum ≤
        (events.length : Fraction.Rational) * share)
      rw [List.Map.map_map]
      apply Rat.sum_map_le_length_mul_of_bounded events
        (fun event => sampleLaw.probability
          (eventFrequencyDeviation source count event threshold)) share
      intro event member
      exact (source.iidSamples_eventFrequency_deviationProbability_lt_requested
        event threshold thresholdPositive share sharePositive).le
    _ < failure :=
      Budget.length_mul_eventFamilyFailureShare_lt events failurePositive
end Distribution

end Purelib.Measure

end
