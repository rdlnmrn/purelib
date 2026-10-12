module
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Measure.Distribution.Basic
public import Purelib.Measure.Distribution.Cumulative.Basic
import Purelib.Measure.Distribution.Sampling.Basic
import Purelib.Measure.Event.RationalOrder
import Purelib.Measure.Sampling.Statistic
import Purelib.Data.Rat.Fraction
import Purelib.Data.List.Map

import Purelib.Data.Rat.Distance.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order
public import Purelib.Measure.Distribution.Sampling.Family
public import Purelib.Measure.Event.RationalGrid
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic

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

section
open Purelib
open Purelib.Data.Rat
/-- Compute the common sample count for cumulative-frequency accuracy at every threshold in the exact retained grid. -/
def requiredCumulativeGridSampleCount
    (thresholds : List Fraction.Rational)
    (tolerance failure : Fraction.Rational) : Nat :=
  requiredEventFamilyFrequencySampleCount
    (Measure.cumulativeEventGrid thresholds) tolerance failure

/-- Select samples with a frequency deviation at some exact original cumulative-grid threshold. -/
def empiricalCumulativeGridDeviation
    (source : Distribution Fraction.Rational) (thresholds : List Fraction.Rational)
    (count : Nat) (tolerance : Fraction.Rational) : List Fraction.Rational → Bool :=
  simultaneousEventFrequencyDeviation source
    (Measure.cumulativeEventGrid thresholds) count tolerance

end

section
open Purelib.Data.Rat
/-- Require squared empirical cumulative-frequency error below tolerance squared at every original grid threshold. -/
def EmpiricalCumulativeGridAccurate
    (source : Distribution Fraction.Rational) (thresholds : List Fraction.Rational)
    (count : Nat) (tolerance : Fraction.Rational)
    (sample : List Fraction.Rational) : Prop :=
  ∀ threshold, threshold ∈ thresholds →
    (eventFrequency count (atMostEvent threshold) sample -
      source.cumulative threshold) ^ 2 < tolerance ^ 2

/-- Require strict empirical cumulative-frequency separation below tolerance at every original grid threshold. -/
def EmpiricalCumulativeGridWithin
    (source : Distribution Fraction.Rational) (thresholds : List Fraction.Rational)
    (count : Nat) (tolerance : Fraction.Rational)
    (sample : List Fraction.Rational) : Prop :=
  ∀ threshold, threshold ∈ thresholds →
    Distance.rationalSeparation
      (eventFrequency count (atMostEvent threshold) sample)
      (source.cumulative threshold) < tolerance

end

section
open Purelib
open Purelib.Data.List
open Purelib.Data.Rat
/-- Outside the grid deviation event, each original threshold satisfies its squared frequency-error bound. -/
theorem empiricalCumulativeGridAccurate_of_outside
    (source : Distribution Fraction.Rational) (thresholds : List Fraction.Rational)
    (count : Nat) (tolerance : Fraction.Rational) (sample : List Fraction.Rational)
    (outside : empiricalCumulativeGridDeviation source thresholds count
      tolerance sample = false) :
    EmpiricalCumulativeGridAccurate source thresholds count tolerance
      sample := by
  intro threshold member
  have eventMember : atMostEvent threshold ∈
      Measure.cumulativeEventGrid thresholds := by
    unfold Measure.cumulativeEventGrid
    exact Map.mem_map.mpr ⟨threshold, member, rfl⟩
  have accurate := eventFamilyFrequenciesAccurate_of_outside source
    (Measure.cumulativeEventGrid thresholds) count tolerance sample outside
  exact accurate (atMostEvent threshold) eventMember

/-- Outside the grid deviation event, each original threshold has frequency separation below the positive tolerance. -/
theorem empiricalCumulativeGridWithin_of_outside
    (source : Distribution Fraction.Rational) (thresholds : List Fraction.Rational)
    (count : Nat) (tolerance : Fraction.Rational) (tolerancePositive : 0 < tolerance)
    (sample : List Fraction.Rational)
    (outside : empiricalCumulativeGridDeviation source thresholds count
      tolerance sample = false) :
    EmpiricalCumulativeGridWithin source thresholds count tolerance sample := by
  intro threshold member
  have within := eventFamilyFrequenciesWithin_of_outside source
    (Measure.cumulativeEventGrid thresholds) count tolerance tolerancePositive sample
    outside
  exact within (atMostEvent threshold)
    (Map.mem_map.mpr ⟨threshold, member, rfl⟩)

end

open Purelib in
open Purelib.Data.Rat in
/-- The exact grid sample request makes the grid deviation probability smaller than the positive failure tolerance. -/
theorem iidSamples_empiricalCumulativeGrid_deviationProbability_lt_requested
    (source : Distribution Fraction.Rational) (thresholds : List Fraction.Rational)
    (tolerance : Fraction.Rational) (tolerancePositive : 0 < tolerance)
    (failure : Fraction.Rational) (failurePositive : 0 < failure) :
    (source.iidSamples
        (requiredCumulativeGridSampleCount
          thresholds tolerance failure)).probability
      (empiricalCumulativeGridDeviation source thresholds
        (requiredCumulativeGridSampleCount thresholds tolerance failure)
        tolerance) < failure :=
  source.iidSamples_simultaneousEventFrequency_deviationProbability_lt_requested
    (Measure.cumulativeEventGrid thresholds) tolerance tolerancePositive failure
    failurePositive

end Distribution

end Purelib.Measure

end
