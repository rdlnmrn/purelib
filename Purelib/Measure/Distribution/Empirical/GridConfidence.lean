module
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.Sampling.Basic
import Purelib.Measure.Distribution.Sampling.Request
import Purelib.Measure.Weighted.Event
import Purelib.Data.Rat.Fraction

import Purelib.Approximation.Rational.Budget.FiniteFamily
import Purelib.Data.Rat.Distance.Basic
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order
public import Purelib.Measure.Distribution.Cumulative.Grid
public import Purelib.Measure.Distribution.Empirical.Basic
import Purelib.Measure.Distribution.Empirical.Cumulative
public import Purelib.Measure.Distribution.Sampling.Cumulative
import Purelib.Measure.Distribution.Sampling.Family
import Purelib.Measure.Event.RationalGrid
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic

section
@[expose] public section

/-!
# Finite empirical quantile certificates

Two empirical cumulative frequencies, at explicitly supplied lower and upper
cuts, certify a bracket for an executable empirical lower quantile.  A shared
finite sampling request controls those cuts together with any other displayed
thresholds.  There is no infinite empirical process and no convergence of a
sequence of quantiles.
-/

namespace Purelib.Measure

namespace Distribution

open Purelib.Data.Rat
/-- Strict cumulative-frequency accuracy is equivalent to strict grid-distance accuracy for the exact nonempty empirical
law. -/
theorem empiricalCumulativeGridWithin_iff_cumulativeGridDistance_lt
    (source : Distribution Fraction.Rational) (thresholds : List Fraction.Rational)
    (samples : List Fraction.Rational) (positiveLength : 0 < samples.length)
    (tolerance : Fraction.Rational) (tolerancePositive : 0 < tolerance) :
    EmpiricalCumulativeGridWithin source thresholds samples.length tolerance
        samples ↔
      (empiricalDistribution samples positiveLength).cumulativeGridDistance
        source thresholds < tolerance := by
  refine Iff.trans ?_ ((empiricalDistribution samples positiveLength)
    |>.cumulativeGridDistance_lt_iff source thresholds tolerance
      tolerancePositive).symm
  constructor
  · intro within threshold member
    rw [empiricalDistribution_cumulative_eq_eventFrequency]
    exact within threshold member
  · intro close threshold member
    rw [← empiricalDistribution_cumulative_eq_eventFrequency]
    exact close threshold member

/-- Outside the original grid deviation event, the exact empirical law is within the positive grid-distance tolerance.
-/
theorem empiricalCumulativeGridDistance_lt_of_outside
    (source : Distribution Fraction.Rational) (thresholds : List Fraction.Rational)
    (samples : List Fraction.Rational) (positiveLength : 0 < samples.length)
    (tolerance : Fraction.Rational) (tolerancePositive : 0 < tolerance)
    (outside : empiricalCumulativeGridDeviation source thresholds
      samples.length tolerance samples = false) :
    (empiricalDistribution samples positiveLength).cumulativeGridDistance
      source thresholds < tolerance := by
  apply (source.empiricalCumulativeGridWithin_iff_cumulativeGridDistance_lt
    thresholds samples positiveLength tolerance tolerancePositive).1
  exact source.empiricalCumulativeGridWithin_of_outside thresholds
    samples.length tolerance tolerancePositive samples outside

/-- Compute empirical-to-source grid distance for nonempty samples, returning zero for the empty list. -/
def sampleCumulativeGridDistance
    (source : Distribution Fraction.Rational) (thresholds : List Fraction.Rational)
    (samples : List Fraction.Rational) : Fraction.Rational :=
  if positiveLength : 0 < samples.length then
    (empiricalDistribution samples positiveLength).cumulativeGridDistance
      source thresholds
  else 0

/-- For the exact nonempty sample list, the total sample-distance function equals its empirical-law grid distance. -/
theorem sampleCumulativeGridDistance_eq_of_positive
    (source : Distribution Fraction.Rational) (thresholds : List Fraction.Rational)
    (samples : List Fraction.Rational) (positiveLength : 0 < samples.length) :
    sampleCumulativeGridDistance source thresholds samples =
      (empiricalDistribution samples positiveLength).cumulativeGridDistance
        source thresholds := by
  unfold sampleCumulativeGridDistance
  rw [dif_pos positiveLength]

/-- Select samples of the exact requested length whose empirical grid distance reaches the tolerance. -/
def empiricalCumulativeGridDistanceDeviation
    (source : Distribution Fraction.Rational) (thresholds : List Fraction.Rational)
    (count : Nat) (tolerance : Fraction.Rational) : List Fraction.Rational → Bool :=
  fun samples => decide (samples.length = count ∧
    tolerance ≤ sampleCumulativeGridDistance source thresholds samples)

/-- At positive count and tolerance, empirical grid-distance deviation probability is bounded by the original
frequency-grid deviation probability. -/
theorem empiricalCumulativeGridDistanceDeviation_probability_le
    (source : Distribution Fraction.Rational) (thresholds : List Fraction.Rational)
    (count : Nat) (countPositive : 0 < count)
    (tolerance : Fraction.Rational) (tolerancePositive : 0 < tolerance) :
    (source.iidSamples count).probability
        (empiricalCumulativeGridDistanceDeviation source thresholds count
          tolerance) ≤
      (source.iidSamples count).probability
        (empiricalCumulativeGridDeviation source thresholds count
          tolerance) := by
  unfold probability
  apply eventWeight_mono
  intro atom member selected
  have failure := of_decide_eq_true selected
  rcases failure with ⟨lengthEqual, distanceLarge⟩
  have samplePositive : 0 < atom.item.length := by
    rw [lengthEqual]
    exact countPositive
  cases deviationSelected :
      empiricalCumulativeGridDeviation source thresholds count tolerance
        atom.item with
  | true => rfl
  | false =>
      have outside : empiricalCumulativeGridDeviation source thresholds
          atom.item.length tolerance atom.item = false := by
        simpa only [lengthEqual] using deviationSelected
      have distanceSmall := source.empiricalCumulativeGridDistance_lt_of_outside
        thresholds atom.item samplePositive tolerance tolerancePositive outside
      have distanceEqual := sampleCumulativeGridDistance_eq_of_positive source
        thresholds atom.item samplePositive
      rw [distanceEqual] at distanceLarge
      exact (not_le_of_gt distanceSmall distanceLarge).elim

/-- The computed grid sample request makes empirical grid-distance deviation probability smaller than the positive
failure tolerance. -/
theorem iidSamples_empiricalCumulativeGridDistanceDeviation_lt_requested
    (source : Distribution Fraction.Rational) (thresholds : List Fraction.Rational)
    (tolerance : Fraction.Rational) (tolerancePositive : 0 < tolerance)
    (failure : Fraction.Rational) (failurePositive : 0 < failure) :
    (source.iidSamples
        (requiredCumulativeGridSampleCount
          thresholds tolerance failure)).probability
      (empiricalCumulativeGridDistanceDeviation source thresholds
        (requiredCumulativeGridSampleCount thresholds tolerance failure)
        tolerance) < failure := by
  let count := requiredCumulativeGridSampleCount thresholds tolerance failure
  have countPositive : 0 < count := by
    unfold count requiredCumulativeGridSampleCount
      requiredEventFamilyFrequencySampleCount
      requiredEventFrequencySampleCount requiredChebyshevSampleCount
    exact Nat.zero_lt_succ _
  exact (source.empiricalCumulativeGridDistanceDeviation_probability_le
    thresholds count countPositive tolerance tolerancePositive).trans_lt
      (source.iidSamples_empiricalCumulativeGrid_deviationProbability_lt_requested
        thresholds tolerance tolerancePositive failure failurePositive)
end Distribution

end Purelib.Measure

end
