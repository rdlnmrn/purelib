module
import Purelib.Data.Rat.Fraction.Field
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.Moments.Basic
import Purelib.Measure.Distribution.Sampling.Basic
public import Purelib.Measure.Distribution.Sampling.Deviation
import Purelib.Measure.Weighted.Integral
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
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
public import Purelib.Approximation.Rational.Budget.ReciprocalSquare
import Purelib.Measure.EventAlgebra.Basic
import Purelib.Measure.Weighted.Basic
import Purelib.Data.Rat.Fraction.Order
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Order.Basic

section
@[expose] public section

/-!
# Executable finite sample-count requests

The one-shot finite Chebyshev estimate can be inverted constructively.  A
rational variance budget, deviation threshold, and failure budget determine
an explicit positive natural sample count using the constructive rational
ceiling.  The returned finite iid table then has deviation probability
strictly below the requested failure budget.

The construction is intentionally one-shot: it creates no infinite sample
sequence and states no asymptotic law.
-/

namespace Purelib.Measure

namespace Distribution

section
open Purelib
open Purelib.Data.Rat
open Purelib.Measure
/-- The computed Chebyshev sample request makes deviation probability strictly below the supplied positive failure
tolerance.

The exact source variance is bounded by the retained nonnegative budget, and the supplied deviation threshold is
positive. -/
theorem iidSamples_sampleMean_deviationProbability_lt_requested
    {α : Type} (source : Measure.Distribution α) (value : α → Fraction.Rational)
    (varianceBudget : Fraction.Rational)
    (varianceBudgetNonnegative : 0 ≤ varianceBudget)
    (varianceLe : source.variance value ≤ varianceBudget)
    (threshold : Fraction.Rational) (thresholdPositive : 0 < threshold)
    (failure : Fraction.Rational) (failurePositive : 0 < failure) :
    (source.iidSamples
        (Distribution.requiredChebyshevSampleCount varianceBudget threshold failure)).probability
          (source.sampleMeanDeviation
            (Distribution.requiredChebyshevSampleCount varianceBudget threshold failure)
            value threshold) < failure := by
  let count := Distribution.requiredChebyshevSampleCount varianceBudget threshold failure
  have countPositive : 0 < (count : Fraction.Rational) :=
    Distribution.requiredChebyshevSampleCount_positive varianceBudget threshold failure
  have squarePositive : 0 < threshold ^ 2 :=
    Fraction.Order.Arithmetic.pow_pos_direct thresholdPositive 2
  calc
    (source.iidSamples count).probability
          (source.sampleMeanDeviation count value threshold) ≤
        (source.variance value / (count : Fraction.Rational)) / threshold ^ 2 :=
      source.iidSamples_sampleMean_chebyshev value count countPositive
        threshold thresholdPositive
    _ ≤ (varianceBudget / (count : Fraction.Rational)) / threshold ^ 2 :=
      Purelib.Data.Rat.Fraction.Order.div_div_le_div_div_of_le varianceLe countPositive squarePositive
    _ < failure := requiredChebyshevSampleCount_accurate varianceBudget
      threshold failure varianceBudgetNonnegative thresholdPositive
      failurePositive

/-- Every draw count meeting the computed Chebyshev request has deviation probability below the supplied positive
failure tolerance. -/
theorem iidSamples_sampleMean_deviationProbability_lt_of_request_le
    {α : Type} (source : Measure.Distribution α) (value : α → Fraction.Rational)
    (varianceBudget : Fraction.Rational)
    (varianceBudgetNonnegative : 0 ≤ varianceBudget)
    (varianceLe : source.variance value ≤ varianceBudget)
    (threshold : Fraction.Rational) (thresholdPositive : 0 < threshold)
    (failure : Fraction.Rational) (failurePositive : 0 < failure)
    (count : Nat)
    (enough : Distribution.requiredChebyshevSampleCount
      varianceBudget threshold failure ≤ count) :
    (source.iidSamples count).probability
      (source.sampleMeanDeviation count value threshold) < failure := by
  have requestedPositive := Distribution.requiredChebyshevSampleCount_positive
    varianceBudget threshold failure
  have countOrder :
      ((Distribution.requiredChebyshevSampleCount
        varianceBudget threshold failure : Nat) : Fraction.Rational) ≤
        (count : Fraction.Rational) :=
    Fraction.Cast.Order.natCast_le_direct enough
  have countPositive : 0 < (count : Fraction.Rational) :=
    requestedPositive.trans_le countOrder
  have squarePositive : 0 < threshold ^ 2 :=
    Fraction.Order.Arithmetic.pow_pos_direct thresholdPositive 2
  calc
    (source.iidSamples count).probability
          (source.sampleMeanDeviation count value threshold) ≤
        (source.variance value / (count : Fraction.Rational)) / threshold ^ 2 :=
      source.iidSamples_sampleMean_chebyshev value count countPositive
        threshold thresholdPositive
    _ ≤ (varianceBudget / (count : Fraction.Rational)) / threshold ^ 2 :=
      Purelib.Data.Rat.Fraction.Order.div_div_le_div_div_of_le varianceLe countPositive squarePositive
    _ < failure := requiredChebyshevSampleCount_accurate_of_le varianceBudget
      threshold failure varianceBudgetNonnegative thresholdPositive
      failurePositive count enough

/-! ## Finite event-frequency requests -/

end

open Purelib.Data.Rat in
open Purelib.Measure in
/-- Compute the sample count for an event-frequency request using the universal one-quarter variance budget. -/
def requiredEventFrequencySampleCount
    (threshold failure : Fraction.Rational) : Nat :=
  Distribution.requiredChebyshevSampleCount (1 / 4) threshold failure

open Purelib
open Purelib.Data.Rat
/-- Read the original event indicator's sample-mean deviation event as an empirical-frequency deviation event. -/
def eventFrequencyDeviation {α : Type} (source : Measure.Distribution α)
    (count : Nat) (event : α → Bool) (threshold : Fraction.Rational) :
    List α → Bool :=
  source.sampleMeanDeviation count (indicator event) threshold

/-- The exact requested draw count makes event-frequency deviation probability smaller than the positive failure
tolerance. -/
theorem iidSamples_eventFrequency_deviationProbability_lt_requested
    {α : Type} (source : Measure.Distribution α) (event : α → Bool)
    (threshold : Fraction.Rational) (thresholdPositive : 0 < threshold)
    (failure : Fraction.Rational) (failurePositive : 0 < failure) :
    (source.iidSamples
        (requiredEventFrequencySampleCount threshold failure)).probability
      (eventFrequencyDeviation source
        (requiredEventFrequencySampleCount threshold failure)
        event threshold) < failure := by
  exact source.iidSamples_sampleMean_deviationProbability_lt_requested
    (indicator event) (1 / 4) (by decide)
    (source.variance_indicator_le_quarter event)
    threshold thresholdPositive failure failurePositive

/-- Every draw count meeting the exact event-frequency request makes deviation probability smaller than the positive
failure tolerance. -/
theorem iidSamples_eventFrequency_deviationProbability_lt_of_request_le
    {α : Type} (source : Measure.Distribution α) (event : α → Bool)
    (threshold : Fraction.Rational) (thresholdPositive : 0 < threshold)
    (failure : Fraction.Rational) (failurePositive : 0 < failure)
    (count : Nat)
    (enough : requiredEventFrequencySampleCount threshold failure ≤ count) :
    (source.iidSamples count).probability
      (eventFrequencyDeviation source count event threshold) < failure := by
  exact source.iidSamples_sampleMean_deviationProbability_lt_of_request_le
    (indicator event) (1 / 4) (by decide)
    (source.variance_indicator_le_quarter event)
    threshold thresholdPositive failure failurePositive count enough

end Distribution

end Purelib.Measure

end
