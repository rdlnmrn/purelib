module
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.Cumulative.Grid
import Purelib.Measure.Distribution.Cumulative.TotalVariation
import Purelib.Measure.Distribution.Empirical.KolmogorovConfidence
import Purelib.Measure.Distribution.Empirical.Quantile
import Purelib.Measure.Distribution.Sampling.Basic
import Purelib.Measure.Distribution.Sampling.Cumulative
import Purelib.Measure.Distribution.Sampling.Family
import Purelib.Measure.Distribution.TotalVariation.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Examples.Measure.Distribution.Coin.Basic
import Purelib.Examples.Measure.Distribution.Coin.Law

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Measure.Distribution.Empirical.Quantile.GridConfidence
public import Purelib.Data.Rat.Fraction.Arithmetic

@[expose] public section

/-!
# Executable finite measure examples

All numerical examples reduce to finite rational calculations checked by the
kernel.  The final examples exercise the generic CCL area-request interface
without postulating a completed CCL value.
-/

namespace Purelib.Examples.Measure.Distribution.Sampling.Coin.WorkedExamples

open Purelib.Data.Rat
open Purelib.Measure
open Purelib.Examples
open Purelib.Examples.Measure.Distribution.Coin.Basic (fairCoin)
open Purelib.Examples.Measure.Distribution.Coin.Law (coinNumberLaw)

/-- The ordered heads and tails events for simultaneous frequency estimation. -/
def coinFrequencyEvents : List (Bool → Bool)
  :=
  [fun outcome => outcome, fun outcome => !outcome]

/-- The two-event frequency request with tolerance one tenth and failure budget one twentieth uses 1501 samples. -/
example : Purelib.Measure.Distribution.requiredEventFamilyFrequencySampleCount
    coinFrequencyEvents (1 / 10) (1 / 20) = 1501 := by decide

/-- The requested sample count makes simultaneous coin-event frequency failure probability less than one twentieth. -/
example :
    (fairCoin.iidSamples
      (Purelib.Measure.Distribution.requiredEventFamilyFrequencySampleCount
        coinFrequencyEvents (1 / 10) (1 / 20))).probability
      (Purelib.Measure.Distribution.simultaneousEventFrequencyDeviation
        fairCoin
        coinFrequencyEvents
        (Purelib.Measure.Distribution.requiredEventFamilyFrequencySampleCount
          coinFrequencyEvents (1 / 10) (1 / 20))
        (1 / 10)) < 1 / 20 :=
  open Purelib.Examples in
    fairCoin.iidSamples_simultaneousEventFrequency_deviationProbability_lt_requested
    coinFrequencyEvents (1 / 10) (by decide) (1 / 20) (by decide)

/-- The cumulative-probability threshold grid containing zero and one. -/
def coinCumulativeThresholdGrid : List
  Fraction.Rational := [0, 1]

/-- The two-threshold cumulative request uses 1501 samples at the displayed tolerance and budget. -/
example : Purelib.Measure.Distribution.requiredCumulativeGridSampleCount
    coinCumulativeThresholdGrid (1 / 10) (1 / 20) = 1501 := by decide

/-- The numeric fair-coin Kolmogorov request uses 1501 samples at the displayed tolerance and budget. -/
example : Purelib.Measure.Distribution.requiredKolmogorovSampleCount
  coinNumberLaw
    (1 / 10) (1 / 20) = 1501 := by decide

/-- The requested empirical numeric-coin Kolmogorov distance exceeds tolerance with probability below one twentieth. -/
example :
    (coinNumberLaw.iidSamples
      (Purelib.Measure.Distribution.requiredKolmogorovSampleCount
        coinNumberLaw
        (1 / 10) (1 / 20))).probability
      (Purelib.Measure.Distribution.empiricalKolmogorovDistanceDeviation
        coinNumberLaw
        (Purelib.Measure.Distribution.requiredKolmogorovSampleCount
          coinNumberLaw
          (1 / 10) (1 / 20))
        (1 / 10)) < 1 / 20 :=
  coinNumberLaw
    |>.iidSamples_empiricalKolmogorovDistanceDeviation_lt_requested
      (1 / 10) (by decide) (1 / 20) (by decide)

/-- The requested cumulative-grid deviation has probability below one twentieth. -/
example :
    (coinNumberLaw.iidSamples
      (Purelib.Measure.Distribution.requiredCumulativeGridSampleCount
        coinCumulativeThresholdGrid (1 / 10) (1 / 20))).probability
      (Purelib.Measure.Distribution.empiricalCumulativeGridDeviation
        coinNumberLaw
        coinCumulativeThresholdGrid
        (Purelib.Measure.Distribution.requiredCumulativeGridSampleCount
          coinCumulativeThresholdGrid (1 / 10) (1 / 20))
        (1 / 10)) < 1 / 20 :=
  open Purelib.Examples in
    coinNumberLaw.iidSamples_empiricalCumulativeGrid_deviationProbability_lt_requested
    coinCumulativeThresholdGrid (1 / 10) (by decide) (1 / 20) (by
      decide)

/-- A sample outside the cumulative-grid deviation event carries the corresponding accuracy certificate. -/
example (sample : List Fraction.Rational)
    (outside : Purelib.Measure.Distribution.empiricalCumulativeGridDeviation
      coinNumberLaw
      coinCumulativeThresholdGrid 1501 (1 / 10) sample = false) :
    Purelib.Measure.Distribution.EmpiricalCumulativeGridAccurate
      coinNumberLaw
      coinCumulativeThresholdGrid 1501 (1 / 10) sample :=
  coinNumberLaw.empiricalCumulativeGridAccurate_of_outside
    coinCumulativeThresholdGrid 1501 (1 / 10) sample outside

/-- The empirical three-quarter quantile lies in its zero-to-one bracket except on an event of probability below one
twentieth. -/
example :
    (coinNumberLaw.iidSamples
      (Purelib.Measure.Distribution.requiredCumulativeGridSampleCount
        coinCumulativeThresholdGrid (1 / 10) (1 / 20))).probability
      (Purelib.Measure.Distribution.empiricalLowerQuantileBracketDeviation
        (Purelib.Measure.Distribution.requiredCumulativeGridSampleCount
          coinCumulativeThresholdGrid (1 / 10) (1 / 20))
        (3 / 4) (by decide) (by decide) 0 1) < 1 / 20 := open Purelib.Examples in by
  apply coinNumberLaw
    |>.iidSamples_empiricalLowerQuantileBracketDeviation_lt_requested
      coinCumulativeThresholdGrid (1 / 10) (by decide)
        (1 / 20) (by decide) (3 / 4) (by decide) (by decide) 0 1
  · decide
  · decide
  · decide
  · decide

/-- Total variation distance below one tenth gives closeness on the retained coin cumulative grid. -/
example (approximation : Purelib.Measure.Distribution Fraction.Rational)
    (close : approximation.totalVariationDistance coinNumberLaw < 1 / 10)
      :
    Purelib.Measure.Distribution.CumulativeGridClose approximation
      coinNumberLaw
      coinCumulativeThresholdGrid (1 / 10) :=
  approximation.cumulativeGridClose_of_totalVariationDistance_lt
    coinNumberLaw
      coinCumulativeThresholdGrid (1 / 10) close

end Purelib.Examples.Measure.Distribution.Sampling.Coin.WorkedExamples

end
