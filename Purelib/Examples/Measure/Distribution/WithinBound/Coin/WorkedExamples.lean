module
import Purelib.Data.Rat.Interval.Basic
import Purelib.Examples.Measure.Distribution.Coin.Basic
import Purelib.Examples.Measure.Distribution.Expectation.Enclosed.Coin.WorkedExamples
public import Purelib.Examples.Measure.Distribution.Threshold.Coin.WorkedExamples

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Measure.Classified.FixedLawProcess
import Purelib.Measure.Event.RationalOrder
import Purelib.Measure.Classified.Interval
import Purelib.Measure.Classified.Basic
public import Purelib.Measure.Distribution.Enclosure.Interval.Process
import Purelib.Measure.Distribution.Enclosure.Interval
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Weighted.Enclosure.Process

@[expose] public section

/-!
# Executable finite measure examples

All numerical examples reduce to finite rational calculations checked by the
kernel.  The final examples exercise the generic CCL area-request interface
without postulating a completed CCL value.
-/

namespace Purelib.Examples.Measure.Distribution.WithinBound.Coin.WorkedExamples

open Purelib.Data.Rat
open Purelib
open Purelib.Examples
open Purelib.Measure
open Purelib.Examples.Measure.Distribution.Coin.Basic (coinNumber fairCoin)
open Purelib.Examples.Measure.Distribution.Expectation.Enclosed.Coin.WorkedExamples
  (coarseCoinRange coinRangeState exactCoinRange)

/-! A bounded rational target gives the analogous finite interval event. -/

/-- The rational interval [3/4, 5/4] containing only the heads value of the coin-number observable. -/
def headsInterval : Interval :=
  ⟨3 / 4, 5 / 4, by decide⟩

/-- The retained finite classification process for coin-number membership in the heads interval. -/
def coinWithinBoundClassificationProcess :
    ClassificationProcess fairCoin
      (withinBoundEvent headsInterval
        coinNumber) :=
  Measure.Distribution.Expectation.Enclosed.Coin.WorkedExamples.coinPointwiseProcess.toWithinBoundClassificationProcess
    headsInterval coinNumber
      Measure.Distribution.Threshold.Coin.WorkedExamples.coinRangesAdmitCoinNumber
    (by
      intro state epsilon positive
      change fairCoin.probability
        (withinBoundUnresolvedEvent (coinRangeState true)
          headsInterval) <
          epsilon
      have zero : fairCoin.probability
          (withinBoundUnresolvedEvent (coinRangeState
            true) headsInterval) =
            0 := by
        decide
      rw [zero]
      exact positive)

/-- The coarse membership frontier gives probability enclosure [0, 1/2]. -/
example : Purelib.Measure.eventBound
      (fairCoin.withinBoundFrontier
        coarseCoinRange
        headsInterval) =
    ⟨0, 1 / 2, by decide⟩ := by
  apply Interval.ext <;> decide

/-- The coarse membership enclosure width equals the unresolved atom probability. -/
example : (Purelib.Measure.eventBound
      (fairCoin.withinBoundFrontier
        coarseCoinRange
        headsInterval)).width =
    fairCoin.probability
      (withinBoundUnresolvedEvent coarseCoinRange
        headsInterval) :=
  fairCoin.withinBoundFrontier_width
    coarseCoinRange
    headsInterval

/-- The coarse membership enclosure contains the original interval-event probability. -/
example : (Purelib.Measure.eventBound
      (fairCoin.withinBoundFrontier
        coarseCoinRange
        headsInterval)).Contains
    (fairCoin.probability
      (withinBoundEvent headsInterval
        coinNumber)) := by
  apply fairCoin.probability_mem_withinBoundFrontier
  intro atom member
  cases atom.item <;> decide

/-- The exact pointwise coin ranges refine the coarse membership probability enclosure. -/
example : Purelib.Data.Rat.Interval.Refines
    (Purelib.Measure.eventBound
      (fairCoin.withinBoundFrontier
        exactCoinRange
        headsInterval))
    (Purelib.Measure.eventBound
      (fairCoin.withinBoundFrontier
        coarseCoinRange
        headsInterval)) := by
  apply fairCoin.withinBoundFrontier_eventBound_refines
  intro atom member
  cases atom.item
  · exact ⟨by decide, by decide⟩
  · exact ⟨by decide, by decide⟩

/-- Exact coin ranges resolve every atom and give zero membership enclosure width. -/
example : (Purelib.Measure.eventBound
      (fairCoin.withinBoundFrontier
        exactCoinRange
        headsInterval)).width = 0 := by
  apply fairCoin.withinBoundFrontier_width_eq_zero_of_resolved
  intro atom member
  cases atom.item
  · exact Or.inr (Or.inl (by decide))
  · exact Or.inl ⟨by decide, by decide⟩

/-- The requested interval-membership approximation equals one half. -/
example :
  coinWithinBoundClassificationProcess.toBoundProcess.approximate
    coinWithinBoundClassificationProcess.initial 1 (by decide) = 1
      / 2 := by
  decide

end Purelib.Examples.Measure.Distribution.WithinBound.Coin.WorkedExamples

end
