module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Interval.Basic
import Purelib.Examples.Measure.Distribution.Coin.Basic
public import Purelib.Examples.Measure.Distribution.Expectation.Enclosed.Coin.WorkedExamples

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Measure.Distribution.Basic
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
public import Purelib.Measure.Distribution.Enclosure.Threshold.Process
import Purelib.Approximation.Gaussian.Logarithm.Quotient.Requirement
import Purelib.Data.List.Prefix.Cursor
import Purelib.Measure.Event.RationalOrder
import Purelib.Measure.Weighted.Basic
import Purelib.Measure.EventAlgebra.Basic
import Purelib.Measure.Distribution.Enclosure.Threshold
import Purelib.Measure.Classified.Threshold
import Purelib.Measure.Classified.Soundness
import Mathlib.Algebra.Ring.Defs
import Purelib.Approximation.Bound.Process
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Measure.Weighted.Enclosure.Process
public import Purelib.Measure.Distribution.Enclosure.Basic

@[expose] public section

/-!
# Executable finite measure examples

All numerical examples reduce to finite rational calculations checked by the
kernel.  The final examples exercise the generic CCL area-request interface
without postulating a completed CCL value.
-/

namespace Purelib.Examples.Measure.Distribution.Threshold.Coin.WorkedExamples

open Purelib.Approximation
open Purelib.Data.Rat
open Purelib
open Purelib.Examples
open Purelib.Measure
open Purelib.Examples.Measure.Distribution.Coin.Basic (coinNumber fairCoin)
open Purelib.Examples.Measure.Distribution.Expectation.Enclosed.Coin.WorkedExamples
  (coarseCoinRange coinPointwiseProcess coinRangeState)

/-- Every positive pointwise request resolves the coin-number threshold one half on each retained atom. -/
theorem coinRequestResolvesHalfThreshold
    (state : coinPointwiseProcess.State) (epsilon :
      Fraction.Rational)
    (positive : 0 < epsilon) (atom : Weighted Bool)
    (_member : atom ∈ fairCoin.atoms) :
    ThresholdResolved
      (coinPointwiseProcess.ranges
        (coinPointwiseProcess.request state epsilon
          positive) atom.item)
      (1 / 2) := by
  change ThresholdResolved (coinRangeState true atom.item)
    (1 / 2)
  cases atom.item
  · exact Or.inr (by decide)
  · exact Or.inl (by decide)

/-- The probability-bound process induced by the resolving pointwise coin ranges at threshold one half. -/
def coinThresholdProcess : BoundProcess :=
  coinPointwiseProcess.toThresholdBoundProcess (1 / 2)
    coinRequestResolvesHalfThreshold

/-- Every retained coin range contains its original coin-number value. -/
theorem coinRangesAdmitCoinNumber
    (state : coinPointwiseProcess.State) (atom : Weighted
      Bool)
    (_member : atom ∈ fairCoin.atoms) :
    (coinPointwiseProcess.ranges state atom.item).Contains
      (coinNumber atom.item) := by
  cases state <;> cases atom.item
  all_goals
    simp only [coinPointwiseProcess,
      coinRangeState,
      coarseCoinRange,
      Measure.Distribution.Expectation.Enclosed.Coin.WorkedExamples.exactCoinRange,
      coinNumber, Interval.Contains, -eq_self, -iff_self]
    exact ⟨by decide, by decide⟩

/-- The finite threshold classification process for the fair-coin event of value at least one half. -/
def coinThresholdClassificationProcess :
    ClassificationProcess fairCoin (atLeastEvent (1 / 2)
      coinNumber) :=
  coinPointwiseProcess.toThresholdClassificationProcess
    (1 / 2) coinNumber
      coinRangesAdmitCoinNumber
    (by
      intro state epsilon positive
      change fairCoin.probability
        (unresolvedStatusEvent fun outcome =>
          thresholdStatus (coinRangeState true outcome) (1
            / 2)) < epsilon
      have zero : fairCoin.probability
          (unresolvedStatusEvent fun outcome =>
            thresholdStatus (coinRangeState true outcome)
              (1 / 2)) = 0 := by
        decide
      rw [zero]
      exact positive)

/-- The initial threshold process retains the coarse frontier's original event bound. -/
example : coinThresholdProcess.bound
  coinThresholdProcess.initial =
    eventBound (fairCoin.thresholdFrontier
      coarseCoinRange (1 / 2)) := rfl

/-- A positive threshold request returns the exact probability interval at one half. -/
example : coinThresholdProcess.bound
      (coinThresholdProcess.request
        coinThresholdProcess.initial 1
        (by decide)) = Interval.exact (1 / 2) := by
  apply Interval.ext <;> decide

/-- The requested threshold approximation equals one half. -/
example : coinThresholdProcess.approximate
    coinThresholdProcess.initial 1 (by decide) = 1 / 2 := by
  decide

/-- The classification-based threshold approximation equals one half. -/
example :
  coinThresholdClassificationProcess.toBoundProcess.approximate
    coinThresholdClassificationProcess.initial 1 (by decide) = 1 / 2
      := by
  decide

/-- Every classification state retains an interval containing the original threshold-event probability. -/
example (state : coinThresholdClassificationProcess.State) :
    (coinThresholdClassificationProcess.toBoundProcess.bound
      state).Contains
      (fairCoin.probability (atLeastEvent (1 / 2)
        coinNumber)) :=
  coinThresholdClassificationProcess.probability_mem_bound state

end Purelib.Examples.Measure.Distribution.Threshold.Coin.WorkedExamples

end
