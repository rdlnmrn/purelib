module
import Purelib.Data.Rat.Interval.Basic
public import Purelib.Examples.Measure.Distribution.Coin.Basic

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
import Purelib.Measure.Distribution.Enclosure.Basic
import Purelib.Measure.Distribution.Enclosure.Threshold
import Purelib.Data.List.Prefix.Cursor
import Purelib.Measure.EventAlgebra.Basic
import Purelib.Measure.Distribution.Enclosure.Process
public import Purelib.Measure.Weighted.Enclosure.Process
import Purelib.Measure.Classified.Split
import Purelib.Measure.Distribution.Expectation
import Purelib.Measure.Event.RationalOrder
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Measure.Weighted.Basic

@[expose] public section

/-!
# Executable finite measure examples

All numerical examples reduce to finite rational calculations checked by the
kernel.  The final examples exercise the generic CCL area-request interface
without postulating a completed CCL value.
-/

namespace Purelib.Examples.Measure.Distribution.Expectation.Enclosed.Coin.WorkedExamples

open Purelib.Data.Rat
open Purelib
open Purelib.Examples
open Purelib.Examples.Measure.Distribution
open Purelib.Measure
open Purelib.Examples.Measure.Distribution.Coin.Basic (coinNumber fairCoin)

/-- The coarse coin-number intervals `[0, 1/2]` on tails and `[1/2, 1]` on heads. -/
def coarseCoinRange : Bool →
  Interval
  | false => ⟨0, 1 / 2, by decide⟩
  | true => ⟨1 / 2, 1, by decide⟩

/-- The exact singleton interval at each coin-number value. -/
def exactCoinRange (outcome :
  Bool) : Interval :=
  Interval.exact (coinNumber outcome)

/-- The coarse pointwise ranges give expectation enclosure `[1/4, 3/4]`. -/
example : fairCoin.enclosedExpectation
  coarseCoinRange =
    ⟨1 / 4, 3 / 4, by decide⟩ := by
  apply Interval.ext <;> decide

/-- The coarse expectation enclosure has width one half. -/
example : (fairCoin.enclosedExpectation
  coarseCoinRange).width = 1 / 2 := by
  decide

/-- The coarse expectation enclosure contains the original fair-coin expectation. -/
example : (fairCoin.enclosedExpectation
  coarseCoinRange).Contains
    (fairCoin.expectation coinNumber) := by
  apply fairCoin.expectation_mem_enclosedExpectation
  intro atom member
  cases atom.item <;> decide

/-- Exact pointwise ranges refine the coarse expectation enclosure. -/
example : Interval.Refines
    (fairCoin.enclosedExpectation
      exactCoinRange)
    (fairCoin.enclosedExpectation
      coarseCoinRange) := by
  apply fairCoin.enclosedExpectation_refines
  intro atom member
  cases atom.item
  · exact ⟨by decide, by decide⟩
  · exact ⟨by decide, by decide⟩

/-- Exact pointwise ranges give the exact expectation interval at one half. -/
example : fairCoin.enclosedExpectation
  exactCoinRange =
    Interval.exact (1 / 2) := by
  unfold exactCoinRange
  rw [fairCoin.enclosedExpectation_exact]
  apply Interval.ext <;> decide

/-- The two-state range table selecting coarse or exact coin-number intervals. -/
def coinRangeState (refined
  outcome : Bool) : Interval :=
  if refined then exactCoinRange outcome else
    coarseCoinRange outcome

/-- The finite pointwise enclosure process resolving every range in one request.

Its exact state refines the original ranges and has zero width for every retained atom. -/
def coinPointwiseProcess :
  PointwiseEnclosureProcess fairCoin where
  State := Bool
  ranges := coinRangeState
  initial := false
  request state epsilon positive := true
  request_refines state epsilon positive atom member := by
    cases state <;> cases atom.item
    all_goals exact ⟨by decide, by decide⟩
  accurate state epsilon positive atom member := by
    cases atom.item
    all_goals
      simp only [coinRangeState,
        exactCoinRange,
        coinNumber,
        -eq_self, -iff_self]
      exact positive.le
  refinesInitial state atom member := by
    cases state <;> cases atom.item
    all_goals exact ⟨by decide, by decide⟩

/-- The initial expectation-process bound equals the coarse enclosure. -/
example :
  coinPointwiseProcess.toExpectationBoundProcess.bound
  false =
    fairCoin.enclosedExpectation
      coarseCoinRange := rfl

/-- A positive expectation request returns the exact interval at one half. -/
example :
  coinPointwiseProcess.toExpectationBoundProcess.bound

        (Expectation.Enclosed.Coin.WorkedExamples.coinPointwiseProcess.toExpectationBoundProcess.request
        false 1 (by decide)) = Interval.exact (1 / 2) := by
  change fairCoin.enclosedExpectation
    exactCoinRange = Interval.exact (1 / 2)
  unfold exactCoinRange
  rw [fairCoin.enclosedExpectation_exact]
  apply Interval.ext <;> decide

/-- The requested expectation approximation is one half. -/
example :
  Expectation.Enclosed.Coin.WorkedExamples.coinPointwiseProcess.toExpectationBoundProcess.approximate
    false 1 (by decide) = 1 / 2 := by
  decide

/-- The coarse threshold frontier at one half bounds probability by `[1/2, 1]`. -/
example : eventBound
      (fairCoin.thresholdFrontier
        coarseCoinRange (1 / 2)) =
    ⟨1 / 2, 1, by decide⟩ := by
  apply Interval.ext <;> decide

/-- The coarse threshold frontier contains the original threshold-event probability. -/
example : (eventBound
      (fairCoin.thresholdFrontier
        coarseCoinRange (1 / 2))).Contains
    (fairCoin.probability (atLeastEvent (1 / 2)
      coinNumber)) := by
  apply fairCoin.probability_mem_thresholdFrontier
  intro atom member
  cases atom.item <;> decide

/-- The exact threshold frontier refines the coarse frontier. -/
example : Interval.Refines
    (eventBound (fairCoin.thresholdFrontier
      exactCoinRange (1 / 2)))
    (eventBound (fairCoin.thresholdFrontier
      coarseCoinRange (1 / 2))) := by
  apply fairCoin.thresholdFrontier_eventBound_refines
  intro atom member
  cases atom.item
  · exact ⟨by decide, by decide⟩
  · exact ⟨by decide, by decide⟩

/-- The exact threshold frontier has zero width because both retained atoms are resolved. -/
example : (eventBound
      (fairCoin.thresholdFrontier
        exactCoinRange (1 / 2))).width = 0 := by
  apply fairCoin.thresholdFrontier_width_eq_zero_of_resolved
  intro atom member
  cases atom.item
  · exact Or.inr (by decide)
  · exact Or.inl (by decide)

end Purelib.Examples.Measure.Distribution.Expectation.Enclosed.Coin.WorkedExamples

end
