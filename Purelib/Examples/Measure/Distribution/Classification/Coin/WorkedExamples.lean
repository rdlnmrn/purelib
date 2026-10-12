module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Interval.Basic
import Purelib.Examples.Approximation.Bound.Process.WorkedExamples
public import Purelib.Examples.Measure.Distribution.Coin.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Measure.Classified.Soundness
public import Purelib.Measure.Classified.FixedLawProcess
import Purelib.Measure.Classified.Basic
import Purelib.Measure.Weighted.Event
import Purelib.Measure.Classified.Distribution
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Measure.Classified.Split
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Weighted.Basic
public import Purelib.Measure.Distribution.Kernel.Basic
public import Purelib.Measure.Weighted.Operations

@[expose] public section

/-!
# Executable finite measure examples

All numerical examples reduce to finite rational calculations checked by the
kernel.  The final examples exercise the generic CCL area-request interface
without postulating a completed CCL value.
-/

namespace Purelib.Examples.Measure.Distribution.Classification.Coin.WorkedExamples

open Purelib.Data.Rat
open Purelib.Examples
open Purelib.Examples.Measure.Distribution
open Purelib.Measure
open Purelib.Examples.Approximation.Bound.Process.WorkedExamples (eighthRequest halfRequest twoAccuracyRequests)
open Purelib.Examples.Measure.Distribution.Coin.Basic (fairCoin)

/-- The partial heads classification with tails outside and heads unresolved. -/
def partialCoinStatus (outcome : Bool) :
  Status :=
  if outcome then .unresolved else .outside

/-- The partial classification admits the original heads event on every fair-coin atom. -/
theorem partialCoinStatus_sound :
    ClassificationSoundOn fairCoin.atoms
      partialCoinStatus
      (fun outcome => outcome) := by
  intro atom member
  cases atom.item <;> trivial

/-- The partial heads event enclosure is the interval from zero to one half. -/
example : Purelib.Measure.eventBound (fairCoin.classifiedEventFrontier
  partialCoinStatus) =
    ⟨0, 1 / 2, by decide⟩ := open Purelib in by
  apply Interval.ext <;> decide

/-- The partial enclosure width equals the probability of the unresolved status event. -/
example : (Purelib.Measure.eventBound
      (fairCoin.classifiedEventFrontier
        partialCoinStatus)).width =
    fairCoin.probability (unresolvedStatusEvent
      partialCoinStatus) :=
  fairCoin.classifiedEventFrontier_width
    partialCoinStatus

/-- The partial event enclosure contains the exact heads probability. -/
example : (Purelib.Measure.eventBound
      (fairCoin.classifiedEventFrontier
        partialCoinStatus)).Contains
    (fairCoin.probability fun outcome => outcome) :=
  fairCoin.probability_mem_classifiedEventFrontier
    partialCoinStatus
    (fun outcome => outcome) partialCoinStatus_sound

/-- The exact heads status table, with heads inside and tails outside. -/
def exactCoinStatus (outcome : Bool) :
  Status :=
  if outcome then .inside else .outside

/-- The two-state classifier switching from the partial table to the exact table. -/
def coinClassificationStatus (refined
  outcome : Bool) : Status :=
  if refined then exactCoinStatus outcome else
    partialCoinStatus outcome

/-- The finite heads classification process.

Every positive request returns the exact table, refining the initial classification and making unresolved probability
zero. -/
def coinClassificationProcess :
    ClassificationProcess fairCoin (fun outcome => outcome) where
  State := Bool
  status := coinClassificationStatus
  initial := false
  request state epsilon positive := true
  sound state := by
    intro atom member
    cases state <;> cases atom.item <;>
      (simp only [-eq_self, -iff_self, coinClassificationStatus,
        exactCoinStatus,
        partialCoinStatus]
       trivial)
  request_refines state epsilon positive atom member := by
    cases state <;> cases atom.item <;>
      (simp only [-eq_self, -iff_self, coinClassificationStatus,
        exactCoinStatus,
        partialCoinStatus]
       simp only [-eq_self, -iff_self, Status.Refines]
       trivial)
  accurate state epsilon positive := by
    rw [Distribution.probability, fairCoin]
    change (0 : Fraction.Rational) < epsilon
    exact positive
  refinesInitial state atom member := by
    cases state <;> cases atom.item <;>
      (simp only [-eq_self, -iff_self, coinClassificationStatus,
        exactCoinStatus,
        partialCoinStatus]
       simp only [-eq_self, -iff_self, Status.Refines]
       trivial)

/-- The initial classification-process bound is the interval from zero to one half. -/
example : coinClassificationProcess.toBoundProcess.bound
      coinClassificationProcess.initial =
    ⟨0, 1 / 2, by decide⟩ := open Purelib in by
  apply Interval.ext <;> decide

/-- A positive request produces the exact interval at one half. -/
example : coinClassificationProcess.toBoundProcess.bound
      (coinClassificationProcess.request
        coinClassificationProcess.initial 1 (by decide)) =
    Purelib.Data.Rat.Interval.exact (1 / 2) := open Purelib in by
  apply Interval.ext <;> decide

/-- Every retained classification state bounds the original heads probability. -/
example (state : coinClassificationProcess.State) :
    (coinClassificationProcess.toBoundProcess.bound
      state).Contains
      (fairCoin.probability fun outcome => outcome) :=
  coinClassificationProcess.probability_mem_bound state

/-- The process approximation is within the requested positive error of the same original heads probability in both
directions. -/
example (state : coinClassificationProcess.State)
    (epsilon : Fraction.Rational) (positive : 0 < epsilon) :
    fairCoin.probability (fun outcome => outcome) -
          coinClassificationProcess.toBoundProcess.approximate
            state epsilon positive < epsilon ∧
      coinClassificationProcess.toBoundProcess.approximate
            state epsilon positive -
          fairCoin.probability (fun outcome => outcome) < epsilon :=
  coinClassificationProcess.probability_close_to_approximation
    state epsilon positive

/-- The requested approximation from the initial state is one half. -/
example : coinClassificationProcess.toBoundProcess.approximate
    coinClassificationProcess.initial 1 (by decide) = 1 / 2 :=
      by
  decide

/-- The completed two-request sequence has unresolved probability below its retained one-eighth tolerance. -/
example : fairCoin.probability
      (unresolvedStatusEvent
        (coinClassificationProcess.status
          (coinClassificationProcess.runRequests
            coinClassificationProcess.initial
              twoAccuracyRequests))) <
    eighthRequest.tolerance := by
  apply
    Classification.Coin.WorkedExamples.coinClassificationProcess.runRequests_unresolved_probability_lt_of_mem
    coinClassificationProcess.initial
      twoAccuracyRequests
      Approximation.Bound.Process.WorkedExamples.eighthRequest
  exact List.mem_cons_of_mem Approximation.Bound.Process.WorkedExamples.halfRequest List.mem_cons_self

/-- The two-request approximation is one half. -/
example : coinClassificationProcess.runRequestsApproximation
    coinClassificationProcess.initial
      twoAccuracyRequests = 1 / 2 := by
  decide

/-- The two-request approximation meets the retained one-eighth probability-error tolerance in both directions. -/
example : fairCoin.probability (fun outcome => outcome) -
        coinClassificationProcess.runRequestsApproximation
          coinClassificationProcess.initial
            twoAccuracyRequests <
      eighthRequest.tolerance ∧
    coinClassificationProcess.runRequestsApproximation
          coinClassificationProcess.initial
            twoAccuracyRequests -
        fairCoin.probability (fun outcome => outcome) <
      eighthRequest.tolerance := by
  apply coinClassificationProcess
    |>.runRequests_probability_close_to_approximation_of_mem
      coinClassificationProcess.initial
        twoAccuracyRequests
        Approximation.Bound.Process.WorkedExamples.eighthRequest
  exact List.mem_cons_of_mem Approximation.Bound.Process.WorkedExamples.halfRequest List.mem_cons_self

end Purelib.Examples.Measure.Distribution.Classification.Coin.WorkedExamples

end
