module
import Purelib.Data.List.Membership
public import Purelib.Examples.Measure.Distribution.Product.Coin.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Examples.Measure.Distribution.Coin.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Measure.Event.Occurrence
import Purelib.Measure.Event.Family
import Purelib.Measure.Distribution.Occurrence.SecondMoment
import Purelib.Measure.Distribution.Occurrence.Independent
import Purelib.Measure.Distribution.Product.Independence
import Purelib.Measure.Distribution.Basic
public import Purelib.Measure.Distribution.Independence.Basic

@[expose] public section

/-!
# Executable finite measure examples

All numerical examples reduce to finite rational calculations checked by the
kernel.  The final examples exercise the generic CCL area-request interface
without postulating a completed CCL value.
-/

namespace Purelib.Examples.Measure.Distribution.Product.IndependentEvents.Coin.WorkedExamples

open Purelib.Data.Rat
open Purelib.Examples
open Purelib.Examples.Measure.Distribution
open Purelib.Measure
open Purelib.Examples.Measure.Distribution.Coin.Basic (fairCoin)
open Purelib.Examples.Measure.Distribution.Product.Coin.Basic.WorkedExamples (twoCoins)

/-- The ordered heads events of the two retained coin coordinates. -/
def twoCoinHeadEvents : List
  (Bool × Bool → Bool) :=
  [fun outcome => outcome.1, fun outcome => outcome.2]

/-- The two coordinate heads events are pairwise independent in the original product law. -/
theorem
  twoCoinHeadEvents_pairwiseIndependent
  :
    twoCoins.PairwiseIndependentEventList
      twoCoinHeadEvents := by
  unfold twoCoinHeadEvents
    Distribution.PairwiseIndependentEventList
  constructor
  · intro candidate member
    have member := Purelib.Data.List.Membership.mem_singleton.mp member
    subst candidate
    exact fairCoin.product_independentEvents_coordinates
      fairCoin
      (fun outcome => outcome) (fun outcome => outcome)
  · constructor
    · intro candidate member
      cases member
    · trivial

/-- The expected pair-occurrence count equals the retained sum of pair-intersection probabilities. -/
example : twoCoins.expectation (fun outcome =>
      (Purelib.Measure.pairOccurrenceCount
        twoCoinHeadEvents outcome :
        Fraction.Rational)) =
    twoCoins.pairIntersectionProbabilitySum
      twoCoinHeadEvents :=
  twoCoins.expectation_pairOccurrenceCount
    twoCoinHeadEvents

/-- The sum of individual heads probabilities minus their pair intersection bounds the union probability from below. -/
example : (twoCoinHeadEvents.map
  twoCoins.probability).sum -
        twoCoins.pairIntersectionProbabilitySum
          twoCoinHeadEvents ≤
      twoCoins.probability (Purelib.Measure.unionEvents
        twoCoinHeadEvents) :=
  twoCoins.probability_unionEvents_lower_bonferroni_two
    twoCoinHeadEvents

/-- The two-event Bonferroni lower bound and union probability both equal three quarters. -/
example : (twoCoinHeadEvents.map
  twoCoins.probability).sum -
          twoCoins.pairIntersectionProbabilitySum
            twoCoinHeadEvents = 3 / 4 ∧
      twoCoins.probability (Purelib.Measure.unionEvents
        twoCoinHeadEvents) = 3 / 4 := by
  decide

/-- The independent heads occurrence-count variance is the sum of its individual Bernoulli variances. -/
example : twoCoins.variance (fun outcome =>
      (Purelib.Measure.occurrenceCount
        twoCoinHeadEvents outcome :
        Fraction.Rational)) =
    (twoCoinHeadEvents.map fun event =>
      twoCoins.probability event *
      (1 - twoCoins.probability event)).sum :=

    Product.Coin.Basic.WorkedExamples.twoCoins.variance_occurrenceCount_of_pairwiseIndependentEventList
    twoCoinHeadEvents
      twoCoinHeadEvents_pairwiseIndependent

/-- The two-coordinate heads occurrence count has variance one half. -/
example : twoCoins.variance (fun outcome =>
    (Purelib.Measure.occurrenceCount
      twoCoinHeadEvents outcome :
      Fraction.Rational)) = 1 / 2 := by
  rw
    [Product.Coin.Basic.WorkedExamples.twoCoins.variance_occurrenceCount_of_pairwiseIndependentEventList
    twoCoinHeadEvents
      twoCoinHeadEvents_pairwiseIndependent]
  decide

/-- The heads occurrence second moment is bounded by the first moment plus its square. -/
example : twoCoins.expectation (fun outcome =>
        (Purelib.Measure.occurrenceCount
          twoCoinHeadEvents outcome :
          Fraction.Rational) ^ 2) ≤
      (twoCoinHeadEvents.map
        twoCoins.probability).sum +
        (twoCoinHeadEvents.map
          twoCoins.probability).sum ^ 2 :=
  twoCoins
    |>.expectation_occurrenceCount_sq_le_sum_add_sq_of_pairwiseIndependent
      twoCoinHeadEvents
        twoCoinHeadEvents_pairwiseIndependent

/-- Pairwise independence gives the first-moment-over-one-plus-first-moment union lower bound. -/
example : (twoCoinHeadEvents.map
  twoCoins.probability).sum /
        (1 + (twoCoinHeadEvents.map
          twoCoins.probability).sum) ≤
      twoCoins.probability (Purelib.Measure.unionEvents
        twoCoinHeadEvents) :=
  twoCoins.pairwiseIndependent_union_lower_bound
    twoCoinHeadEvents
    twoCoinHeadEvents_pairwiseIndependent (by decide)

/-- The independent-event lower bound is one half and the heads union probability is three quarters. -/
example : (twoCoinHeadEvents.map
  twoCoins.probability).sum /
          (1 + (twoCoinHeadEvents.map
            twoCoins.probability).sum) = 1 / 2 ∧
      twoCoins.probability (Purelib.Measure.unionEvents
        twoCoinHeadEvents) = 3 / 4 := by
  decide

end Purelib.Examples.Measure.Distribution.Product.IndependentEvents.Coin.WorkedExamples

end
