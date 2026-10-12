module
import Purelib.Data.Rat.Fraction
import Purelib.Examples.Measure.Distribution.Coin.Basic

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
import Purelib.Measure.Event.InclusionExclusion
import Purelib.Measure.Distribution.Occurrence.FirstMoment
import Purelib.Measure.Event.Occurrence
import Purelib.Measure.Distribution.Occurrence.SecondMoment
import Purelib.Measure.EventAlgebra.Basic
import Purelib.Measure.Distribution.Content
import Purelib.Measure.Distribution.Expectation
import Purelib.Measure.Event.Family

@[expose] public section

/-!
# Executable finite measure examples

All numerical examples reduce to finite rational calculations checked by the
kernel.  The final examples exercise the generic CCL area-request interface
without postulating a completed CCL value.
-/

namespace Purelib.Examples.Measure.Distribution.Events.Occurrence.Coin.WorkedExamples

open Purelib.Data.Rat
open Purelib.Measure
open Purelib.Examples
open Purelib.Examples.Measure.Distribution.Coin.Basic (fairCoin)

/-- The list retaining three separate occurrences of the heads event. -/
def repeatedHeadsEvents : List (Bool
  → Bool) :=
  [fun outcome => outcome, fun outcome => outcome, fun outcome => outcome]

/-- The three retained event occurrences yield seven nonempty inclusion-exclusion terms. -/
example : (inclusionExclusionTerms
  repeatedHeadsEvents).length = 7 := by
  rw [inclusionExclusionTerms_length]
  decide

/-- Finite inclusion-exclusion equals the probability of the union of the retained repeated events. -/
example : inclusionExclusionValue fairCoin.toContent
      repeatedHeadsEvents =
    fairCoin.probability (unionEvents
      repeatedHeadsEvents) :=
  fairCoin.inclusionExclusionValue_eq_probability_unionEvents
    repeatedHeadsEvents

/-- The repeated-heads inclusion-exclusion value is one half. -/
example : inclusionExclusionValue fairCoin.toContent
    repeatedHeadsEvents = 1 / 2 := by
  decide

/-- The occurrence count is zero on tails and three on heads. -/
example : occurrenceCount repeatedHeadsEvents false = 0 ∧
    occurrenceCount repeatedHeadsEvents true = 3 := by
  decide

/-- The expected number of retained heads occurrences is three halves. -/
example : fairCoin.expectation (fun outcome =>
      (occurrenceCount repeatedHeadsEvents outcome :
        Fraction.Rational)) = 3 / 2 := open Purelib.Examples in by
  rw [fairCoin.expectation_occurrenceCount
    repeatedHeadsEvents]
  decide

/-- The probability of at least two heads occurrences is one half. -/
example : fairCoin.probability
    (atLeastOccurrences 2 repeatedHeadsEvents) = 1 / 2 := by
  decide

/-- The first-moment occurrence bound gives an upper bound of three quarters for at least two occurrences. -/
example : fairCoin.probability
      (atLeastOccurrences 2 repeatedHeadsEvents) ≤ 3 / 4 :=
        open Purelib.Data.Rat in open Purelib.Examples in by
  have bound := fairCoin.probability_atLeastOccurrences_le_sum_div
    repeatedHeadsEvents 2 (by omega)
  have evaluated :
      (repeatedHeadsEvents.map
        fairCoin.probability).sum /
        ((2 : Nat) : Fraction.Rational) = 3 / 4 := by
    decide
  rw [evaluated] at bound
  exact bound

/-- At least one occurrence is exactly the union event. -/
example (outcome : Bool) :
    atLeastOccurrences 1 repeatedHeadsEvents outcome =
      unionEvents repeatedHeadsEvents outcome :=
  atLeastOccurrences_one_eq_unionEvents repeatedHeadsEvents
    outcome

/-- The pair-intersection probability sum for the three repeated heads events is three halves. -/
example : fairCoin.pairIntersectionProbabilitySum
  repeatedHeadsEvents =
    3 / 2 := by
  decide

/-- The occurrence count has second moment nine halves. -/
example : fairCoin.expectation (fun outcome =>
      (occurrenceCount repeatedHeadsEvents outcome :
        Fraction.Rational) ^ 2) =
    9 / 2 := open Purelib.Examples in by
  rw [fairCoin.expectation_occurrenceCount_sq
    repeatedHeadsEvents]
  decide

/-- The finite second-moment expression is a lower bound for the repeated-event union probability. -/
example :
    (repeatedHeadsEvents.map
      fairCoin.probability).sum ^ 2 /
        ((repeatedHeadsEvents.map
          fairCoin.probability).sum +
          2 * fairCoin.pairIntersectionProbabilitySum
            repeatedHeadsEvents) ≤
      fairCoin.probability (unionEvents
        repeatedHeadsEvents) :=
  fairCoin.secondMoment_union_lower_bound
    repeatedHeadsEvents (by decide)

/-- The second-moment lower bound and the actual repeated-event union probability both equal one half. -/
example :
    (repeatedHeadsEvents.map
      fairCoin.probability).sum ^ 2 /
          ((repeatedHeadsEvents.map
            fairCoin.probability).sum +
            2 * fairCoin.pairIntersectionProbabilitySum
              repeatedHeadsEvents) =
        1 / 2 ∧
      fairCoin.probability (unionEvents
        repeatedHeadsEvents) = 1 / 2 := by
  decide

end Purelib.Examples.Measure.Distribution.Events.Occurrence.Coin.WorkedExamples

end
