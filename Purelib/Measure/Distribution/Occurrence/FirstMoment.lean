module
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Measure.Distribution.Basic
public import Purelib.Measure.Distribution.Expectation
import Purelib.Measure.Distribution.Kernel.Basic
import Purelib.Measure.Weighted.Integral
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Cast.Order

import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order
public import Purelib.Measure.Event.Occurrence
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic

section
@[expose] public section

/-!
# Counts of occurrences in finite event families

The number of selected events in a displayed finite family is an executable
natural-valued observable.  Its exact rational expectation is the sum of the
event probabilities, and Markov's finite sum proof bounds the probability of
at least a displayed positive number of occurrences.  This is the finite
quantitative core of the first Borel--Cantelli argument, without a sequence,
limsup event, or infinite sum.
-/

namespace Purelib.Measure
namespace Distribution

open Purelib.Data.Rat
/-- Expected occurrence count equals the sum of the original probabilities of the retained event list.

Repeated events remain distinct occurrences and contribute once for each original list position. -/
theorem expectation_occurrenceCount {α : Type}
    (distribution : Distribution α) (events : List (α → Bool)) :
    distribution.expectation (fun item =>
        (occurrenceCount events item : Fraction.Rational)) =
      (events.map distribution.probability).sum := by
  induction events with
  | nil =>
      change distribution.expectation (fun _ => (0 : Fraction.Rational)) = 0
      exact distribution.expectation_constant 0
  | cons event remaining inductionHypothesis =>
      calc
        distribution.expectation (fun item =>
              (occurrenceCount (event :: remaining) item : Fraction.Rational)) =
            distribution.expectation (fun item =>
              Distribution.indicator event item +
                (occurrenceCount remaining item : Fraction.Rational)) :=
          distribution.expectation_congr _ _
            (cast_occurrenceCount_cons event remaining)
        _ = distribution.probability event +
              (remaining.map distribution.probability).sum := by
          rw [distribution.expectation_add,
            distribution.expectation_indicator,
            inductionHypothesis]
        _ = ((event :: remaining).map distribution.probability).sum := by
          simp only [-eq_self, -iff_self, List.map_cons, List.sum_cons]
          rfl

/-- The probability of at least a positive number of event occurrences is at most the event-probability sum divided by
that number. -/
theorem probability_atLeastOccurrences_le_sum_div {α : Type}
    (distribution : Distribution α) (events : List (α → Bool))
    (threshold : Nat) (positive : 0 < threshold) :
    distribution.probability (atLeastOccurrences threshold events) ≤
      (events.map distribution.probability).sum /
        (threshold : Fraction.Rational) := by
  have castPositive : 0 < (threshold : Fraction.Rational) :=
    Fraction.Cast.Order.natCast_pos_direct positive
  calc
    distribution.probability (atLeastOccurrences threshold events) ≤
        distribution.expectation (fun item =>
          (occurrenceCount events item : Fraction.Rational)) /
            (threshold : Fraction.Rational) := by
      apply distribution.markov_bound
        (atLeastOccurrences threshold events)
        (fun item => (occurrenceCount events item : Fraction.Rational))
        (threshold : Fraction.Rational) castPositive
      · intro atom member
        simpa only [Nat.cast_zero] using
          Fraction.Cast.Order.natCast_le_direct
            (Nat.zero_le (occurrenceCount events atom.item))
      · intro atom member selected
        exact Fraction.Cast.Order.natCast_le_direct
          (of_decide_eq_true selected)
    _ = (events.map distribution.probability).sum /
          (threshold : Fraction.Rational) := by
      rw [distribution.expectation_occurrenceCount events]

end Distribution
end Purelib.Measure

end
