module
import Purelib.Algebra.NatCast
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Measure.Weighted.Event
import Purelib.Measure.Weighted.Integral
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Cast.Order

import Purelib.Data.Rat.Fraction.Field
public import Purelib.Measure.Event.Family
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Data.Nat.Basic
public import Purelib.Measure.Weighted.IntegralTransform

section
section
public section

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

open Purelib.Algebra

/-- Count the event-list positions selecting the supplied payload.

Each position contributes separately, including repetitions of the same Boolean event. -/
@[expose] def occurrenceCount {α : Type} : List (α → Bool) → α → Nat
  | [], _ => 0
  | event :: remaining, item =>
      (if event item then 1 else 0) + occurrenceCount remaining item

/-- Select payloads satisfying at least the requested number of event-list occurrences. -/
@[expose] def atLeastOccurrences {α : Type} (threshold : Nat)
    (events : List (α → Bool)) : α → Bool :=
  fun item => decide (threshold ≤ occurrenceCount events item)

/-- The number of selecting event positions is at most the length of the original event list. -/
theorem occurrenceCount_le_length {α : Type}
    (events : List (α → Bool)) (item : α) :
    occurrenceCount events item ≤ events.length := by
  induction events with
  | nil => exact le_rfl
  | cons event remaining inductionHypothesis =>
      unfold occurrenceCount
      simp only [-eq_self, -iff_self, List.length_cons]
      split <;> omega

open Purelib.Data.Rat in
/-- The rational occurrence count of a head event and tail is the head indicator plus the tail count. -/
theorem cast_occurrenceCount_cons {α : Type}
    (event : α → Bool) (remaining : List (α → Bool)) (item : α) :
    (occurrenceCount (event :: remaining) item : Fraction.Rational) =
      Distribution.indicator event item +
        (occurrenceCount remaining item : Fraction.Rational) := by
  cases selected : event item
  · simp only [-eq_self, -iff_self, occurrenceCount, selected, if_neg (by decide : ¬ false = true),
      Distribution.indicator, zero_add]
    rfl
  · simp only [-eq_self, -iff_self, occurrenceCount, selected, if_pos rfl,
      Distribution.indicator, NatCast.add, Nat.cast_one]
    rfl

namespace Distribution
end Distribution

/-- At least one selecting event is exactly membership in the finite event union. -/
theorem atLeastOccurrences_one_eq_unionEvents {α : Type}
    (events : List (α → Bool)) (item : α) :
    atLeastOccurrences 1 events item = unionEvents events item := by
  induction events with
  | nil => rfl
  | cons event remaining inductionHypothesis =>
      cases selected : event item
      · simp only [-eq_self, -iff_self, atLeastOccurrences, occurrenceCount, selected,
          if_neg (by decide : ¬ false = true), Nat.zero_add, unionEvents,
          unionEvent, Bool.false_or]
        exact inductionHypothesis
      · simp only [-eq_self, -iff_self, atLeastOccurrences, occurrenceCount, selected,
          if_pos rfl, unionEvents, unionEvent, Bool.true_or]
        exact decide_eq_true (by omega)

end Purelib.Measure

end

end

section
public section

/-!
# Second moments of finite event counts

Expanding the square of a displayed occurrence count gives the exact sum of
the individual probabilities and twice the pair-intersection sum.  Applying
the finite Paley--Zygmund inequality at fraction zero then gives the standard
second-moment lower bound for a finite union.  All sums and events are
displayed and finite.
-/

namespace Purelib.Measure

open Purelib.Algebra

/-- Count pairs of selecting event positions with the first position preceding the second.

For each selected head, add the selecting positions in its exact remaining tail, then recurse on that tail. -/
@[expose] def pairOccurrenceCount {α : Type} : List (α → Bool) → α → Nat
  | [], _ => 0
  | event :: remaining, item =>
      (if event item then occurrenceCount remaining item else 0) +
        pairOccurrenceCount remaining item

open Purelib.Data.Rat
/-- A head event contributes its indicator times the remaining occurrence count to the rational selecting-pair count. -/
theorem cast_pairOccurrenceCount_cons {α : Type}
    (event : α → Bool) (remaining : List (α → Bool)) (item : α) :
    (pairOccurrenceCount (event :: remaining) item : Fraction.Rational) =
      Distribution.indicator event item *
          (occurrenceCount remaining item : Fraction.Rational) +
        (pairOccurrenceCount remaining item : Fraction.Rational) := by
  cases selected : event item
  · simp only [-eq_self, -iff_self, pairOccurrenceCount, selected,
      if_neg (by decide : ¬ false = true), Distribution.indicator,
      zero_mul, zero_add]
    rfl
  · simp only [-eq_self, -iff_self, pairOccurrenceCount, selected,
      if_pos rfl, Distribution.indicator, one_mul, NatCast.add]
    rfl

/-- The rational occurrence count minus the selecting-pair count is bounded by the union indicator.

This pointwise finite Bonferroni bound keeps repeated events as distinct list positions. -/
theorem occurrenceCount_sub_pairOccurrenceCount_le_indicator_union
    {α : Type} : ∀ (events : List (α → Bool)) (item : α),
    (occurrenceCount events item : Fraction.Rational) -
        (pairOccurrenceCount events item : Fraction.Rational) ≤
      Distribution.indicator (unionEvents events) item
  | [], item => by
      change (0 : Fraction.Rational) - 0 ≤ 0
      rw [sub_self]
  | event :: remaining, item => by
      cases selected : event item
      · simpa only [-eq_self, -iff_self, occurrenceCount, pairOccurrenceCount, selected,
          if_neg (by decide : ¬ false = true), Nat.zero_add, unionEvents,
          unionEvent, Bool.false_or, Distribution.indicator] using
          occurrenceCount_sub_pairOccurrenceCount_le_indicator_union
            remaining item
      · have pairNonnegative :
            0 ≤ (pairOccurrenceCount remaining item : Fraction.Rational) := by
          simpa only [-eq_self, -iff_self, Nat.cast_zero] using
            Fraction.Cast.Order.natCast_le_direct
              (Nat.zero_le (pairOccurrenceCount remaining item))
        calc
          (occurrenceCount (event :: remaining) item : Fraction.Rational) -
                (pairOccurrenceCount (event :: remaining) item : Fraction.Rational) =
              1 - (pairOccurrenceCount remaining item : Fraction.Rational) := by
            simp only [-eq_self, -iff_self, occurrenceCount, pairOccurrenceCount, selected,
              if_pos rfl, NatCast.add, Nat.cast_one]
            ring1
          _ ≤ 1 := Fraction.Order.Arithmetic.sub_le_iff_le_add_direct.mpr (by
            have translated := Fraction.Order.Arithmetic.add_le_add_right_direct
              pairNonnegative (1 : Fraction.Rational)
            calc
              (1 : Fraction.Rational) = 0 + 1 := (Fraction.zero_add _).symm
              _ ≤ (pairOccurrenceCount remaining item : Fraction.Rational) + 1 := translated
              _ = 1 + (pairOccurrenceCount remaining item : Fraction.Rational) :=
                Fraction.add_comm _ _)
          _ = Distribution.indicator
                (unionEvents (event :: remaining)) item := by
            simp only [-eq_self, -iff_self, unionEvents, unionEvent, selected, Bool.true_or,
              Distribution.indicator]
            rfl

end Purelib.Measure

end
