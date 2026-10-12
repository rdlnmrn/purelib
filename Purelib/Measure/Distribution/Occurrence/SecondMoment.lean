module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Cast.Order
public import Purelib.Measure.Event.Occurrence
public import Purelib.Measure.Distribution.Moments.PaleyZygmund
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.Expectation
import Purelib.Measure.Event.Family
import Purelib.Measure.Distribution.Occurrence.FirstMoment
import Purelib.Measure.Weighted.Event
import Purelib.Measure.Weighted.Integral
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Measure.Distribution.Stability
import Purelib.Tactic.Ring

section
@[expose] public section

/-!
# Second moments of finite event counts

Expanding the square of a displayed occurrence count gives the exact sum of
the individual probabilities and twice the pair-intersection sum.  Applying
the finite Paley--Zygmund inequality at fraction zero then gives the standard
second-moment lower bound for a finite union.  All sums and events are
displayed and finite.
-/

namespace Purelib.Measure
namespace Distribution

section
open Purelib.Data.Rat
/-- Sum intersection probabilities over pairs of distinct positions in the original ordered event list.

The recursive sum pairs the current event occurrence with every later occurrence, retaining repeated event values at
their distinct positions. -/
def pairIntersectionProbabilitySum {α : Type}
    (distribution : Distribution α) : List (α → Bool) → Fraction.Rational
  | [] => 0
  | event :: remaining =>
      (remaining.map fun candidate =>
        distribution.probability
          (intersectionEvent event candidate)).sum +
        distribution.pairIntersectionProbabilitySum remaining

/-- An event indicator times an occurrence count has expectation equal to the corresponding intersection-probability
sum. -/
theorem expectation_indicator_mul_occurrenceCount {α : Type}
    (distribution : Distribution α) (event : α → Bool)
    (remaining : List (α → Bool)) :
    distribution.expectation (fun item =>
        Distribution.indicator event item *
          (occurrenceCount remaining item : Fraction.Rational)) =
      (remaining.map fun candidate =>
        distribution.probability
          (intersectionEvent event candidate)).sum := by
  induction remaining with
  | nil =>
      calc
        distribution.expectation (fun item =>
              Distribution.indicator event item *
                (occurrenceCount [] item : Fraction.Rational)) =
            distribution.expectation (fun _ => (0 : Fraction.Rational)) :=
          distribution.expectation_congr _ _ (fun item => by
            simp only [occurrenceCount, Nat.cast_zero, mul_zero, -eq_self, -iff_self]
            rfl)
        _ = 0 := distribution.expectation_constant 0
  | cons candidate remaining inductionHypothesis =>
      calc
        distribution.expectation (fun item =>
              Distribution.indicator event item *
                (occurrenceCount (candidate :: remaining) item :
                  Fraction.Rational)) =
            distribution.expectation (fun item =>
              Distribution.indicator event item *
                  Distribution.indicator candidate item +
                Distribution.indicator event item *
                  (occurrenceCount remaining item : Fraction.Rational)) :=
          distribution.expectation_congr _ _ (fun item => by
            rw [cast_occurrenceCount_cons]
            ring1)
        _ = distribution.probability
                (intersectionEvent event candidate) +
              (remaining.map fun later =>
                distribution.probability
                  (intersectionEvent event later)).sum := by
          rw [distribution.expectation_add,
            distribution.expectation_indicator_mul_indicator,
            inductionHypothesis]
        _ = ((candidate :: remaining).map fun later =>
              distribution.probability
                (intersectionEvent event later)).sum := by
          rfl

/-- Expected pair-occurrence count equals the exact retained pair-intersection probability sum. -/
theorem expectation_pairOccurrenceCount {α : Type}
    (distribution : Distribution α) (events : List (α → Bool)) :
    distribution.expectation (fun item =>
        (pairOccurrenceCount events item : Fraction.Rational)) =
      distribution.pairIntersectionProbabilitySum events := by
  induction events with
  | nil =>
      change distribution.expectation (fun _ => (0 : Fraction.Rational)) = 0
      exact distribution.expectation_constant 0
  | cons event remaining inductionHypothesis =>
      calc
        distribution.expectation (fun item =>
              (pairOccurrenceCount (event :: remaining) item :
                Fraction.Rational)) =
            distribution.expectation (fun item =>
              Distribution.indicator event item *
                  (occurrenceCount remaining item : Fraction.Rational) +
                (pairOccurrenceCount remaining item : Fraction.Rational)) :=
          distribution.expectation_congr _ _
            (cast_pairOccurrenceCount_cons event remaining)
        _ = distribution.pairIntersectionProbabilitySum
              (event :: remaining) := by
          rw [distribution.expectation_add,
            distribution.expectation_indicator_mul_occurrenceCount event
              remaining,
            inductionHypothesis]
          rfl

end

open Purelib.Data.Rat in
open Purelib.Measure in
/-- The occurrence-count second moment equals the event-probability sum plus twice the pair-intersection sum. -/
theorem expectation_occurrenceCount_sq {α : Type}
    (distribution : Distribution α) (events : List (α → Bool)) :
    distribution.expectation (fun item =>
        (occurrenceCount events item : Fraction.Rational) ^ 2) =
      (events.map distribution.probability).sum +
        2 * distribution.pairIntersectionProbabilitySum events := by
  induction events with
  | nil =>
      calc
        distribution.expectation (fun item : α =>
              (occurrenceCount ([] : List (α → Bool)) item :
                Fraction.Rational) ^ 2) =
            distribution.expectation (fun _ : α => (0 : Fraction.Rational)) :=
          distribution.expectation_congr _ _ (fun _ => by
            change (0 : Fraction.Rational) ^ 2 = 0
            ring1)
        _ = 0 := distribution.expectation_constant 0
        _ = ([].map distribution.probability).sum +
              2 * distribution.pairIntersectionProbabilitySum [] := by
          simp only [List.map_nil, List.sum_nil,
            Distribution.pairIntersectionProbabilitySum, mul_zero, add_zero, -eq_self, -iff_self]
          rfl
  | cons event remaining inductionHypothesis =>
      calc
        distribution.expectation (fun item =>
              (occurrenceCount (event :: remaining) item : Fraction.Rational) ^ 2) =
            distribution.expectation (fun item =>
              Distribution.indicator event item +
                2 * (Distribution.indicator event item *
                  (occurrenceCount remaining item : Fraction.Rational)) +
                (occurrenceCount remaining item : Fraction.Rational) ^ 2) :=
          distribution.expectation_congr _ _ (fun item => by
            rw [cast_occurrenceCount_cons]
            cases selected : event item <;>
              simp only [Distribution.indicator, selected] <;> ring1)
        _ = ((event :: remaining).map distribution.probability).sum +
              2 * distribution.pairIntersectionProbabilitySum
                (event :: remaining) := by
          rw [distribution.expectation_add,
            distribution.expectation_add,
            distribution.expectation_indicator,
            distribution.expectation_scale,
            distribution.expectation_indicator_mul_occurrenceCount event
              remaining,
            inductionHypothesis]
          simp only [List.map_cons, List.sum_cons,
            Distribution.pairIntersectionProbabilitySum]
          ring1

open Purelib.Data.Rat in
/-- Union probability is at least the original probability sum minus the retained pair-intersection sum. -/
theorem probability_unionEvents_lower_bonferroni_two {α : Type}
    (distribution : Distribution α) (events : List (α → Bool)) :
    (events.map distribution.probability).sum -
        distribution.pairIntersectionProbabilitySum events ≤
      distribution.probability (unionEvents events) := by
  have averaged := distribution.expectation_mono
    (fun item => (occurrenceCount events item : Fraction.Rational) -
      (pairOccurrenceCount events item : Fraction.Rational))
    (Distribution.indicator (unionEvents events)) (by
      intro atom member
      exact occurrenceCount_sub_pairOccurrenceCount_le_indicator_union
        events atom.item)
  rw [distribution.expectation_sub,
    distribution.expectation_occurrenceCount events,
    distribution.expectation_pairOccurrenceCount events,
    distribution.expectation_indicator] at averaged
  exact averaged

open Purelib in
open Purelib.Data.Rat in
open Purelib.Measure in
/-- Positive occurrence count selects exactly the union of the original event list. -/
public theorem aboveFractionZero_occurrenceCount_eq_unionEvents
    {α : Type} (distribution : Distribution α)
    (events : List (α → Bool)) (item : α) :
    distribution.aboveFractionOfMeanEvent
        (fun item => (occurrenceCount events item : Fraction.Rational)) 0 item =
      unionEvents events item := by
  calc
    distribution.aboveFractionOfMeanEvent
          (fun item => (occurrenceCount events item : Fraction.Rational)) 0 item =
        Measure.atLeastOccurrences 1 events item := by
      unfold Distribution.aboveFractionOfMeanEvent Measure.atLeastOccurrences
      simp only [zero_mul]
      cases countEq : occurrenceCount events item with
      | zero =>
          simp only [Nat.cast_zero]
          decide
      | succ count =>
          have castPositive :
              0 < ((Nat.succ count : Nat) : Fraction.Rational) :=
            Fraction.Cast.Order.natCast_pos_direct
              (Nat.zero_lt_succ count)
          have oneLe : 1 ≤ Nat.succ count := Nat.succ_le_succ (Nat.zero_le _)
          rw [decide_eq_true castPositive,
            decide_eq_true oneLe]
    _ = unionEvents events item :=
      Measure.atLeastOccurrences_one_eq_unionEvents events item

open Purelib.Data.Rat in
/-- Positive total event probability gives the second-moment lower bound on the exact finite union probability.

The lower bound is the squared probability sum divided by that sum plus twice the retained pair-intersection sum. -/
theorem secondMoment_union_lower_bound {α : Type}
    (distribution : Distribution α) (events : List (α → Bool))
    (positive : 0 < (events.map distribution.probability).sum) :
    (events.map distribution.probability).sum ^ 2 /
        ((events.map distribution.probability).sum +
          2 * distribution.pairIntersectionProbabilitySum events) ≤
      distribution.probability (unionEvents events) := by
  have countNonnegative : ∀ atom, atom ∈ distribution.atoms →
      0 ≤ (occurrenceCount events atom.item : Fraction.Rational) := by
    intro atom member
    simpa only [Nat.cast_zero] using
      Fraction.Cast.Order.natCast_le_direct
        (Nat.zero_le (occurrenceCount events atom.item))
  have meanPositive : 0 < distribution.expectation (fun item =>
      (occurrenceCount events item : Fraction.Rational)) := by
    rw [distribution.expectation_occurrenceCount events]
    exact positive
  have bound := distribution.paleyZygmund_bound
    (fun item => (occurrenceCount events item : Fraction.Rational)) 0
    le_rfl (by decide) countNonnegative meanPositive
  have eventProbability :
      distribution.probability
          (distribution.aboveFractionOfMeanEvent
            (fun item => (occurrenceCount events item : Fraction.Rational)) 0) =
        distribution.probability (unionEvents events) :=
    distribution.probability_congr _ _
      (aboveFractionZero_occurrenceCount_eq_unionEvents distribution events)
  rw [distribution.expectation_occurrenceCount events,
    distribution.expectation_occurrenceCount_sq events,
    eventProbability]
    at bound
  have coefficient : (1 - (0 : Fraction.Rational)) ^ 2 = 1 := by ring1
  rw [coefficient, one_mul] at bound
  exact bound
end Distribution

end Purelib.Measure

end
