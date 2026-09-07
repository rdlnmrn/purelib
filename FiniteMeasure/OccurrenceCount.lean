import mathlib.Tactic.QuotientFreeOmega
import FiniteMeasure.Family

/-!
# Counts of occurrences in finite event families

The number of selected events in a displayed finite family is an executable
natural-valued observable.  Its exact rational expectation is the sum of the
event probabilities, and Markov's finite sum proof bounds the probability of
at least a displayed positive number of occurrences.  This is the finite
quantitative core of the first Borel--Cantelli argument, without a sequence,
limsup event, or infinite sum.
-/

namespace FiniteMeasure

/-- Number of events selected by one item in a displayed finite family. -/
def occurrenceCount {α : Type} : List (α → Bool) → α → Nat
  | [], _ => 0
  | event :: remaining, item =>
      (if event item then 1 else 0) + occurrenceCount remaining item

/-- Executable event that at least the displayed number of members of the
family occur. -/
def atLeastOccurrences {α : Type} (threshold : Nat)
    (events : List (α → Bool)) : α → Bool :=
  fun item => decide (threshold ≤ occurrenceCount events item)

theorem occurrenceCount_le_length {α : Type}
    (events : List (α → Bool)) (item : α) :
    occurrenceCount events item ≤ events.length := by
  induction events with
  | nil => exact le_rfl
  | cons event remaining inductionHypothesis =>
      unfold occurrenceCount
      simp only [List.length_cons]
      split <;> omega

/-- Casting an occurrence count exposes the head event indicator and the
remaining count. -/
theorem cast_occurrenceCount_cons {α : Type}
    (event : α → Bool) (remaining : List (α → Bool)) (item : α) :
    (occurrenceCount (event :: remaining) item : Coordinate) =
      Distribution.indicator event item +
        (occurrenceCount remaining item : Coordinate) := by
  cases selected : event item
  · simp only [occurrenceCount, selected, Bool.false_eq_true,
      ↓reduceIte, Distribution.indicator, zero_add]
  · simp only [occurrenceCount, selected, ↓reduceIte,
      Distribution.indicator, Nat.cast_add, Nat.cast_one]

namespace Distribution

/-- Exact first-moment identity for the number of events occurring in a
displayed finite family. -/
theorem expectation_occurrenceCount {α : Type}
    (distribution : Distribution α) (events : List (α → Bool)) :
    distribution.expectation (fun item =>
        (occurrenceCount events item : Coordinate)) =
      (events.map distribution.probability).sum := by
  induction events with
  | nil =>
      change distribution.expectation (fun _ => (0 : Coordinate)) = 0
      exact distribution.expectation_constant 0
  | cons event remaining inductionHypothesis =>
      calc
        distribution.expectation (fun item =>
              (occurrenceCount (event :: remaining) item : Coordinate)) =
            distribution.expectation (fun item =>
              Distribution.indicator event item +
                (occurrenceCount remaining item : Coordinate)) :=
          distribution.expectation_congr _ _
            (cast_occurrenceCount_cons event remaining)
        _ = distribution.probability event +
              (remaining.map distribution.probability).sum := by
          rw [distribution.expectation_add,
            distribution.expectation_indicator,
            inductionHypothesis]
        _ = ((event :: remaining).map distribution.probability).sum := by
          simp only [List.map_cons, List.sum_cons]

/-- Finite occurrence-count bound: the probability that at least `threshold`
members of a displayed family occur is at most the sum of their probabilities
divided by that positive natural threshold. -/
theorem probability_atLeastOccurrences_le_sum_div {α : Type}
    (distribution : Distribution α) (events : List (α → Bool))
    (threshold : Nat) (positive : 0 < threshold) :
    distribution.probability (atLeastOccurrences threshold events) ≤
      (events.map distribution.probability).sum /
        (threshold : Coordinate) := by
  have castPositive : 0 < (threshold : Coordinate) :=
    RFAP.ConstructiveFraction.natCast_pos_direct positive
  calc
    distribution.probability (atLeastOccurrences threshold events) ≤
        distribution.expectation (fun item =>
          (occurrenceCount events item : Coordinate)) /
            (threshold : Coordinate) := by
      apply distribution.markov_bound
        (atLeastOccurrences threshold events)
        (fun item => (occurrenceCount events item : Coordinate))
        (threshold : Coordinate) castPositive
      · intro atom member
        simpa only [Nat.cast_zero] using
          RFAP.ConstructiveFraction.natCast_le_direct
            (Nat.zero_le (occurrenceCount events atom.item))
      · intro atom member selected
        exact RFAP.ConstructiveFraction.natCast_le_direct
          (of_decide_eq_true selected)
    _ = (events.map distribution.probability).sum /
          (threshold : Coordinate) := by
      rw [distribution.expectation_occurrenceCount events]

end Distribution

/-- Pointwise, at least one event occurs exactly when the displayed finite
union is selected. -/
theorem atLeastOccurrences_one_eq_unionEvents {α : Type}
    (events : List (α → Bool)) (item : α) :
    atLeastOccurrences 1 events item = unionEvents events item := by
  induction events with
  | nil => rfl
  | cons event remaining inductionHypothesis =>
      cases selected : event item
      · simp only [atLeastOccurrences, occurrenceCount, selected,
          Bool.false_eq_true, ↓reduceIte, Nat.zero_add, unionEvents,
          unionEvent, Bool.false_or]
        exact inductionHypothesis
      · simp only [atLeastOccurrences, occurrenceCount, selected,
          ↓reduceIte, unionEvents, unionEvent, Bool.true_or]
        exact decide_eq_true_eq.mpr (by omega)

end FiniteMeasure
