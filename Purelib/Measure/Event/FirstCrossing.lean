module
import Purelib.Data.Bool.Decide
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Measure.Distribution.Kernel.Basic
public import Purelib.Measure.Event.Family
import Purelib.Measure.Weighted.Basic
import Purelib.Measure.Weighted.Event
import Purelib.Data.Rat.Fraction
public import Purelib.Measure.Event.RationalOrder

section
public section

/-!
# Finite first-crossing maximal inequality

A displayed list of rational observables has explicit first-crossing events
at every positive threshold.  These events are disjoint.  If each crossing
value transfers its restricted integral to one nonnegative terminal
observable, finite subadditivity and disjoint additivity give the sharp
Doob-style L1 maximal inequality.  The transfer property is explicit data;
there is no unbounded time, stopping-time space, or optional-limit theorem.
-/

namespace Purelib.Measure

open Purelib.Data

open Purelib in
open Purelib.Data.Rat in
/-- Construct the exact first-threshold-crossing event at each retained stage among the initially active payloads.

After each stage, remove its selected crossing from the active event before continuing through the same remaining
observables. The output order matches the original observable list. -/
@[expose] def firstCrossingEventsFrom {α : Type} (active : α → Bool)
    (threshold : Fraction.Rational) : List (α → Fraction.Rational) →
      List (α → Bool)
  | [] => []
  | value :: remaining =>
      intersectionEvent active (Measure.atLeastEvent threshold value) ::
        firstCrossingEventsFrom
          (intersectionEvent active
            (complementEvent (Measure.atLeastEvent threshold value)))
          threshold remaining

open Purelib.Data.Rat in
/-- Construct first-threshold-crossing events starting with all payloads active. -/
@[expose] def firstCrossingEvents {α : Type} (threshold : Fraction.Rational)
    (values : List (α → Fraction.Rational)) : List (α → Bool) :=
  firstCrossingEventsFrom (fun _ => true) threshold values

section
open Purelib
open Purelib.Data.Rat
/-- Retain initially active payloads that stay strictly below the threshold at every supplied finite stage. -/
@[expose] def survivingEventFrom {α : Type} (active : α → Bool)
    (threshold : Fraction.Rational) : List (α → Fraction.Rational) → α → Bool
  | [] => active
  | value :: remaining =>
      survivingEventFrom
        (intersectionEvent active
          (complementEvent (Measure.atLeastEvent threshold value)))
        threshold remaining

/-- Surviving an appended stage list equals surviving its prefix and then its suffix with the exact remaining active
event. -/
theorem survivingEventFrom_append {α : Type} (active : α → Bool)
    (threshold : Fraction.Rational) :
    ∀ (left right : List (α → Fraction.Rational)),
      survivingEventFrom active threshold (left ++ right) =
        survivingEventFrom (survivingEventFrom active threshold left)
          threshold right
  | [], right => rfl
  | value :: remaining, right => by
      simp only [-eq_self, -iff_self, List.cons_append, survivingEventFrom]
      exact survivingEventFrom_append
        (intersectionEvent active
          (complementEvent (Measure.atLeastEvent threshold value)))
        threshold remaining right

/-- Split an appended first-crossing construction at its exact surviving prefix event. -/
theorem firstCrossingEventsFrom_append {α : Type}
    (active : α → Bool) (threshold : Fraction.Rational) :
    ∀ (left right : List (α → Fraction.Rational)),
      firstCrossingEventsFrom active threshold (left ++ right) =
        firstCrossingEventsFrom active threshold left ++
          firstCrossingEventsFrom
            (survivingEventFrom active threshold left) threshold right
  | [], right => rfl
  | value :: remaining, right => by
      change _ :: _ = _ :: _
      exact congrArg (List.cons (intersectionEvent active
        (Measure.atLeastEvent threshold value)))
        (firstCrossingEventsFrom_append
          (intersectionEvent active
            (complementEvent (Measure.atLeastEvent threshold value)))
          threshold remaining right)

end

open Purelib.Data.Rat in
/-- First-crossing construction retains exactly one event per supplied stage. -/
theorem firstCrossingEventsFrom_length {α : Type}
    (active : α → Bool) (threshold : Fraction.Rational) :
    ∀ values : List (α → Fraction.Rational),
      (firstCrossingEventsFrom active threshold values).length = values.length
  | [] => rfl
  | value :: remaining => by
      simp only [-eq_self, -iff_self, firstCrossingEventsFrom, List.length_cons]
      rw [firstCrossingEventsFrom_length]

section
open Purelib
open Purelib.Data.Rat
/-- The union of first crossings equals the initially active event intersected with any retained threshold crossing. -/
theorem unionEvents_firstCrossingEventsFrom {α : Type}
    (threshold : Fraction.Rational) :
    ∀ (values : List (α → Fraction.Rational)) (active : α → Bool) (item : α),
      unionEvents (firstCrossingEventsFrom active threshold values) item =
        intersectionEvent active
          (unionEvents (values.map (Measure.atLeastEvent threshold))) item
  | [], active, item => by
      simp only [-eq_self, -iff_self, firstCrossingEventsFrom, unionEvents, List.map_nil,
        intersectionEvent]
      cases active item <;> rfl
  | value :: remaining, active, item => by
      simp only [-eq_self, -iff_self, firstCrossingEventsFrom, List.map_cons, unionEvents,
        unionEvent]
      rw [unionEvents_firstCrossingEventsFrom threshold remaining
        (intersectionEvent active
          (complementEvent (Measure.atLeastEvent threshold value))) item]
      simp only [-eq_self, -iff_self, intersectionEvent, complementEvent]
      cases active item <;>
        cases Measure.atLeastEvent threshold value item <;>
        cases unionEvents
          (remaining.map (Measure.atLeastEvent threshold)) item <;> rfl

/-- The union of first-crossing events equals the union of the original threshold events pointwise. -/
theorem unionEvents_firstCrossingEvents {α : Type}
    (threshold : Fraction.Rational) (values : List (α → Fraction.Rational)) (item : α) :
    unionEvents (firstCrossingEvents threshold values) item =
      unionEvents (values.map (Measure.atLeastEvent threshold)) item := by
  rw [firstCrossingEvents,
    unionEvents_firstCrossingEventsFrom threshold values (fun _ => true) item]
  unfold intersectionEvent
  rfl

/-- First crossings from any retained active event are mutually disjoint on every exact weighted occurrence list. -/
theorem firstCrossingEventsFrom_mutuallyDisjointOn {α : Type}
    (atoms : List (Weighted α)) (threshold : Fraction.Rational) :
    ∀ (values : List (α → Fraction.Rational)) (active : α → Bool),
      MutuallyDisjointOn atoms
        (firstCrossingEventsFrom active threshold values)
  | [], active => trivial
  | value :: remaining, active => by
      constructor
      · intro atom member both
        have tailUnion := both.2
        rw [unionEvents_firstCrossingEventsFrom threshold remaining
          (intersectionEvent active
            (complementEvent
              (Measure.atLeastEvent threshold value))) atom.item] at tailUnion
        have hitTrue : Measure.atLeastEvent threshold value atom.item =
            true := ((Bool.Decide.and_true_iff _ _).mp both.1).2
        have tailActive : intersectionEvent active
            (complementEvent (Measure.atLeastEvent threshold value))
              atom.item = true :=
          ((Bool.Decide.and_true_iff _ _).mp tailUnion).1
        have hitFalse : complementEvent
            (Measure.atLeastEvent threshold value) atom.item = true :=
          ((Bool.Decide.and_true_iff _ _).mp tailActive).2
        unfold complementEvent at hitFalse
        rw [hitTrue] at hitFalse
        exact Bool.noConfusion hitFalse
      · exact firstCrossingEventsFrom_mutuallyDisjointOn atoms threshold
          remaining
          (intersectionEvent active
            (complementEvent (Measure.atLeastEvent threshold value)))

end

open Purelib.Data.Rat in
/-- The finite first-crossing event list is mutually disjoint on every exact weighted occurrence list. -/
theorem firstCrossingEvents_mutuallyDisjointOn {α : Type}
    (atoms : List (Weighted α)) (threshold : Fraction.Rational)
    (values : List (α → Fraction.Rational)) :
    MutuallyDisjointOn atoms (firstCrossingEvents threshold values) :=
  firstCrossingEventsFrom_mutuallyDisjointOn atoms threshold values
    (fun _ => true)

end Purelib.Measure

end
