module
import Purelib.Data.List.Membership
import Purelib.Measure.Distribution.Kernel.Basic
import Purelib.Measure.Weighted.Basic
public import Purelib.Measure.Weighted.Event

import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic

section
public section

/-!
# Finite event families

This is the finite constructive content of subadditivity and disjoint
additivity.  Event families are displayed lists; no countable family or
sigma-additivity principle is introduced.
-/

namespace Purelib.Measure

open Purelib.Data

/-- Take the Boolean union of the retained finite event list, using false for the empty list. -/
@[expose] def unionEvents {α : Type} : List (α → Bool) → α → Bool
  | [], _ => false
  | event :: remaining, item =>
      unionEvent event (unionEvents remaining) item

/-- Outside a finite union, every event retained in that list is false at the same payload. -/
theorem event_eq_false_of_mem_of_unionEvents_eq_false {α : Type} :
    ∀ (events : List (α → Bool)) (event : α → Bool),
      event ∈ events → ∀ item,
        unionEvents events item = false → event item = false
  | [], event, member, item, outside => by
      cases member
  | head :: remaining, event, member, item, outside => by
      have separated : head item = false ∧
          unionEvents remaining item = false := by
        cases headSelected : head item
        · cases tailSelected : unionEvents remaining item
          · exact ⟨rfl, rfl⟩
          · have impossible : true = false := by
              simpa only [-eq_self, -iff_self, unionEvents, unionEvent,
                headSelected, tailSelected, Bool.false_or] using outside
            exact Bool.noConfusion impossible
        · have impossible : true = false := by
            simpa only [-eq_self, -iff_self, unionEvents, unionEvent,
              headSelected, Bool.true_or] using outside
          exact Bool.noConfusion impossible
      rcases List.Membership.mem_cons.mp member with same | tail
      · subst event
        exact separated.1
      · exact event_eq_false_of_mem_of_unionEvents_eq_false
          remaining event tail item separated.2

/-- The everywhere-false event has weight zero on every retained occurrence list. -/
theorem eventWeight_false {α : Type} (atoms : List (Weighted α)) :
    eventWeight atoms (fun _ => false) = 0 := by
  induction atoms with
  | nil => rfl
  | cons atom remaining inductionHypothesis =>
      simp only [-eq_self, -iff_self, eventWeight, zero_add, inductionHypothesis]
      rfl

/-- The union event weight is at most the sum of its two original event weights. -/
theorem eventWeight_union_le_add {α : Type} (atoms : List (Weighted α))
    (first second : α → Bool) :
    eventWeight atoms (unionEvent first second) ≤
      eventWeight atoms first + eventWeight atoms second := by
  calc
    eventWeight atoms (unionEvent first second) ≤
        eventWeight atoms (unionEvent first second) +
          eventWeight atoms (intersectionEvent first second) :=
      le_add_of_nonneg_right
        (eventWeight_nonneg atoms (intersectionEvent first second))
    _ = eventWeight atoms first + eventWeight atoms second :=
      (eventWeight_valuation atoms first second).symm

/-- The weight of a finite event union is at most the sum of the same retained event weights. -/
theorem eventWeight_unionEvents_le_sum {α : Type}
    (atoms : List (Weighted α)) :
    ∀ events : List (α → Bool),
      eventWeight atoms (unionEvents events) ≤
        (events.map fun event => eventWeight atoms event).sum
  | [] => by
      simp only [-eq_self, -iff_self, unionEvents, List.map_nil, List.sum_nil,
        eventWeight_false]
      exact le_rfl
  | event :: remaining => by
      simp only [-eq_self, -iff_self, unionEvents, List.map_cons, List.sum_cons]
      exact (eventWeight_union_le_add atoms event (unionEvents remaining)).trans
        (add_le_add le_rfl
          (eventWeight_unionEvents_le_sum atoms remaining))

/-- Require each event to be disjoint from the union of its exact remaining events on the retained occurrences. -/
@[expose] def MutuallyDisjointOn {α : Type} (atoms : List (Weighted α)) :
    List (α → Bool) → Prop
  | [] => True
  | event :: remaining =>
      DisjointOn atoms event (unionEvents remaining) ∧
        MutuallyDisjointOn atoms remaining

/-- Mutually disjoint retained events have union weight equal to their exact finite sum of weights. -/
theorem eventWeight_unionEvents_of_disjoint {α : Type}
    (atoms : List (Weighted α)) :
    ∀ {events : List (α → Bool)},
      MutuallyDisjointOn atoms events →
      eventWeight atoms (unionEvents events) =
        (events.map fun event => eventWeight atoms event).sum
  | [], _ => by
      simp only [-eq_self, -iff_self, unionEvents, List.map_nil, List.sum_nil,
        eventWeight_false]
      rfl
  | event :: remaining, disjoint => by
      simp only [-eq_self, -iff_self, unionEvents, List.map_cons, List.sum_cons]
      rw [eventWeight_union_of_disjoint disjoint.1,
        eventWeight_unionEvents_of_disjoint atoms disjoint.2]

namespace Distribution
end Distribution

namespace Content
end Content

end Purelib.Measure

end
