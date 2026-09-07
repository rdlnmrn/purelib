import FiniteMeasure.Valuation

/-!
# Finite event families

This is the finite constructive content of subadditivity and disjoint
additivity.  Event families are displayed lists; no countable family or
sigma-additivity principle is introduced.
-/

namespace FiniteMeasure

/-- Executable union of a displayed finite event family. -/
def unionEvents {α : Type} : List (α → Bool) → α → Bool
  | [], _ => false
  | event :: remaining, item =>
      unionEvent event (unionEvents remaining) item

/-- If the displayed finite union is false at an item, then every member
event is false there.  This is the pointwise elimination rule needed to turn
one finite exceptional union into simultaneous guarantees. -/
theorem event_eq_false_of_mem_of_unionEvents_eq_false {α : Type} :
    ∀ (events : List (α → Bool)) (event : α → Bool),
      event ∈ events → ∀ item,
        unionEvents events item = false → event item = false
  | [], event, member, item, outside => by
      cases member
  | head :: remaining, event, member, item, outside => by
      have separated : head item = false ∧
          unionEvents remaining item = false := by
        cases headSelected : head item <;>
          cases tailSelected : unionEvents remaining item <;>
          simp_all [unionEvents, unionEvent]
      rcases List.mem_cons.mp member with same | tail
      · subst event
        exact separated.1
      · exact event_eq_false_of_mem_of_unionEvents_eq_false
          remaining event tail item separated.2

theorem eventWeight_false {α : Type} (atoms : List (Weighted α)) :
    eventWeight atoms (fun _ => false) = 0 := by
  induction atoms with
  | nil => rfl
  | cons atom remaining inductionHypothesis =>
      simp only [eventWeight, zero_add, inductionHypothesis]

/-- Two-event finite subadditivity follows from the valuation identity and
nonnegativity of the overlap. -/
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

/-- Finite subadditivity for every displayed event list. -/
theorem eventWeight_unionEvents_le_sum {α : Type}
    (atoms : List (Weighted α)) :
    ∀ events : List (α → Bool),
      eventWeight atoms (unionEvents events) ≤
        (events.map fun event => eventWeight atoms event).sum
  | [] => by
      simp only [unionEvents, List.map_nil, List.sum_nil,
        eventWeight_false]
      exact le_rfl
  | event :: remaining => by
      simp only [unionEvents, List.map_cons, List.sum_cons]
      exact (eventWeight_union_le_add atoms event (unionEvents remaining)).trans
        (add_le_add le_rfl
          (eventWeight_unionEvents_le_sum atoms remaining))

/-- Recursive displayed certificate that each event is disjoint from the
union of all later events on the finite atom list. -/
def MutuallyDisjointOn {α : Type} (atoms : List (Weighted α)) :
    List (α → Bool) → Prop
  | [] => True
  | event :: remaining =>
      DisjointOn atoms event (unionEvents remaining) ∧
        MutuallyDisjointOn atoms remaining

/-- Exact finite additivity for an explicitly disjoint event family. -/
theorem eventWeight_unionEvents_of_disjoint {α : Type}
    (atoms : List (Weighted α)) :
    ∀ {events : List (α → Bool)},
      MutuallyDisjointOn atoms events →
      eventWeight atoms (unionEvents events) =
        (events.map fun event => eventWeight atoms event).sum
  | [], _ => by
      simp only [unionEvents, List.map_nil, List.sum_nil,
        eventWeight_false]
  | event :: remaining, disjoint => by
      simp only [unionEvents, List.map_cons, List.sum_cons]
      rw [eventWeight_union_of_disjoint disjoint.1,
        eventWeight_unionEvents_of_disjoint atoms disjoint.2]

namespace Distribution

/-- Finite probability subadditivity. -/
theorem probability_unionEvents_le_sum {α : Type}
    (distribution : Distribution α) (events : List (α → Bool)) :
    distribution.probability (unionEvents events) ≤
      (events.map distribution.probability).sum :=
  eventWeight_unionEvents_le_sum distribution.atoms events

/-- Exact additivity of an explicitly disjoint finite probability family. -/
theorem probability_unionEvents_of_disjoint {α : Type}
    (distribution : Distribution α) {events : List (α → Bool)}
    (disjoint : MutuallyDisjointOn distribution.atoms events) :
    distribution.probability (unionEvents events) =
      (events.map distribution.probability).sum :=
  eventWeight_unionEvents_of_disjoint distribution.atoms disjoint

end Distribution

namespace FiniteContent

/-- Finite content subadditivity. -/
theorem measure_unionEvents_le_sum {α : Type}
    (content : FiniteContent α) (events : List (α → Bool)) :
    content.measure (unionEvents events) ≤
      (events.map content.measure).sum :=
  eventWeight_unionEvents_le_sum content.atoms events

/-- Exact additivity of an explicitly disjoint finite content family. -/
theorem measure_unionEvents_of_disjoint {α : Type}
    (content : FiniteContent α) {events : List (α → Bool)}
    (disjoint : MutuallyDisjointOn content.atoms events) :
    content.measure (unionEvents events) =
      (events.map content.measure).sum :=
  eventWeight_unionEvents_of_disjoint content.atoms disjoint

end FiniteContent

end FiniteMeasure
