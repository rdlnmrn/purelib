module
public import Purelib.Measure.Content.Basic
public import Purelib.Measure.Event.Family
import Purelib.Measure.Weighted.AlmostEverywhere
public import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Weighted.Basic
import Purelib.Measure.Distribution.Content
import Purelib.Measure.Weighted.Event
import Purelib.Data.Rat.Fraction

@[expose] public section

/-!
# Finite monotone event chains

For a displayed nonempty increasing event chain, its finite union is exactly
its last event on the supplied atom table.  Dually, the finite intersection
of a decreasing chain is its last event.  These endpoint identities are the
finite content behind continuity from below and above, without a limiting
union or intersection.
-/

namespace Purelib.Measure

section
open Purelib
/-- Require successive events in the retained list to imply the next on every original weighted occurrence. -/
def IncreasingEventChainOn {α : Type} (atoms : List (Measure.Weighted α)) :
    List (α → Bool) → Prop
  | [] => True
  | [_] => True
  | first :: second :: remaining =>
      EventImpliesOn atoms first second ∧
        IncreasingEventChainOn atoms (second :: remaining)

/-- Require successive events in the retained list to imply the previous on every original weighted occurrence. -/
def DecreasingEventChainOn {α : Type} (atoms : List (Measure.Weighted α)) :
    List (α → Bool) → Prop
  | [] => True
  | [_] => True
  | first :: second :: remaining =>
      EventImpliesOn atoms second first ∧
        DecreasingEventChainOn atoms (second :: remaining)

end

/-- Read the last event of a nonempty finite event list supplied as head and tail. -/
def lastEvent {α : Type} (first : α → Bool) :
    List (α → Bool) → α → Bool
  | [] => first
  | next :: remaining => lastEvent next remaining

/-- Intersect a retained first event with every event in its exact finite tail. -/
def intersectionEvents {α : Type} (first : α → Bool) :
    List (α → Bool) → α → Bool
  | [] => first
  | next :: remaining =>
      intersectionEvent first (intersectionEvents next remaining)

section
open Purelib
/-- An increasing nonempty event chain's union equals its last event on every retained occurrence.

Successive implications preserve each selected occurrence through the remaining
events. Structural recursion identifies the finite union with the retained final
event on that same atom, without changing the event list. -/
theorem unionEvents_eq_lastEvent_on_atom {α : Type}
    (atoms : List (Measure.Weighted α)) (first : α → Bool) :
    ∀ (remaining : List (α → Bool)),
      IncreasingEventChainOn atoms (first :: remaining) →
      ∀ atom, atom ∈ atoms →
        unionEvents (first :: remaining) atom.item =
          lastEvent first remaining atom.item
  | [], monotone, atom, member => by
      simp only [unionEvents, unionEvent, Bool.or_false, lastEvent,
        -eq_self, -iff_self]
      rfl
  | second :: remaining, monotone, atom, member => by
      have tailEqual := unionEvents_eq_lastEvent_on_atom atoms second
        remaining monotone.2 atom member
      cases firstSelected : first atom.item
      · simp only [unionEvents, unionEvent, firstSelected, Bool.false_or,
          lastEvent, -eq_self, -iff_self]
        exact tailEqual
      · have secondSelected : second atom.item = true :=
          monotone.1 atom member firstSelected
        have tailSelected : unionEvents (second :: remaining) atom.item =
            true := by
          simp only [unionEvents, unionEvent, secondSelected, Bool.true_or,
            -eq_self, -iff_self]
          rfl
        have lastSelected : lastEvent second remaining atom.item = true := by
          rw [← tailEqual]
          exact tailSelected
        simp only [unionEvents, unionEvent, firstSelected, Bool.true_or,
          lastEvent, lastSelected, -eq_self, -iff_self]
        rfl

/-- A decreasing nonempty event chain's intersection equals its last event on every retained occurrence.

Successive reverse implications show that any occurrence excluded by the first
event is excluded throughout the tail. The finite intersection therefore agrees
with the retained final event on every original atom. -/
theorem intersectionEvents_eq_lastEvent_on_atom {α : Type}
    (atoms : List (Measure.Weighted α)) (first : α → Bool) :
    ∀ (remaining : List (α → Bool)),
      DecreasingEventChainOn atoms (first :: remaining) →
      ∀ atom, atom ∈ atoms →
        intersectionEvents first remaining atom.item =
          lastEvent first remaining atom.item
  | [], monotone, atom, member => rfl
  | second :: remaining, monotone, atom, member => by
      have tailEqual := intersectionEvents_eq_lastEvent_on_atom atoms second
        remaining monotone.2 atom member
      cases firstSelected : first atom.item
      · have secondSelected : second atom.item = false := by
          cases selected : second atom.item
          · rfl
          · have firstTrue := monotone.1 atom member selected
            rw [firstSelected] at firstTrue
            exact Bool.noConfusion firstTrue
        have tailSelected : intersectionEvents second remaining atom.item =
            false := by
          cases remaining with
          | nil => exact secondSelected
          | cons third rest =>
              simp only [intersectionEvents, intersectionEvent,
                secondSelected, Bool.false_and, -eq_self, -iff_self]
              rfl
        have lastSelected : lastEvent second remaining atom.item = false := by
          rw [← tailEqual]
          exact tailSelected
        simp only [intersectionEvents, intersectionEvent, firstSelected,
          Bool.false_and, lastEvent, lastSelected, -eq_self, -iff_self]
        rfl
      · simp only [intersectionEvents, intersectionEvent, firstSelected,
          Bool.true_and, lastEvent, -eq_self, -iff_self]
        exact tailEqual

end

namespace Content

/-- An increasing finite event chain's union has the same content as its exact last event. -/
theorem measure_unionEvents_eq_last_of_increasing {α : Type}
    (content : Content α) (first : α → Bool)
    (remaining : List (α → Bool))
    (monotone : IncreasingEventChainOn content.atoms (first :: remaining)) :
    content.measure (unionEvents (first :: remaining)) =
      content.measure (lastEvent first remaining) := by
  apply eventWeight_congr_off_zero
  intro atom member
  exact Or.inr
    (unionEvents_eq_lastEvent_on_atom content.atoms first remaining
      monotone atom member)

/-- A decreasing finite event chain's intersection has the same content as its exact last event. -/
theorem measure_intersectionEvents_eq_last_of_decreasing {α : Type}
    (content : Content α) (first : α → Bool)
    (remaining : List (α → Bool))
    (monotone : DecreasingEventChainOn content.atoms (first :: remaining)) :
    content.measure (intersectionEvents first remaining) =
      content.measure (lastEvent first remaining) := by
  apply eventWeight_congr_off_zero
  intro atom member
  exact Or.inr
    (intersectionEvents_eq_lastEvent_on_atom content.atoms first remaining
      monotone atom member)

end Content

namespace Distribution

/-- An increasing finite event chain's union has the same probability as its exact last event. -/
theorem probability_unionEvents_eq_last_of_increasing {α : Type}
    (distribution : Distribution α) (first : α → Bool)
    (remaining : List (α → Bool))
    (monotone : IncreasingEventChainOn distribution.atoms
      (first :: remaining)) :
    distribution.probability (unionEvents (first :: remaining)) =
      distribution.probability (lastEvent first remaining) :=
  distribution.toContent.measure_unionEvents_eq_last_of_increasing
    first remaining monotone

/-- A decreasing finite event chain's intersection has the same probability as its exact last event. -/
theorem probability_intersectionEvents_eq_last_of_decreasing {α : Type}
    (distribution : Distribution α) (first : α → Bool)
    (remaining : List (α → Bool))
    (monotone : DecreasingEventChainOn distribution.atoms
      (first :: remaining)) :
    distribution.probability (intersectionEvents first remaining) =
      distribution.probability (lastEvent first remaining) :=
  distribution.toContent.measure_intersectionEvents_eq_last_of_decreasing
    first remaining monotone

end Distribution

end Purelib.Measure
