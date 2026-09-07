import FiniteMeasure.Family
import FiniteMeasure.ZeroWeight

/-!
# Finite monotone event chains

For a displayed nonempty increasing event chain, its finite union is exactly
its last event on the supplied atom table.  Dually, the finite intersection
of a decreasing chain is its last event.  These endpoint identities are the
finite content behind continuity from below and above, without a limiting
union or intersection.
-/

namespace FiniteMeasure

/-- Adjacent inclusion for a displayed finite event chain. -/
def IncreasingEventChainOn {α : Type} (atoms : List (Weighted α)) :
    List (α → Bool) → Prop
  | [] => True
  | [_] => True
  | first :: second :: remaining =>
      EventImpliesOn atoms first second ∧
        IncreasingEventChainOn atoms (second :: remaining)

/-- Adjacent reverse inclusion for a displayed finite event chain. -/
def DecreasingEventChainOn {α : Type} (atoms : List (Weighted α)) :
    List (α → Bool) → Prop
  | [] => True
  | [_] => True
  | first :: second :: remaining =>
      EventImpliesOn atoms second first ∧
        DecreasingEventChainOn atoms (second :: remaining)

/-- Last event of a nonempty displayed family. -/
def lastEvent {α : Type} (first : α → Bool) :
    List (α → Bool) → α → Bool
  | [] => first
  | next :: remaining => lastEvent next remaining

/-- Pointwise intersection of a nonempty displayed event family. -/
def intersectionEvents {α : Type} (first : α → Bool) :
    List (α → Bool) → α → Bool
  | [] => first
  | next :: remaining =>
      intersectionEvent first (intersectionEvents next remaining)

/-- A finite increasing union agrees with its last event on every supplied
atom. -/
theorem unionEvents_eq_lastEvent_on_atom {α : Type}
    (atoms : List (Weighted α)) (first : α → Bool) :
    ∀ (remaining : List (α → Bool)),
      IncreasingEventChainOn atoms (first :: remaining) →
      ∀ atom, atom ∈ atoms →
        unionEvents (first :: remaining) atom.item =
          lastEvent first remaining atom.item
  | [], monotone, atom, member => by
      simp only [unionEvents, unionEvent, Bool.or_false, lastEvent]
  | second :: remaining, monotone, atom, member => by
      have tailEqual := unionEvents_eq_lastEvent_on_atom atoms second
        remaining monotone.2 atom member
      cases firstSelected : first atom.item
      · simp only [unionEvents, unionEvent, firstSelected, Bool.false_or,
          lastEvent]
        exact tailEqual
      · have secondSelected : second atom.item = true :=
          monotone.1 atom member firstSelected
        have tailSelected : unionEvents (second :: remaining) atom.item =
            true := by
          simp only [unionEvents, unionEvent, secondSelected, Bool.true_or]
        have lastSelected : lastEvent second remaining atom.item = true := by
          rw [← tailEqual]
          exact tailSelected
        simp only [unionEvents, unionEvent, firstSelected, Bool.true_or,
          lastEvent, lastSelected]

/-- A finite decreasing intersection agrees with its last event on every
supplied atom. -/
theorem intersectionEvents_eq_lastEvent_on_atom {α : Type}
    (atoms : List (Weighted α)) (first : α → Bool) :
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
                secondSelected, Bool.false_and]
        have lastSelected : lastEvent second remaining atom.item = false := by
          rw [← tailEqual]
          exact tailSelected
        simp only [intersectionEvents, intersectionEvent, firstSelected,
          Bool.false_and, lastEvent, lastSelected]
      · simp only [intersectionEvents, intersectionEvent, firstSelected,
          Bool.true_and, lastEvent]
        exact tailEqual

namespace FiniteContent

/-- Finite continuity from below: the union of a displayed nonempty
increasing chain has exactly the content of its final event. -/
theorem measure_unionEvents_eq_last_of_increasing {α : Type}
    (content : FiniteContent α) (first : α → Bool)
    (remaining : List (α → Bool))
    (monotone : IncreasingEventChainOn content.atoms (first :: remaining)) :
    content.measure (unionEvents (first :: remaining)) =
      content.measure (lastEvent first remaining) := by
  apply eventWeight_congr_off_zero
  intro atom member
  exact Or.inr
    (unionEvents_eq_lastEvent_on_atom content.atoms first remaining
      monotone atom member)

/-- Finite continuity from above: the intersection of a displayed nonempty
decreasing chain has exactly the content of its final event. -/
theorem measure_intersectionEvents_eq_last_of_decreasing {α : Type}
    (content : FiniteContent α) (first : α → Bool)
    (remaining : List (α → Bool))
    (monotone : DecreasingEventChainOn content.atoms (first :: remaining)) :
    content.measure (intersectionEvents first remaining) =
      content.measure (lastEvent first remaining) := by
  apply eventWeight_congr_off_zero
  intro atom member
  exact Or.inr
    (intersectionEvents_eq_lastEvent_on_atom content.atoms first remaining
      monotone atom member)

end FiniteContent

namespace Distribution

theorem probability_unionEvents_eq_last_of_increasing {α : Type}
    (distribution : Distribution α) (first : α → Bool)
    (remaining : List (α → Bool))
    (monotone : IncreasingEventChainOn distribution.atoms
      (first :: remaining)) :
    distribution.probability (unionEvents (first :: remaining)) =
      distribution.probability (lastEvent first remaining) :=
  distribution.toFiniteContent.measure_unionEvents_eq_last_of_increasing
    first remaining monotone

theorem probability_intersectionEvents_eq_last_of_decreasing {α : Type}
    (distribution : Distribution α) (first : α → Bool)
    (remaining : List (α → Bool))
    (monotone : DecreasingEventChainOn distribution.atoms
      (first :: remaining)) :
    distribution.probability (intersectionEvents first remaining) =
      distribution.probability (lastEvent first remaining) :=
  distribution.toFiniteContent.measure_intersectionEvents_eq_last_of_decreasing
    first remaining monotone

end Distribution

end FiniteMeasure
