module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Measure.Distribution.AlmostEverywhere
public import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.EventFamily
import Purelib.Measure.Distribution.Kernel.Basic
public import Purelib.Measure.Event.Family
import Purelib.Measure.Weighted.Basic
import Purelib.Measure.Weighted.Event
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction

section
@[expose] public section

/-!
# Finite rational conditioning and partitions

Conditioning is executable reweighting of a displayed finite distribution by
an indicator divided by an explicitly positive rational probability.  Finite
partitions carry direct coverage and disjointness certificates.
-/

namespace Purelib.Measure

set_option genInjectivity false in
/-- Retain a finite event list disjoint on and covering the exact original distribution occurrences.

Disjointness and coverage are certified on the retained atom list, including its zero-weight occurrences; the event list
keeps its original order. -/
structure EventPartition {α : Type} (distribution : Distribution α) where
  /-- The exact ordered finite partition event list. -/ events : List (α → Bool)
  /-- The retained events are mutually disjoint on the original distribution atoms. -/ disjoint : MutuallyDisjointOn
    distribution.atoms events
  /-- Their union selects every retained original distribution occurrence. -/ covers : ∀ atom, atom ∈ distribution.atoms
    →
    unionEvents events atom.item = true

constructive_injectivity EventPartition

namespace EventPartition

/-- Intersect every event in the exact retained list with the same supplied event. -/
def intersectEvents {α : Type} (event : α → Bool) :
    List (α → Bool) → List (α → Bool)
  | [] => []
  | member :: remaining =>
      intersectionEvent event member :: intersectEvents event remaining

/-- Union of the pointwise-intersected event list is intersection with the original union. -/
theorem unionEvents_intersectEvents {α : Type}
    (event : α → Bool) : ∀ (events : List (α → Bool)) (item : α),
    unionEvents (intersectEvents event events) item =
      intersectionEvent event (unionEvents events) item
  | [], item => by
      simp only [-eq_self, -iff_self, intersectEvents, unionEvents, intersectionEvent,
        Bool.and_false]
      rfl
  | member :: remaining, item => by
      cases eventSelected : event item <;>
        cases memberSelected : member item <;>
        (simp only [-eq_self, -iff_self, intersectEvents, unionEvents, unionEvent,
          intersectionEvent,
          unionEvents_intersectEvents event remaining item, eventSelected,
          memberSelected, Bool.false_and, Bool.true_and,
          Bool.false_or, Bool.true_or]
         rfl)

/-- Intersecting each event with the same condition preserves disjointness on the retained atoms. -/
theorem mutuallyDisjointOn_intersectEvents {α : Type}
    (atoms : List (Weighted α)) (event : α → Bool) :
    ∀ {events : List (α → Bool)},
      MutuallyDisjointOn atoms events →
        MutuallyDisjointOn atoms (intersectEvents event events)
  | [], disjoint => trivial
  | member :: remaining, disjoint => by
      constructor
      · intro atom atomMember selected
        apply disjoint.1 atom atomMember
        have memberSelected : member atom.item = true := by
          cases eventSelected : event atom.item
          · have impossible : false = true := by
              simpa only [-eq_self, -iff_self, intersectionEvent, eventSelected,
                Bool.false_and] using selected.1
            exact Bool.noConfusion impossible
          · simpa only [-eq_self, -iff_self, intersectionEvent, eventSelected,
              Bool.true_and] using selected.1
        have remainingSelected : unionEvents remaining atom.item = true := by
          have mappedSelected := selected.2
          rw [unionEvents_intersectEvents event remaining atom.item]
            at mappedSelected
          cases eventSelected : event atom.item
          · have impossible : false = true := by
              simpa only [-eq_self, -iff_self, intersectionEvent, eventSelected,
                Bool.false_and] using mappedSelected
            exact Bool.noConfusion impossible
          · simpa only [-eq_self, -iff_self, intersectionEvent, eventSelected,
              Bool.true_and] using mappedSelected
        exact ⟨memberSelected, remainingSelected⟩
      · exact mutuallyDisjointOn_intersectEvents atoms event disjoint.2

open Purelib.Data.Rat in
/-- The union of the retained partition events has probability one in its original distribution. -/
theorem probability_union {α : Type} {distribution : Distribution α}
    (partition : EventPartition distribution) :
    distribution.probability (unionEvents partition.events) = 1 := by
  apply Fraction.Order.Basic.Compatibility.le_antisymm
  · exact distribution.probability_le_one _
  · rw [← distribution.probability_true]
    apply eventWeight_mono
    intro atom member selected
    exact partition.covers atom member

/-- The probabilities of the exact retained partition events sum to one. -/
theorem probabilities_sum_one {α : Type}
    {distribution : Distribution α}
    (partition : EventPartition distribution) :
    (partition.events.map distribution.probability).sum = 1 := by
  rw [← distribution.probability_unionEvents_of_disjoint partition.disjoint]
  exact partition.probability_union

/-- Summing probabilities of intersections with the retained partition recovers the original event probability. -/
theorem total_probability {α : Type}
    {distribution : Distribution α}
    (partition : EventPartition distribution) (event : α → Bool) :
    ((intersectEvents event partition.events).map
      distribution.probability).sum = distribution.probability event := by
  rw [← distribution.probability_unionEvents_of_disjoint
    (mutuallyDisjointOn_intersectEvents distribution.atoms event
      partition.disjoint)]
  apply distribution.probability_congr_off_zero
  intro atom member
  apply Or.inr
  rw [unionEvents_intersectEvents]
  unfold intersectionEvent
  rw [partition.covers atom member]
  cases selected : event atom.item <;> rfl

end EventPartition

end Purelib.Measure

end
