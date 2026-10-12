module
import Purelib.Data.List.Append
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Interval.Basic
public import Purelib.Measure.Classified.Basic
import Purelib.Measure.Weighted.Basic

/-!
# Finite rational contents and event bounds

Weights are attached only to a displayed finite list.  Event measurement is
a three-way finite classification: inside, outside, or unresolved.  The
unresolved weight is exactly the width of the returned rational enclosure.
-/

@[expose] public section

namespace Purelib.Measure

/-! ## Certified finite refinement -/

/-- Require a refined status to preserve an already inside or outside decision; an unresolved parent admits any status.
-/
def Status.Refines (child parent : Status) : Prop :=
  match parent with
  | .inside => child = .inside
  | .outside => child = .outside
  | .unresolved => True

set_option genInjectivity false in
/-- Retain finite classified children of one exact parent, with conservation of its weight and refinement of its status.

The child payload type may differ from the parent's. Conservation and status refinement bind the exact child list to the
original classified occurrence. -/
structure Split {α β : Type} (parent : Classified α) where
  /-- The exact ordered classified child list replacing this parent. -/ children : List (Classified β)
  /-- The total child weight equals the exact original parent's weight. -/ conserved : classifiedWeight children =
    parent.atom.weight
  /-- Each retained child status refines the original parent status. -/ statuses : ∀ child, child ∈ children →
    child.status.Refines parent.status

constructive_injectivity Split

/-- If every retained occurrence is inside, its lower weight equals total classified weight. -/
private theorem lowerWeight_eq_classifiedWeight_of_inside {α : Type} :
    ∀ {entries : List (Classified α)},
      (∀ entry, entry ∈ entries → entry.status = .inside) →
      lowerWeight entries = classifiedWeight entries
  | [], _ => rfl
  | entry :: remaining, all => by
      have head := all entry List.mem_cons_self
      have tail : ∀ child, child ∈ remaining → child.status = .inside :=
        fun child member => all child (List.mem_cons_of_mem entry member)
      rcases entry with ⟨atom, status⟩
      cases status <;> try contradiction
      dsimp only [lowerWeight, classifiedWeight]
      rw [lowerWeight_eq_classifiedWeight_of_inside tail]

/-- If every retained occurrence is inside, its upper weight equals total classified weight. -/
private theorem upperWeight_eq_classifiedWeight_of_inside {α : Type} :
    ∀ {entries : List (Classified α)},
      (∀ entry, entry ∈ entries → entry.status = .inside) →
      upperWeight entries = classifiedWeight entries
  | [], _ => rfl
  | entry :: remaining, all => by
      have head := all entry List.mem_cons_self
      have tail : ∀ child, child ∈ remaining → child.status = .inside :=
        fun child member => all child (List.mem_cons_of_mem entry member)
      rcases entry with ⟨atom, status⟩
      cases status <;> try contradiction
      dsimp only [upperWeight, classifiedWeight]
      rw [upperWeight_eq_classifiedWeight_of_inside tail]

/-- If every retained occurrence is outside, its lower weight vanishes. -/
private theorem lowerWeight_eq_zero_of_outside {α : Type} :
    ∀ {entries : List (Classified α)},
      (∀ entry, entry ∈ entries → entry.status = .outside) →
      lowerWeight entries = 0
  | [], _ => rfl
  | entry :: remaining, all => by
      have head := all entry List.mem_cons_self
      have tail : ∀ child, child ∈ remaining → child.status = .outside :=
        fun child member => all child (List.mem_cons_of_mem entry member)
      rcases entry with ⟨atom, status⟩
      cases status <;> try contradiction
      dsimp only [lowerWeight]
      simpa only [zero_add] using lowerWeight_eq_zero_of_outside tail

/-- If every retained occurrence is outside, its upper weight vanishes. -/
private theorem upperWeight_eq_zero_of_outside {α : Type} :
    ∀ {entries : List (Classified α)},
      (∀ entry, entry ∈ entries → entry.status = .outside) →
      upperWeight entries = 0
  | [], _ => rfl
  | entry :: remaining, all => by
      have head := all entry List.mem_cons_self
      have tail : ∀ child, child ∈ remaining → child.status = .outside :=
        fun child member => all child (List.mem_cons_of_mem entry member)
      rcases entry with ⟨atom, status⟩
      cases status <;> try contradiction
      dsimp only [upperWeight]
      simpa only [zero_add] using upperWeight_eq_zero_of_outside tail

open Purelib.Data.Rat
/-- A mass-conserving classified split refines its original parent's event interval. -/
theorem Split.eventBound_refines {α β : Type} {parent : Classified α}
    (split : Split (β := β) parent) :
    Interval.Refines (eventBound split.children) (eventBound [parent]) := by
  rcases parent with ⟨atom, parentStatus⟩
  cases parentStatus with
  | inside =>
      have allInside : ∀ child, child ∈ split.children →
          child.status = .inside := by
        intro child member
        exact split.statuses child member
      have lower := lowerWeight_eq_classifiedWeight_of_inside allInside
      have upper := upperWeight_eq_classifiedWeight_of_inside allInside
      constructor
      · simpa only [eventBound, lowerWeight, split.conserved, add_zero] using
          le_of_eq lower.symm
      · simpa only [eventBound, upperWeight, split.conserved, add_zero] using
          le_of_eq upper
  | outside =>
      have allOutside : ∀ child, child ∈ split.children →
          child.status = .outside := by
        intro child member
        exact split.statuses child member
      have lower := lowerWeight_eq_zero_of_outside allOutside
      have upper := upperWeight_eq_zero_of_outside allOutside
      constructor
      · simpa only [eventBound, lowerWeight, lower, add_zero] using
          (le_rfl : (0 : Fraction.Rational) ≤ 0)
      · simpa only [eventBound, upperWeight, upper, add_zero] using
          (le_rfl : (0 : Fraction.Rational) ≤ 0)
  | unresolved =>
      constructor
      · simpa only [eventBound, lowerWeight, add_zero] using
          lowerWeight_nonneg split.children
      · simpa only [eventBound, upperWeight, split.conserved, add_zero] using
          upperWeight_le_classifiedWeight split.children

/-- Replacing one retained frontier occurrence by its certified children refines the whole frontier event interval. -/
theorem Split.frontier_eventBound_refines
    {α : Type} {parent : Classified α}
    (split : Split (β := α) parent)
    (before after : List (Classified α)) :
    Interval.Refines
      (eventBound (before ++ split.children ++ after))
      (eventBound (before ++ [parent] ++ after)) := by
  have middle := split.eventBound_refines
  have withAfter := Interval.Refines.add middle
    (Interval.Refines.refl (eventBound after))
  have complete := Interval.Refines.add
    (Interval.Refines.refl (eventBound before)) withAfter
  rw [Data.List.Append.append_assoc, Data.List.Append.append_assoc]
  rw [eventBound_append before (split.children ++ after),
    eventBound_append split.children after,
    eventBound_append before ([parent] ++ after),
    eventBound_append [parent] after]
  exact complete

end Purelib.Measure

end
