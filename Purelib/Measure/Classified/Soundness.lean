module
import Purelib.Data.List.Membership
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Measure.Weighted.Basic
import Purelib.Measure.Classified.Basic
public import Purelib.Measure.Classified.Split
public import Purelib.Measure.Weighted.Event
import Purelib.Data.Rat.Fraction
import Mathlib.Order.Basic

section
public section

/-!
# Sound finite event classifications

A three-way status table becomes a probability enclosure once its inside and
outside claims are certified against one executable event.  Unresolved rows
need no claim; their exact rational weight is the complete error budget.
-/

namespace Purelib.Measure

open Purelib.Data.Rat

namespace Status

/-- Require inside and outside statuses to agree with the supplied Boolean selection, while unresolved permits either
value. -/
@[expose] def AdmitsSelection (status : Status) (selected : Bool) : Prop :=
  match status with
  | .inside => selected = true
  | .outside => selected = false
  | .unresolved => True

end Status

/-- Attach the supplied payload status to every exact retained weighted occurrence, preserving order and weights. -/
@[expose] def classifiedAtomsWith {α : Type} (atoms : List (Weighted α))
    (status : α → Status) : List (Classified α) :=
  atoms.map fun atom => ⟨atom, status atom.item⟩

/-- Require each retained occurrence's payload status to admit its exact event selection. -/
@[expose] def ClassificationSoundOn {α : Type} (atoms : List (Weighted α))
    (status : α → Status) (event : α → Bool) : Prop :=
  ∀ atom, atom ∈ atoms →
    (status atom.item).AdmitsSelection (event atom.item)

/-- Select payloads whose supplied status is unresolved. -/
@[expose] def unresolvedStatusEvent {α : Type} (status : α → Status) : α → Bool :=
  fun item => decide (status item = .unresolved)

section
open Purelib
/-- The unresolved classified weight equals the original atom-list mass of the unresolved-status event. -/
theorem unresolvedWeight_classifiedAtomsWith {α : Type}
    (status : α → Status) : ∀ atoms : List (Weighted α),
    unresolvedWeight (Measure.classifiedAtomsWith atoms status) =
      eventWeight atoms (Measure.unresolvedStatusEvent status)
  | [] => rfl
  | atom :: remaining => by
      have tail := Purelib.Measure.unresolvedWeight_classifiedAtomsWith status remaining
      have mappedTail :
          unresolvedWeight
              (remaining.map fun candidate =>
                (⟨candidate, status candidate.item⟩ : Classified α)) =
            eventWeight remaining (Measure.unresolvedStatusEvent status) := by
        simpa only [-eq_self, -iff_self, Measure.classifiedAtomsWith] using tail
      cases current : status atom.item <;>
        simp only [-eq_self, -iff_self, Measure.classifiedAtomsWith, List.map_cons,
          unresolvedWeight, eventWeight, Measure.unresolvedStatusEvent, current] <;>
        exact congrArg (fun total : Fraction.Rational => _ + total) mappedTail

/-- A sound classification encloses the original event weight in its exact classified interval.

Every retained occurrence contributes its original nonnegative weight. Inside and outside statuses fix selection;
unresolved occurrences supply the interval's remaining allowance. -/
theorem eventWeight_mem_eventBound_of_classification
    {α : Type} (status : α → Status) (event : α → Bool) :
    ∀ atoms : List (Weighted α),
      Measure.ClassificationSoundOn atoms status event →
      (eventBound (Measure.classifiedAtomsWith atoms status)).Contains
        (eventWeight atoms event)
  | [], _ => ⟨le_rfl, le_rfl⟩
  | atom :: remaining, sound => by
      change lowerWeight (Measure.classifiedAtomsWith (atom :: remaining) status) ≤
          eventWeight (atom :: remaining) event ∧
        eventWeight (atom :: remaining) event ≤
          upperWeight (Measure.classifiedAtomsWith (atom :: remaining) status)
      have head := sound atom List.mem_cons_self
      have tailSound : Measure.ClassificationSoundOn remaining status event :=
        fun candidate member =>
          sound candidate (List.mem_cons_of_mem atom member)
      have tail := Purelib.Measure.eventWeight_mem_eventBound_of_classification
        status event remaining tailSound
      cases current : status atom.item with
      | inside =>
          have selected : event atom.item = true := by
            simpa only [-eq_self, -iff_self, Status.AdmitsSelection, current] using head
          simp only [-eq_self, -iff_self, Measure.classifiedAtomsWith, List.map_cons, lowerWeight,
            upperWeight, eventWeight, current, selected]
          exact ⟨add_le_add le_rfl tail.1, add_le_add le_rfl tail.2⟩
      | outside =>
          have selected : event atom.item = false := by
            simpa only [-eq_self, -iff_self, Status.AdmitsSelection, current] using head
          simp only [-eq_self, -iff_self, Measure.classifiedAtomsWith, List.map_cons, lowerWeight,
            upperWeight, eventWeight, current, selected, zero_add]
          exact tail
      | unresolved =>
          cases selected : event atom.item
          · simp only [-eq_self, -iff_self, Measure.classifiedAtomsWith, List.map_cons, lowerWeight,
              upperWeight, eventWeight, current, selected, zero_add]
            exact ⟨tail.1,
              tail.2.trans (le_add_of_nonneg_left atom.nonnegative)⟩
          · simp only [-eq_self, -iff_self, Measure.classifiedAtomsWith, List.map_cons, lowerWeight,
              upperWeight, eventWeight, current, selected, zero_add]
            exact ⟨tail.1.trans
                (le_add_of_nonneg_left atom.nonnegative),
              add_le_add le_rfl tail.2⟩

end

open Purelib.Data.Rat in
/-- Refining the status of the same weighted occurrence refines its singleton event interval. -/
private theorem singleton_classified_eventBound_refines {α : Type}
    (atom : Weighted α) (inner outer : Status)
    (refines : inner.Refines outer) :
    Interval.Refines (eventBound [⟨atom, inner⟩])
      (eventBound [⟨atom, outer⟩]) := by
  let replacement : Split (⟨atom, outer⟩ : Classified α) :=
    { children := [⟨atom, inner⟩]
      conserved := by
        simp only [-eq_self, -iff_self, classifiedWeight, add_zero]
        rfl
      statuses := by
        intro child member
        have equal := Data.List.Membership.mem_singleton.mp member
        cases equal
        exact refines }
  exact replacement.eventBound_refines

open Purelib in
open Purelib.Data.Rat in
/-- Pointwise status refinement on the exact retained atoms refines their classified event interval. -/
theorem eventBound_classifiedAtomsWith_refines {α : Type}
    (inner outer : α → Status) :
    ∀ atoms : List (Weighted α),
      (∀ atom, atom ∈ atoms →
        (inner atom.item).Refines (outer atom.item)) →
      Interval.Refines
        (eventBound (Measure.classifiedAtomsWith atoms inner))
        (eventBound (Measure.classifiedAtomsWith atoms outer))
  | [], _ => Interval.Refines.refl _
  | atom :: remaining, refines => by
      have head := singleton_classified_eventBound_refines atom
        (inner atom.item) (outer atom.item)
        (refines atom List.mem_cons_self)
      have tail := Purelib.Measure.eventBound_classifiedAtomsWith_refines
        inner outer remaining (fun candidate member =>
          refines candidate (List.mem_cons_of_mem atom member))
      have combined := Interval.Refines.add head tail
      rw [← eventBound_append [⟨atom, inner atom.item⟩]
          (Measure.classifiedAtomsWith remaining inner),
        ← eventBound_append [⟨atom, outer atom.item⟩]
          (Measure.classifiedAtomsWith remaining outer)] at combined
      simpa only [-eq_self, -iff_self, Measure.classifiedAtomsWith, List.map_cons,
        List.singleton_append] using combined

end Purelib.Measure

end
