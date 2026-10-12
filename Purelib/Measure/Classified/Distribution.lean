module
import Purelib.Data.Rat.Interval.Basic
public import Purelib.Measure.Classified.Soundness
import Purelib.Measure.Classified.Basic
public import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Weighted.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Measure.Classified.Split

section
@[expose] public section

/-!
# Sound finite event classifications

A three-way status table becomes a probability enclosure once its inside and
outside claims are certified against one executable event.  Unresolved rows
need no claim; their exact rational weight is the complete error budget.
-/

namespace Purelib.Measure

namespace Distribution

open Purelib in
/-- Attach the supplied statuses to the original distribution's exact weighted occurrences. -/
def classifiedEventFrontier {α : Type} (distribution : Distribution α)
    (status : α → Status) : List (Classified α) :=
  Measure.classifiedAtomsWith distribution.atoms status

open Purelib in
open Purelib.Data.Rat in
/-- Status refinement on the retained distribution atoms refines the exact classified frontier interval. -/
theorem classifiedEventFrontier_refines {α : Type}
    (distribution : Distribution α) (inner outer : α → Status)
    (refines : ∀ atom, atom ∈ distribution.atoms →
      (inner atom.item).Refines (outer atom.item)) :
    Interval.Refines
      (eventBound (distribution.classifiedEventFrontier inner))
      (eventBound (distribution.classifiedEventFrontier outer)) :=
  Measure.eventBound_classifiedAtomsWith_refines
    inner outer distribution.atoms refines

open Purelib
/-- The classified frontier interval's width equals the probability of unresolved status under the original
distribution. -/
theorem classifiedEventFrontier_width {α : Type}
    (distribution : Distribution α) (status : α → Status) :
    (eventBound (distribution.classifiedEventFrontier status)).width =
      distribution.probability (unresolvedStatusEvent status) := by
  rw [Measure.eventBound_width]
  exact unresolvedWeight_classifiedAtomsWith status distribution.atoms

/-- Sound classification of the exact retained distribution encloses its event probability in the classified interval.
-/
theorem probability_mem_classifiedEventFrontier
    {α : Type} (distribution : Distribution α)
    (status : α → Status) (event : α → Bool)
    (sound : ClassificationSoundOn distribution.atoms status event) :
    (eventBound (distribution.classifiedEventFrontier status)).Contains
      (distribution.probability event) :=
  Measure.eventWeight_mem_eventBound_of_classification
    status event distribution.atoms sound

end Distribution

end Purelib.Measure

end

section
@[expose] public section

/-!
# Finite rational probability

A probability distribution is a displayed finite weighted list whose total is
exactly one.  Events are executable Boolean tests, so their probabilities and
expectations are exact rational calculations.
-/

namespace Purelib.Measure
namespace Distribution

/-- Classify each retained weighted occurrence exactly inside or outside according to the supplied Boolean event. -/
def classifyEvent {α : Type} :
    List (Weighted α) → (α → Bool) → List (Classified α)
  | [], _ => []
  | atom :: remaining, event =>
      { atom := atom
        status := match event atom.item with
          | true => .inside
          | false => .outside } :: Purelib.Measure.Distribution.classifyEvent remaining event

section
open Purelib.Measure
/-- Compute the exact inside-outside event classification of the original distribution's retained atoms. -/
def eventFrontier {α : Type} (distribution : Distribution α)
    (event : α → Bool) : List (Classified α) :=
  Distribution.classifyEvent distribution.atoms event

/-- Exact Boolean event classification leaves zero unresolved weight. -/
theorem eventFrontier_unresolved_zero {α : Type}
    (distribution : Distribution α) (event : α → Bool) :
    unresolvedWeight (distribution.eventFrontier event) = 0 := by
  unfold Distribution.eventFrontier
  induction distribution.atoms with
  | nil => rfl
  | cons atom remaining inductionHypothesis =>
      cases choice : event atom.item <;>
        simp only [-eq_self, -iff_self, Distribution.classifyEvent, choice, unresolvedWeight, zero_add,
          inductionHypothesis] <;> rfl

end

open Purelib in
/-- The exact event classification frontier has interval width zero. -/
theorem eventFrontier_bound_exact {α : Type}
    (distribution : Distribution α) (event : α → Bool) :
    (eventBound (distribution.eventFrontier event)).width = 0 := by
  rw [Measure.eventBound_width, distribution.eventFrontier_unresolved_zero]

end Distribution

end Purelib.Measure

end
