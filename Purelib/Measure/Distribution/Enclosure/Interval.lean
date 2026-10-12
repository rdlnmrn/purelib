module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Interval.Basic
import Purelib.Measure.Classified.Basic
import Purelib.Measure.Distribution.Basic
public import Purelib.Measure.Classified.Interval
import Purelib.Measure.Classified.Soundness
import Purelib.Measure.Content.Density.Aligned
public import Purelib.Measure.Classified.Distribution
public import Purelib.Measure.Event.RationalOrder
import Purelib.Measure.Content.Basic
import Purelib.Data.List.Event
import Purelib.Measure.Classified.Split
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Measure.Weighted.Basic
import Mathlib.Order.Basic

section
@[expose] public section

/-!
# Finite probability of rational-interval membership

A rational enclosure for each displayed atom can certify that its value is
inside a target rational interval, outside it, or still unresolved.  The
resulting finite lower/upper sums enclose the exact probability for every
explicit rational observable admitted by those enclosures.  Narrower source
enclosures can only narrow the probability enclosure.
-/

namespace Purelib.Measure

section
open Purelib
/-- Classify each exact original distribution occurrence by containment or separation of its retained range from the
target interval. -/
def Distribution.withinBoundFrontier {α : Type}
    (distribution : Measure.Distribution α) (ranges : α → Data.Rat.Interval)
    (target : Data.Rat.Interval) : List (Classified α) :=
  distribution.classifiedEventFrontier fun item =>
    withinBoundStatus (ranges item) target

/-- The exact classified interval-bound width equals original probability of unresolved range classification. -/
theorem Distribution.withinBoundFrontier_width {α : Type}
    (distribution : Measure.Distribution α) (ranges : α → Data.Rat.Interval)
    (target : Data.Rat.Interval) :
    (eventBound (distribution.withinBoundFrontier ranges target)).width =
      distribution.probability (withinBoundUnresolvedEvent ranges target) :=
  distribution.classifiedEventFrontier_width _

end

section
open Purelib
open Purelib.Data.Rat
/-- Retained range containment makes interval classification sound for the exact observable's target-membership event.
-/
theorem Distribution.withinBoundClassification_sound
    {α : Type} (distribution : Measure.Distribution α) (ranges : α → Data.Rat.Interval)
    (target : Data.Rat.Interval) (value : α → Fraction.Rational)
    (inside : ∀ atom, atom ∈ distribution.atoms →
      (ranges atom.item).Contains (value atom.item)) :
    ClassificationSoundOn distribution.atoms
      (fun item => withinBoundStatus (ranges item) target)
      (withinBoundEvent target value) := by
  intro atom member
  have admitted := inside atom member
  simp only [Status.AdmitsSelection, -eq_self, -iff_self]
  by_cases whollyInside :
      target.lower ≤ (ranges atom.item).lower ∧
        (ranges atom.item).upper ≤ target.upper
  · simp only [-eq_self, -iff_self, withinBoundStatus, if_pos whollyInside,
      withinBoundEvent]
    apply decide_eq_true
    exact ⟨whollyInside.1.trans admitted.1,
      admitted.2.trans whollyInside.2⟩
  · by_cases separated :
        (ranges atom.item).upper < target.lower ∨
          target.upper < (ranges atom.item).lower
    · simp only [-eq_self, -iff_self, withinBoundStatus, if_neg whollyInside,
        if_pos separated, withinBoundEvent]
      apply decide_eq_false
      intro selected
      rcases separated with left | right
      · exact left.2 (selected.1.trans admitted.2)
      · exact right.2 (admitted.1.trans selected.2)
    · simp only [-eq_self, -iff_self, withinBoundStatus, if_neg whollyInside,
        if_neg separated]

/-- The classified frontier's event bound contains the original probability that the admitted observable lies in the
target interval. -/
theorem Distribution.probability_mem_withinBoundFrontier
    {α : Type} (distribution : Measure.Distribution α) (ranges : α → Data.Rat.Interval)
    (target : Data.Rat.Interval) (value : α → Fraction.Rational)
    (inside : ∀ atom, atom ∈ distribution.atoms →
      (ranges atom.item).Contains (value atom.item)) :
    (eventBound (distribution.withinBoundFrontier ranges target)).Contains
      (distribution.probability (withinBoundEvent target value)) :=
  distribution.probability_mem_classifiedEventFrontier
    (fun item => withinBoundStatus (ranges item) target)
    (withinBoundEvent target value)
    (distribution.withinBoundClassification_sound ranges target value inside)

end

open Purelib in
open Purelib.Data.Rat in
open Purelib.Measure in
/-- Occurrence-wise narrowing of original ranges refines their target-membership probability interval. -/
theorem Distribution.withinBoundFrontier_eventBound_refines
    {α : Type} (distribution : Measure.Distribution α)
    (inner outer : α → Data.Rat.Interval) (target : Data.Rat.Interval)
    (refines : ∀ atom, atom ∈ distribution.atoms →
      Interval.Refines (inner atom.item) (outer atom.item)) :
    Interval.Refines
      (eventBound (distribution.withinBoundFrontier inner target))
      (eventBound (distribution.withinBoundFrontier outer target)) := by
  unfold Distribution.withinBoundFrontier
  exact distribution.classifiedEventFrontier_refines
    (fun item => withinBoundStatus (inner item) target)
    (fun item => withinBoundStatus (outer item) target)
    (fun atom member => withinBoundStatus_refines (refines atom member))

open Purelib in
open Purelib.Measure in
/-- Resolving every retained range against the target makes the exact probability interval have zero width. -/
theorem Distribution.withinBoundFrontier_width_eq_zero_of_resolved
    {α : Type} (distribution : Measure.Distribution α)
    (ranges : α → Data.Rat.Interval) (target : Data.Rat.Interval)
    (resolved : ∀ atom, atom ∈ distribution.atoms →
      WithinBoundResolved (ranges atom.item) target) :
    (eventBound
      (distribution.withinBoundFrontier ranges target)).width = 0 := by
  rw [Measure.eventBound_width]
  unfold Distribution.withinBoundFrontier classifiedEventFrontier classifiedAtomsWith
  exact Measure.unresolvedWeight_withinBoundFrontier_eq_zero
    ranges target distribution.atoms resolved

open Purelib in
open Purelib.Data.Rat in
/-- A strict budget on original unresolved-classification probability gives the same strict event-bound width budget. -/
theorem Distribution.withinBoundFrontier_width_lt_of_unresolved_budget
    {α : Type} (distribution : Measure.Distribution α)
    (ranges : α → Data.Rat.Interval) (target : Data.Rat.Interval) (epsilon : Fraction.Rational)
    (budget : distribution.probability
      (withinBoundUnresolvedEvent ranges target) < epsilon) :
    (eventBound
      (distribution.withinBoundFrontier ranges target)).width < epsilon := by
  rw [distribution.withinBoundFrontier_width]
  exact budget

end Purelib.Measure

end
