module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Measure.Classified.Basic
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Weighted.Event
public import Purelib.Measure.Event.RationalOrder
import Purelib.Measure.Classified.Soundness
public import Purelib.Measure.Classified.Threshold
public import Purelib.Measure.Classified.Distribution
import Purelib.Measure.Weighted.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic

section
@[expose] public section

/-!
# Threshold events from finite rational enclosures

Pointwise rational enclosures can decide some threshold comparisons and leave
the rest explicitly unresolved.  The resulting lower and upper probability
sums contain the exact threshold probability of every rational observable
admitted by the displayed enclosures.  Refining the enclosures narrows the
probability bound.
-/

namespace Purelib.Measure

section
open Purelib
open Purelib.Data.Rat
/-- Classify each original weighted atom using its exact retained interval and the supplied threshold. -/
def Distribution.thresholdFrontier {α : Type}
    (distribution : Distribution α) (ranges : α → Data.Rat.Interval)
    (threshold : Fraction.Rational) : List (Classified α) :=
  distribution.classifiedEventFrontier fun item =>
    thresholdStatus (ranges item) threshold

/-- An observable admitted by every original range has threshold-event selections allowed by the exact range
classifications. -/
theorem Distribution.thresholdClassification_sound
    {α : Type} (distribution : Distribution α) (ranges : α → Data.Rat.Interval)
    (threshold : Fraction.Rational) (value : α → Fraction.Rational)
    (inside : ∀ atom, atom ∈ distribution.atoms →
      (ranges atom.item).Contains (value atom.item)) :
    ClassificationSoundOn distribution.atoms
      (fun item => thresholdStatus (ranges item) threshold)
      (atLeastEvent threshold value) := by
  intro atom member
  have admitted := inside atom member
  by_cases definitelyInside : threshold ≤ (ranges atom.item).lower
  · simp only [thresholdStatus, -eq_self, -iff_self]
    rewrite [if_pos definitelyInside]
    change decide (threshold ≤ value atom.item) = true
    exact decide_eq_true (definitelyInside.trans admitted.1)
  · by_cases definitelyOutside : (ranges atom.item).upper < threshold
    · simp only [thresholdStatus, -eq_self, -iff_self]
      rewrite [if_neg definitelyInside, if_pos definitelyOutside]
      change decide (threshold ≤ value atom.item) = false
      apply decide_eq_false
      intro selected
      exact definitelyOutside.2 (selected.trans admitted.2)
    · simp only [thresholdStatus, -eq_self, -iff_self]
      rewrite [if_neg definitelyInside, if_neg definitelyOutside]
      exact True.intro

/-- The exact classified frontier interval contains the original threshold-event probability of any admitted observable.
-/
theorem Distribution.probability_mem_thresholdFrontier
    {α : Type} (distribution : Distribution α) (ranges : α → Data.Rat.Interval)
    (threshold : Fraction.Rational) (value : α → Fraction.Rational)
    (inside : ∀ atom, atom ∈ distribution.atoms →
      (ranges atom.item).Contains (value atom.item)) :
    (eventBound (distribution.thresholdFrontier ranges threshold)).Contains
      (distribution.probability (atLeastEvent threshold value)) := by
  exact distribution.probability_mem_classifiedEventFrontier
    (fun item => thresholdStatus (ranges item) threshold)
    (atLeastEvent threshold value)
    (distribution.thresholdClassification_sound
      ranges threshold value inside)

section
open Purelib.Measure
/-- Occurrence-wise range refinement narrows the exact threshold-event probability interval. -/
theorem Distribution.thresholdFrontier_eventBound_refines
    {α : Type} (distribution : Distribution α)
    (inner outer : α → Data.Rat.Interval) (threshold : Fraction.Rational)
    (refines : ∀ atom, atom ∈ distribution.atoms →
      Interval.Refines (inner atom.item) (outer atom.item)) :
    Interval.Refines
      (eventBound (distribution.thresholdFrontier inner threshold))
      (eventBound (distribution.thresholdFrontier outer threshold)) := by
  unfold Distribution.thresholdFrontier
  exact distribution.classifiedEventFrontier_refines
    (fun item => thresholdStatus (inner item) threshold)
    (fun item => thresholdStatus (outer item) threshold)
    (fun atom member =>
      thresholdStatus_refines (refines atom member))

/-- The classified lower bound equals original probability that the interval's lower endpoint reaches the threshold. -/
theorem Distribution.thresholdFrontier_lower_eq_probability_lower
    {α : Type} (distribution : Distribution α) (ranges : α → Data.Rat.Interval)
    (threshold : Fraction.Rational) :
    (eventBound (distribution.thresholdFrontier ranges threshold)).lower =
      distribution.probability
        (fun item => decide (threshold ≤ (ranges item).lower)) := by
  unfold Distribution.thresholdFrontier classifiedEventFrontier classifiedAtomsWith
    probability
  induction distribution.atoms with
  | nil => rfl
  | cons atom remaining inductionHypothesis =>
      have tailIH :
          lowerWeight (List.map (fun candidate =>
            (⟨candidate, thresholdStatus (ranges candidate.item) threshold⟩ :
              Classified α)) remaining) =
            eventWeight remaining
              (fun item => decide (threshold ≤ (ranges item).lower)) := by
        exact inductionHypothesis
      by_cases inside : threshold ≤ (ranges atom.item).lower
      · have headStatus :
            (fun item => thresholdStatus (ranges item) threshold) atom.item =
              .inside := by
          simp only [thresholdStatus, -eq_self, -iff_self]
          rewrite [if_pos inside]
          rfl
        rw [List.map_cons, headStatus]
        simp only [eventBound, lowerWeight, eventWeight, decide_eq_true inside,
          tailIH, -eq_self, -iff_self]
        rfl
      · by_cases outside : (ranges atom.item).upper < threshold
        · have headStatus :
              (fun item => thresholdStatus (ranges item) threshold) atom.item =
                .outside := by
            simp only [thresholdStatus, -eq_self, -iff_self]
            rewrite [if_neg inside, if_pos outside]
            rfl
          rw [List.map_cons, headStatus]
          simp only [eventBound, lowerWeight, eventWeight, decide_eq_false inside,
            zero_add, tailIH, -eq_self, -iff_self]
          rfl
        · have headStatus :
              (fun item => thresholdStatus (ranges item) threshold) atom.item =
                .unresolved := by
            simp only [thresholdStatus, -eq_self, -iff_self]
            rewrite [if_neg inside, if_neg outside]
            rfl
          rw [List.map_cons, headStatus]
          simp only [eventBound, lowerWeight, eventWeight, decide_eq_false inside,
            zero_add, tailIH, -eq_self, -iff_self]
          rfl

/-- The classified upper bound equals original probability that the interval's upper endpoint reaches the threshold. -/
theorem Distribution.thresholdFrontier_upper_eq_probability_upper
    {α : Type} (distribution : Distribution α) (ranges : α → Data.Rat.Interval)
    (threshold : Fraction.Rational) :
    (eventBound (distribution.thresholdFrontier ranges threshold)).upper =
      distribution.probability
        (fun item => decide (threshold ≤ (ranges item).upper)) := by
  unfold Distribution.thresholdFrontier classifiedEventFrontier classifiedAtomsWith
    probability
  induction distribution.atoms with
  | nil => rfl
  | cons atom remaining inductionHypothesis =>
      have tailIH :
          upperWeight (List.map (fun candidate =>
            (⟨candidate, thresholdStatus (ranges candidate.item) threshold⟩ :
              Classified α)) remaining) =
            eventWeight remaining
              (fun item => decide (threshold ≤ (ranges item).upper)) := by
        exact inductionHypothesis
      by_cases inside : threshold ≤ (ranges atom.item).lower
      · have upper : threshold ≤ (ranges atom.item).upper :=
          inside.trans (ranges atom.item).valid
        have headStatus :
            (fun item => thresholdStatus (ranges item) threshold) atom.item =
              .inside := by
          simp only [thresholdStatus, -eq_self, -iff_self]
          rewrite [if_pos inside]
          rfl
        rw [List.map_cons, headStatus]
        simp only [eventBound, upperWeight, eventWeight, decide_eq_true upper,
          tailIH, -eq_self, -iff_self]
        rfl
      · by_cases outside : (ranges atom.item).upper < threshold
        · have notUpper : ¬threshold ≤ (ranges atom.item).upper := outside.2
          have headStatus :
              (fun item => thresholdStatus (ranges item) threshold) atom.item =
                .outside := by
            simp only [thresholdStatus, -eq_self, -iff_self]
            rewrite [if_neg inside, if_pos outside]
            rfl
          rw [List.map_cons, headStatus]
          simp only [eventBound, upperWeight, eventWeight, decide_eq_false notUpper,
            zero_add, tailIH, -eq_self, -iff_self]
          rfl
        · have upper : threshold ≤ (ranges atom.item).upper :=
            Fraction.Order.Arithmetic.le_of_not_gt_direct outside
          have headStatus :
              (fun item => thresholdStatus (ranges item) threshold) atom.item =
                .unresolved := by
            simp only [thresholdStatus, -eq_self, -iff_self]
            rewrite [if_neg inside, if_neg outside]
            rfl
          rw [List.map_cons, headStatus]
          simp only [eventBound, upperWeight, eventWeight, decide_eq_true upper,
            tailIH, -eq_self, -iff_self]
          rfl

end

/-- Increasing the threshold cannot increase the exact classified probability lower bound. -/
theorem Distribution.thresholdFrontier_lower_anti
    {α : Type} (distribution : Distribution α) (ranges : α → Data.Rat.Interval)
    {lower upper : Fraction.Rational} (order : lower ≤ upper) :
    (eventBound (distribution.thresholdFrontier ranges upper)).lower ≤
      (eventBound (distribution.thresholdFrontier ranges lower)).lower := by
  rw [distribution.thresholdFrontier_lower_eq_probability_lower,
    distribution.thresholdFrontier_lower_eq_probability_lower]
  apply eventWeight_mono
  intro atom member selected
  have upperLe : upper ≤ (ranges atom.item).lower :=
    of_decide_eq_true selected
  exact decide_eq_true (order.trans upperLe)

/-- Increasing the threshold cannot increase the exact classified probability upper bound. -/
theorem Distribution.thresholdFrontier_upper_anti
    {α : Type} (distribution : Distribution α) (ranges : α → Data.Rat.Interval)
    {lower upper : Fraction.Rational} (order : lower ≤ upper) :
    (eventBound (distribution.thresholdFrontier ranges upper)).upper ≤
      (eventBound (distribution.thresholdFrontier ranges lower)).upper := by
  rw [distribution.thresholdFrontier_upper_eq_probability_upper,
    distribution.thresholdFrontier_upper_eq_probability_upper]
  apply eventWeight_mono
  intro atom member selected
  have upperLe : upper ≤ (ranges atom.item).upper :=
    of_decide_eq_true selected
  exact decide_eq_true (order.trans upperLe)

open Purelib.Measure in
/-- Resolving every retained range at the threshold makes the exact frontier's unresolved weight zero. -/
theorem Distribution.thresholdFrontier_unresolvedWeight_eq_zero
    {α : Type} (distribution : Distribution α)
    (ranges : α → Data.Rat.Interval) (threshold : Fraction.Rational)
    (resolved : ∀ atom, atom ∈ distribution.atoms →
      ThresholdResolved (ranges atom.item) threshold) :
    unresolvedWeight (distribution.thresholdFrontier ranges threshold) = 0 := by
  unfold Distribution.thresholdFrontier
  exact Measure.unresolvedWeight_thresholdFrontier_eq_zero
    ranges threshold distribution.atoms resolved

/-- Resolving every retained range at the threshold makes the exact event-bound interval have zero width. -/
theorem Distribution.thresholdFrontier_width_eq_zero_of_resolved
    {α : Type} (distribution : Distribution α)
    (ranges : α → Data.Rat.Interval) (threshold : Fraction.Rational)
    (resolved : ∀ atom, atom ∈ distribution.atoms →
      ThresholdResolved (ranges atom.item) threshold) :
    (eventBound (distribution.thresholdFrontier ranges threshold)).width = 0 := by
  rw [Measure.eventBound_width,
    distribution.thresholdFrontier_unresolvedWeight_eq_zero
      ranges threshold resolved]

end

end Purelib.Measure

end
