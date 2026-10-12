module

import Purelib.Data.Rat.Fraction
public import Purelib.Data.Rat.Interval.Basic
import Purelib.Elab.Deriving.Repr
public import Purelib.Measure.Weighted.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Finite rational contents and event bounds

Weights are attached only to a displayed finite list.  Event measurement is
a three-way finite classification: inside, outside, or unresolved.  The
unresolved weight is exactly the width of the returned rational enclosure.
-/

public section

namespace Purelib.Measure

/-- Record whether a retained occurrence is inside, outside, or unresolved for an event classification. -/
inductive Status where
  /-- The retained occurrence is classified inside the event. -/ | inside
  /-- The retained occurrence is classified outside the event. -/ | outside
  /-- The retained occurrence's membership remains unresolved. -/ | unresolved
deriving DecidableEq

derive_exposed_repr Status

set_option genInjectivity false in
/-- Pair an exact nonnegative weighted occurrence with its retained event-classification status. -/
structure Classified (α : Type) where
  /-- The exact original nonnegative weighted occurrence. -/ atom : Weighted α
  /-- The retained classification of this same occurrence. -/ status : Status

constructive_injectivity Classified

section
open Purelib.Data.Rat
/-- Sum the weights of all retained classified occurrences, independently of status. -/
@[expose] def classifiedWeight {α : Type} : List (Classified α) → Fraction.Rational
  | [] => 0
  | entry :: remaining => entry.atom.weight + Purelib.Measure.classifiedWeight remaining

/-- Sum only the retained weights classified as inside. -/
@[expose] def lowerWeight {α : Type} : List (Classified α) → Fraction.Rational
  | [] => 0
  | entry :: remaining =>
      (match entry.status with
        | .inside => entry.atom.weight
        | .outside | .unresolved => 0) + Purelib.Measure.lowerWeight remaining

/-- Sum retained weights classified as inside or unresolved. -/
@[expose] def upperWeight {α : Type} : List (Classified α) → Fraction.Rational
  | [] => 0
  | entry :: remaining =>
      (match entry.status with
        | .outside => 0
        | .inside | .unresolved => entry.atom.weight) + Purelib.Measure.upperWeight remaining

/-- Sum only the retained weights with unresolved classification. -/
@[expose] def unresolvedWeight {α : Type} : List (Classified α) → Fraction.Rational
  | [] => 0
  | entry :: remaining =>
      (match entry.status with
        | .unresolved => entry.atom.weight
        | .inside | .outside => 0) + Purelib.Measure.unresolvedWeight remaining

end

section
open Purelib
/-- The empty classified occurrence list has zero total weight. -/
@[simp] theorem classifiedWeight_nil {α : Type} :
    Measure.classifiedWeight ([] : List (Classified α)) = 0 := rfl

/-- The classified total of a head and tail is the head's exact weight plus the tail total. -/
@[simp] theorem classifiedWeight_cons {α : Type} (entry : Classified α)
    (remaining : List (Classified α)) :
    Measure.classifiedWeight (entry :: remaining) =
      entry.atom.weight + Measure.classifiedWeight remaining := rfl

/-- The empty classified occurrence list has zero lower weight. -/
@[simp] theorem lowerWeight_nil {α : Type} :
    Measure.lowerWeight ([] : List (Classified α)) = 0 := rfl

/-- The empty classified occurrence list has zero upper weight. -/
@[simp] theorem upperWeight_nil {α : Type} :
    Measure.upperWeight ([] : List (Classified α)) = 0 := rfl

/-- The empty classified occurrence list has zero unresolved weight. -/
@[simp] theorem unresolvedWeight_nil {α : Type} :
    Measure.unresolvedWeight ([] : List (Classified α)) = 0 := rfl

/-- The total classified weight is nonnegative. -/
theorem classifiedWeight_nonneg {α : Type} :
    ∀ entries : List (Classified α), 0 ≤ Measure.classifiedWeight entries
  | [] => le_rfl
  | entry :: remaining =>
      add_nonneg entry.atom.nonnegative
        (Purelib.Measure.classifiedWeight_nonneg remaining)

/-- The weight of occurrences classified as inside is nonnegative. -/
theorem lowerWeight_nonneg {α : Type} :
    ∀ entries : List (Classified α), 0 ≤ Measure.lowerWeight entries
  | [] => le_rfl
  | entry :: remaining => by
      rcases entry with ⟨atom, status⟩
      cases status
      · exact add_nonneg atom.nonnegative
          (Purelib.Measure.lowerWeight_nonneg remaining)
      · simpa only [-eq_self, -iff_self, Measure.lowerWeight, zero_add] using
          Purelib.Measure.lowerWeight_nonneg remaining
      · simpa only [-eq_self, -iff_self, Measure.lowerWeight, zero_add] using
          Purelib.Measure.lowerWeight_nonneg remaining

/-- The retained unresolved weight is nonnegative. -/
theorem unresolvedWeight_nonneg {α : Type} :
    ∀ entries : List (Classified α), 0 ≤ Measure.unresolvedWeight entries
  | [] => le_rfl
  | entry :: remaining => by
      rcases entry with ⟨atom, status⟩
      cases status
      · simpa only [-eq_self, -iff_self, Measure.unresolvedWeight, zero_add] using
          Purelib.Measure.unresolvedWeight_nonneg remaining
      · simpa only [-eq_self, -iff_self, Measure.unresolvedWeight, zero_add] using
          Purelib.Measure.unresolvedWeight_nonneg remaining
      · exact add_nonneg atom.nonnegative
          (Purelib.Measure.unresolvedWeight_nonneg remaining)

/-- Inside-or-unresolved weight is bounded by total classified weight. -/
theorem upperWeight_le_classifiedWeight {α : Type} :
    ∀ entries : List (Classified α),
      Measure.upperWeight entries ≤ Measure.classifiedWeight entries
  | [] => le_rfl
  | entry :: remaining => by
      rcases entry with ⟨atom, status⟩
      cases status
      · exact add_le_add le_rfl
          (Purelib.Measure.upperWeight_le_classifiedWeight remaining)
      · simpa only [-eq_self, -iff_self, Measure.upperWeight, Measure.classifiedWeight, zero_add] using
          (Purelib.Measure.upperWeight_le_classifiedWeight remaining).trans
            (le_add_of_nonneg_left atom.nonnegative)
      · exact add_le_add le_rfl
          (Purelib.Measure.upperWeight_le_classifiedWeight remaining)

/-- The upper classified weight is exactly the inside weight plus unresolved weight. -/
theorem upperWeight_eq_lower_add_unresolved {α : Type} :
    ∀ entries : List (Classified α),
      Measure.upperWeight entries = Measure.lowerWeight entries + Measure.unresolvedWeight entries
  | [] => by
      simp only [-eq_self, -iff_self, Measure.upperWeight_nil, Measure.lowerWeight_nil, Measure.unresolvedWeight_nil,
        add_zero]
      rfl
  | entry :: remaining => by
      have inductionHypothesis :=
        Purelib.Measure.upperWeight_eq_lower_add_unresolved remaining
      rcases entry with ⟨atom, status⟩
      cases status
      · dsimp only [Measure.upperWeight, Measure.lowerWeight, Measure.unresolvedWeight]
        rw [inductionHypothesis]
        ring1
      · dsimp only [Measure.upperWeight, Measure.lowerWeight, Measure.unresolvedWeight]
        rw [inductionHypothesis]
        ring1
      · dsimp only [Measure.upperWeight, Measure.lowerWeight, Measure.unresolvedWeight]
        rw [inductionHypothesis]
        ring1

/-- The lower classified weight is bounded by the upper classified weight. -/
theorem lowerWeight_le_upperWeight {α : Type}
    (entries : List (Classified α)) :
    Measure.lowerWeight entries ≤ Measure.upperWeight entries := by
  rw [Measure.upperWeight_eq_lower_add_unresolved]
  exact le_add_of_nonneg_right (Measure.unresolvedWeight_nonneg entries)

/-- Form the rational interval from the exact inside weight to the inside-or-unresolved weight.

Retain the two classified sums and certify their order using nonnegativity of the unresolved weight. -/
@[expose] def eventBound {α : Type} (entries : List (Classified α)) : Data.Rat.Interval where
  lower := Measure.lowerWeight entries
  upper := Measure.upperWeight entries
  valid := Measure.lowerWeight_le_upperWeight entries

end

open Purelib in
open Purelib.Data.Rat in
/-- The width of the retained event interval is exactly the original unresolved weight. -/
theorem eventBound_width {α : Type} (entries : List (Classified α)) :
    (Measure.eventBound entries).width = Measure.unresolvedWeight entries := by
  dsimp only [Interval.width, Measure.eventBound]
  rw [Measure.upperWeight_eq_lower_add_unresolved]
  ring1

section
open Purelib
/-- Concatenating classified lists adds their inside weights. -/
theorem lowerWeight_append {α : Type}
    (left right : List (Classified α)) :
    Measure.lowerWeight (left ++ right) = Measure.lowerWeight left + Measure.lowerWeight right := by
  induction left with
  | nil =>
      simp only [-eq_self, -iff_self, List.nil_append, Measure.lowerWeight_nil, zero_add]
      rfl
  | cons entry remaining inductionHypothesis =>
      rcases entry with ⟨atom, status⟩
      cases status <;>
        simp only [-eq_self, -iff_self, List.cons_append, Measure.lowerWeight, inductionHypothesis] <;>
        ring1

/-- Concatenating classified lists adds their inside-or-unresolved weights. -/
theorem upperWeight_append {α : Type}
    (left right : List (Classified α)) :
    Measure.upperWeight (left ++ right) = Measure.upperWeight left + Measure.upperWeight right := by
  induction left with
  | nil =>
      simp only [-eq_self, -iff_self, List.nil_append, Measure.upperWeight_nil, zero_add]
      rfl
  | cons entry remaining inductionHypothesis =>
      rcases entry with ⟨atom, status⟩
      cases status <;>
        simp only [-eq_self, -iff_self, List.cons_append, Measure.upperWeight, inductionHypothesis] <;>
        ring1

/-- Concatenating classified lists adds their unresolved weights. -/
theorem unresolvedWeight_append {α : Type}
    (left right : List (Classified α)) :
    Measure.unresolvedWeight (left ++ right) =
      Measure.unresolvedWeight left + Measure.unresolvedWeight right := by
  induction left with
  | nil =>
      simp only [-eq_self, -iff_self, List.nil_append, Measure.unresolvedWeight_nil, zero_add]
      rfl
  | cons entry remaining inductionHypothesis =>
      rcases entry with ⟨atom, status⟩
      cases status <;>
        simp only [-eq_self, -iff_self, List.cons_append, Measure.unresolvedWeight, inductionHypothesis] <;>
        ring1

/-- Concatenating classified lists adds their total weights. -/
theorem classifiedWeight_append {α : Type}
    (left right : List (Classified α)) :
    Measure.classifiedWeight (left ++ right) =
      Measure.classifiedWeight left + Measure.classifiedWeight right := by
  induction left with
  | nil =>
      simp only [-eq_self, -iff_self, List.nil_append, Measure.classifiedWeight_nil, zero_add]
      rfl
  | cons entry remaining inductionHypothesis =>
      simp only [-eq_self, -iff_self, List.cons_append, Measure.classifiedWeight_cons, inductionHypothesis]
      ring1

end

open Purelib
open Purelib.Data.Rat
/-- The event interval of concatenated classified lists is the sum of their exact event intervals. -/
theorem eventBound_append {α : Type}
    (left right : List (Classified α)) :
    Measure.eventBound (left ++ right) = (Measure.eventBound left).add (Measure.eventBound right) := by
  apply Interval.ext
  · exact Measure.lowerWeight_append left right
  · exact Measure.upperWeight_append left right

/-- Require the exact unresolved weight to be strictly smaller than the supplied tolerance. -/
@[expose] def Resolves {α : Type} (entries : List (Classified α))
    (epsilon : Fraction.Rational) : Prop :=
  Measure.unresolvedWeight entries < epsilon

/-- Resolving the retained classifications at a tolerance makes their event interval strictly narrower than that
tolerance. -/
theorem eventBound_width_lt {α : Type} {entries : List (Classified α)}
    {epsilon : Fraction.Rational} (resolves : Measure.Resolves entries epsilon) :
    (Measure.eventBound entries).width < epsilon := by
  rw [Measure.eventBound_width]
  exact resolves
end Purelib.Measure

end
