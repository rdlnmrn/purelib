module
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Measure.Weighted.Basic
import Purelib.Measure.Weighted.Event
import Purelib.Data.List.Membership
public import Purelib.Measure.Weighted.Integral
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic

import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic

section
section
@[expose] public section

/-!
# Equality away from displayed zero weight

This is a finite replacement for almost-everywhere reasoning.  It quantifies
only over the supplied list of weighted atoms: two evaluations may differ at
an atom only when that atom carries exactly zero rational weight.
-/

namespace Purelib.Measure

/-- Require each retained occurrence to have zero weight or equal observable values.

The disjunction belongs to each exact list occurrence, retaining executable evidence rather than quotienting payloads or
discarding zero-weight entries. -/
def EqualOffZeroWeightOn {α β : Type} (atoms : List (Weighted α))
    (left right : α → β) : Prop :=
  ∀ atom, atom ∈ atoms → atom.weight = 0 ∨ left atom.item = right atom.item

namespace EqualOffZeroWeightOn

/-- Every observable agrees with itself away from zero-weight retained occurrences. -/
theorem refl {α β : Type} (atoms : List (Weighted α)) (value : α → β) :
    EqualOffZeroWeightOn atoms value value := by
  intro atom member
  exact Or.inr rfl

/-- Reverse agreement away from zero-weight retained occurrences. -/
theorem symm {α β : Type} {atoms : List (Weighted α)}
    {left right : α → β} (equal : EqualOffZeroWeightOn atoms left right) :
    EqualOffZeroWeightOn atoms right left := by
  intro atom member
  rcases equal atom member with zero | same
  · exact Or.inl zero
  · exact Or.inr same.symm

/-- Compose agreement through the same middle observable on the exact retained occurrence list. -/
theorem trans {α β : Type} {atoms : List (Weighted α)}
    {left middle right : α → β}
    (leftMiddle : EqualOffZeroWeightOn atoms left middle)
    (middleRight : EqualOffZeroWeightOn atoms middle right) :
    EqualOffZeroWeightOn atoms left right := by
  intro atom member
  rcases leftMiddle atom member with zero | first
  · exact Or.inl zero
  rcases middleRight atom member with zero | second
  · exact Or.inl zero
  · exact Or.inr (Eq.trans first second)

end EqualOffZeroWeightOn

open Purelib.Data.Rat in
/-- Agreement away from zero-weight occurrences preserves the exact weighted integral.

Each original occurrence either has zero weight or the same two scalar readings. Finite induction retains the original
occurrence order and weighted sum. -/
theorem expectationWeight_congr_off_zero {α : Type} :
    ∀ (atoms : List (Weighted α)) (left right : α → Fraction.Rational),
      EqualOffZeroWeightOn atoms left right →
        Distribution.expectationWeight atoms left =
          Distribution.expectationWeight atoms right := by
  intro atoms left right equal
  induction atoms with
  | nil => rfl
  | cons atom remaining inductionHypothesis =>
      have tail : EqualOffZeroWeightOn remaining left right :=
        fun candidate member =>
          equal candidate (List.mem_cons_of_mem atom member)
      rcases equal atom List.mem_cons_self with zero | same
      · simp only [Distribution.expectationWeight, zero, zero_mul,
          inductionHypothesis tail, -eq_self, -iff_self]
        rfl
      · simp only [Distribution.expectationWeight, same,
          inductionHypothesis tail, -eq_self, -iff_self]
        rfl

/-- Boolean agreement away from zero-weight occurrences preserves the exact event weight.

Every retained occurrence contributes the same selected weight on both sides, with zero-weight occurrences contributing
zero under either event. -/
theorem eventWeight_congr_off_zero {α : Type} :
    ∀ (atoms : List (Weighted α)) (left right : α → Bool),
      EqualOffZeroWeightOn atoms left right →
        eventWeight atoms left = eventWeight atoms right := by
  intro atoms left right equal
  induction atoms with
  | nil => rfl
  | cons atom remaining inductionHypothesis =>
      have tail : EqualOffZeroWeightOn remaining left right :=
        fun candidate member =>
          equal candidate (List.mem_cons_of_mem atom member)
      have headEqual :
          (match left atom.item with
            | true => atom.weight
            | false => 0) =
          (match right atom.item with
            | true => atom.weight
            | false => 0) := by
        rcases equal atom List.mem_cons_self with zero | same
        · cases leftChoice : left atom.item <;>
            cases rightChoice : right atom.item <;>
            simp only [zero, -eq_self, -iff_self] <;> rfl
        · rw [same]
      change
        (match left atom.item with
          | true => atom.weight
          | false => 0) + eventWeight remaining left =
        (match right atom.item with
          | true => atom.weight
          | false => 0) + eventWeight remaining right
      rw [headEqual, inductionHypothesis tail]

open Purelib.Data.List in
/-- The weight of a selected retained occurrence is at most its event's total weight.

The original membership witness locates that selected occurrence in the finite atom list, whose remaining weights are
nonnegative. -/
theorem atom_weight_le_eventWeight_of_mem {α : Type} :
    ∀ {atoms : List (Weighted α)} {event : α → Bool}
      {candidate : Weighted α},
      candidate ∈ atoms → event candidate.item = true →
        candidate.weight ≤ eventWeight atoms event
  | [], event, candidate, member, selected => by
      cases member
  | atom :: remaining, event, candidate, member, selected => by
      rcases Membership.mem_cons.mp member with head | tailMember
      · rw [head] at selected ⊢
        simp only [eventWeight, selected]
        exact le_add_of_nonneg_right (eventWeight_nonneg remaining event)
      · have tailBound := atom_weight_le_eventWeight_of_mem
          tailMember selected
        cases headSelected : event atom.item
        · simpa only [eventWeight, headSelected, zero_add] using tailBound
        · simp only [eventWeight, headSelected]
          exact tailBound.trans (le_add_of_nonneg_left atom.nonnegative)

/-- Require two observables to agree at every retained occurrence outside the exceptional Boolean event. -/
def EqualOutsideEventOn {α β : Type} (atoms : List (Weighted α))
    (exceptional : α → Bool) (left right : α → β) : Prop :=
  ∀ atom, atom ∈ atoms → exceptional atom.item = false →
    left atom.item = right atom.item

open Purelib.Data.Rat in
/-- Agreement outside a zero-weight event gives agreement away from zero-weight occurrences. -/
theorem equalOffZeroWeight_of_equalOutsideEvent {α β : Type}
    (atoms : List (Weighted α)) (exceptional : α → Bool)
    (left right : α → β)
    (zero : eventWeight atoms exceptional = 0)
    (outside : EqualOutsideEventOn atoms exceptional left right) :
    EqualOffZeroWeightOn atoms left right := by
  intro atom member
  cases selected : exceptional atom.item
  · exact Or.inr (outside atom member selected)
  · have weightLe := atom_weight_le_eventWeight_of_mem member selected
    rw [zero] at weightLe
    exact Or.inl (Fraction.Order.Basic.Compatibility.le_antisymm _ _
      weightLe atom.nonnegative)

namespace Distribution
end Distribution

end Purelib.Measure

end

end

section
@[expose] public section

/-!
# Finite almost-everywhere calculus

Equality almost everywhere means equality at every displayed atom whose
rational weight is nonzero.  The relation is executable on finite atom
tables and supports arithmetic, integration, and an exact L1
characterization without quotienting a function space.
-/

namespace Purelib.Measure
namespace EqualOffZeroWeightOn

/-- Applying the same function preserves agreement away from zero-weight occurrences. -/
theorem comp {α β γ : Type} {atoms : List (Weighted α)}
    {left right : α → β}
    (equal : EqualOffZeroWeightOn atoms left right)
    (function : β → γ) :
    EqualOffZeroWeightOn atoms
      (fun item => function (left item))
      (fun item => function (right item)) := by
  intro atom member
  rcases equal atom member with zero | same
  · exact Or.inl zero
  · exact Or.inr (congrArg function same)

open Purelib.Data.Rat
/-- Add two agreements away from zero-weight occurrences on the same retained list. -/
theorem add {α : Type} {atoms : List (Weighted α)}
    {leftFirst leftSecond rightFirst rightSecond : α → Fraction.Rational}
    (leftEqual : EqualOffZeroWeightOn atoms leftFirst leftSecond)
    (rightEqual : EqualOffZeroWeightOn atoms rightFirst rightSecond) :
    EqualOffZeroWeightOn atoms
      (fun item => leftFirst item + rightFirst item)
      (fun item => leftSecond item + rightSecond item) := by
  intro atom member
  rcases leftEqual atom member with zero | leftSame
  · exact Or.inl zero
  rcases rightEqual atom member with zero | rightSame
  · exact Or.inl zero
  · apply Or.inr
    change leftFirst atom.item + rightFirst atom.item =
      leftSecond atom.item + rightSecond atom.item
    rw [leftSame, rightSame]

/-- Negation preserves agreement away from zero-weight occurrences. -/
theorem neg {α : Type} {atoms : List (Weighted α)}
    {left right : α → Fraction.Rational}
    (equal : EqualOffZeroWeightOn atoms left right) :
    EqualOffZeroWeightOn atoms
      (fun item => -left item) (fun item => -right item) :=
  equal.comp fun value => -value

/-- Subtract two agreements away from zero-weight occurrences on the same retained list. -/
theorem sub {α : Type} {atoms : List (Weighted α)}
    {leftFirst leftSecond rightFirst rightSecond : α → Fraction.Rational}
    (leftEqual : EqualOffZeroWeightOn atoms leftFirst leftSecond)
    (rightEqual : EqualOffZeroWeightOn atoms rightFirst rightSecond) :
    EqualOffZeroWeightOn atoms
      (fun item => leftFirst item - rightFirst item)
      (fun item => leftSecond item - rightSecond item) := by
  have combined := leftEqual.add rightEqual.neg
  exact combined

/-- Multiply two agreements away from zero-weight occurrences on the same retained list. -/
theorem mul {α : Type} {atoms : List (Weighted α)}
    {leftFirst leftSecond rightFirst rightSecond : α → Fraction.Rational}
    (leftEqual : EqualOffZeroWeightOn atoms leftFirst leftSecond)
    (rightEqual : EqualOffZeroWeightOn atoms rightFirst rightSecond) :
    EqualOffZeroWeightOn atoms
      (fun item => leftFirst item * rightFirst item)
      (fun item => leftSecond item * rightSecond item) := by
  intro atom member
  rcases leftEqual atom member with zero | leftSame
  · exact Or.inl zero
  rcases rightEqual atom member with zero | rightSame
  · exact Or.inl zero
  · apply Or.inr
    change leftFirst atom.item * rightFirst atom.item =
      leftSecond atom.item * rightSecond atom.item
    rw [leftSame, rightSame]

/-- Rational scaling preserves agreement away from zero-weight occurrences. -/
theorem scale {α : Type} {atoms : List (Weighted α)}
    (factor : Fraction.Rational) {left right : α → Fraction.Rational}
    (equal : EqualOffZeroWeightOn atoms left right) :
    EqualOffZeroWeightOn atoms
      (fun item => factor * left item)
      (fun item => factor * right item) :=
  equal.comp fun value => factor * value

end EqualOffZeroWeightOn

end Purelib.Measure

end
