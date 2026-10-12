module

import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction
import Purelib.Measure.Weighted.Basic
public import Purelib.Measure.Weighted.Event
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
meta import Purelib.Elab.ConstructiveInjectivity

section
@[expose] public section

/-!
# Finite rational probability

A probability distribution is a displayed finite weighted list whose total is
exactly one.  Events are executable Boolean tests, so their probabilities and
expectations are exact rational calculations.
-/

namespace Purelib.Measure

set_option genInjectivity false in
/-- Retain a finite list of nonnegative weighted occurrences with total weight exactly one.

The original ordered list is the probability representation, including repeated payloads and zero-weight occurrences.
The normalization witness refers to that exact list. -/
structure Distribution (α : Type) where
  /-- The exact finite ordered list of nonnegative weighted payload occurrences. -/ atoms : List (Weighted α)
  /-- The same retained occurrence list has total weight exactly one. -/ total_one : totalWeight atoms = 1

constructive_injectivity Distribution

namespace Distribution

/-- Two finite distributions with the same exact occurrence list are equal. -/
theorem eq_of_atoms_eq {α : Type} (left right : Distribution α)
    (atomsEqual : left.atoms = right.atoms) : left = right := by
  cases left with
  | mk leftAtoms leftTotal =>
      cases right with
      | mk rightAtoms rightTotal =>
          cases atomsEqual
          rfl

end Distribution
namespace Distribution

open Purelib.Data.Rat in
/-- Sum the weights of the retained distribution occurrences selected by a Boolean event. -/
def probability {α : Type} (distribution : Distribution α)
    (event : α → Bool) : Fraction.Rational :=
  eventWeight distribution.atoms event

/-- Pointwise equal Boolean events have equal probability under the same retained distribution. -/
theorem probability_congr {α : Type} (distribution : Distribution α)
    (left right : α → Bool) (pointwise : ∀ item, left item = right item) :
    distribution.probability left = distribution.probability right :=
  eventWeight_congr distribution.atoms left right pointwise

/-- Every Boolean event has nonnegative probability. -/
theorem probability_nonneg {α : Type} (distribution : Distribution α)
    (event : α → Bool) : 0 ≤ distribution.probability event :=
  eventWeight_nonneg distribution.atoms event

/-- Every Boolean event has probability at most one. -/
theorem probability_le_one {α : Type} (distribution : Distribution α)
    (event : α → Bool) : distribution.probability event ≤ 1 := by
  rw [← distribution.total_one]
  exact eventWeight_le_totalWeight distribution.atoms event

/-- An event and its Boolean complement have probabilities summing to one. -/
theorem probability_add_complement {α : Type}
    (distribution : Distribution α) (event : α → Bool) :
    distribution.probability event +
      distribution.probability (complementEvent event) = 1 := by
  unfold probability
  rw [eventWeight_add_complement, distribution.total_one]

/-- The probabilities of two events sum to those of their union and intersection. -/
theorem probability_valuation {α : Type}
    (distribution : Distribution α) (first second : α → Bool) :
    distribution.probability first + distribution.probability second =
      distribution.probability (unionEvent first second) +
        distribution.probability (intersectionEvent first second) :=
  eventWeight_valuation distribution.atoms first second

/-- Events disjoint on the retained occurrences have additive union probability. -/
theorem probability_union_of_disjoint {α : Type}
    (distribution : Distribution α) {first second : α → Bool}
    (disjoint : DisjointOn distribution.atoms first second) :
    distribution.probability (unionEvent first second) =
      distribution.probability first + distribution.probability second :=
  eventWeight_union_of_disjoint disjoint

/-- Events disjoint on the retained occurrences have zero intersection probability. -/
theorem probability_intersection_eq_zero_of_disjoint {α : Type}
    (distribution : Distribution α) {first second : α → Bool}
    (disjoint : DisjointOn distribution.atoms first second) :
    distribution.probability (intersectionEvent first second) = 0 :=
  eventWeight_intersection_eq_zero_of_disjoint disjoint

open Purelib.Data.Rat in
/-- The everywhere-false event has probability zero.

Every retained occurrence contributes scalar zero to the original event
scan. Zero addition and the unchanged tail certificate identify its exact
weight without changing the distribution's occurrence list. -/
@[simp] theorem probability_false {α : Type}
    (distribution : Distribution α) :
    distribution.probability (fun _ => false) = 0 := by
  unfold probability
  induction distribution.atoms with
  | nil => rfl
  | cons atom remaining inductionHypothesis =>
      exact (Fraction.Field.zero_add _).trans inductionHypothesis

/-- The everywhere-true event has probability one.

Every retained occurrence contributes its original weight. Scalar tail
transport identifies the event scan with the same total-weight scan, and
the distribution's retained normalization certificate gives one. -/
@[simp] theorem probability_true {α : Type}
    (distribution : Distribution α) :
    distribution.probability (fun _ => true) = 1 := by
  unfold probability
  have allWeight : eventWeight distribution.atoms (fun _ => true) =
      totalWeight distribution.atoms := by
    induction distribution.atoms with
    | nil => rfl
    | cons atom remaining inductionHypothesis =>
        exact congrArg (fun tail => atom.weight + tail) inductionHypothesis
  exact allWeight.trans distribution.total_one
end Distribution

end Purelib.Measure

end

section
@[expose] public section

/-!
# Independence of finite rational events

Independence is an exact rational multiplication identity between three
finite event evaluations.  Event families remain displayed lists.
-/

namespace Purelib.Measure

/-- Splitting one event by another event and its complement preserves the first event's probability. -/
theorem Distribution.probability_intersection_add_complement
    {α : Type} (distribution : Distribution α)
    (left right : α → Bool) :
    distribution.probability (intersectionEvent left right) +
        distribution.probability
          (intersectionEvent left (complementEvent right)) =
      distribution.probability left := by
  unfold probability
  induction distribution.atoms with
  | nil =>
      simp only [eventWeight]
      ring1
  | cons atom remaining inductionHypothesis =>
      cases leftSelected : left atom.item <;>
        cases rightSelected : right atom.item <;>
        simp only [eventWeight, intersectionEvent, complementEvent,
          leftSelected, rightSelected, Bool.false_and, Bool.true_and,
          Bool.not_false, Bool.not_true, zero_add] <;>
        rw [← inductionHypothesis] <;>
        ring1
end Purelib.Measure

end
