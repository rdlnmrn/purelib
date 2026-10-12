module

import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction
import Purelib.Measure.Weighted.Basic
public import Purelib.Measure.Weighted.Event

import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
meta import Purelib.Elab.ConstructiveInjectivity

section
public section

/-!
# Exact finite rational valuations

`Content` retains an ordered finite weighted occurrence list with unrestricted
total mass. Executable Boolean events read that exact list, and the resulting
rational measurements obey the finite valuation identities.
-/

namespace Purelib.Measure

set_option genInjectivity false in
/-- Retain a finite content as an exact ordered list of nonnegative weighted payload occurrences.

Total mass is unrestricted. The retained list preserves repeated payloads and zero-weight occurrences and supplies all
event measurements directly. -/
structure Content (α : Type) where
  /-- The exact finite ordered list of nonnegative weighted occurrences. -/ atoms : List (Weighted α)

constructive_injectivity Content

namespace Content

section
open Purelib.Data.Rat
/-- Read the total nonnegative weight of the exact retained content occurrences. -/
@[expose] def total {α : Type} (content : Content α) : Fraction.Rational :=
  totalWeight content.atoms

/-- Sum the retained content weights selected by the supplied Boolean event. -/
@[expose] def measure {α : Type} (content : Content α)
    (event : α → Bool) : Fraction.Rational :=
  eventWeight content.atoms event

end

/-- Pointwise equal Boolean events have equal measurement in the same retained content. -/
theorem measure_congr {α : Type} (content : Content α)
    (left right : α → Bool) (pointwise : ∀ item, left item = right item) :
    content.measure left = content.measure right :=
  eventWeight_congr content.atoms left right pointwise

/-- Every event has nonnegative measurement in a finite nonnegative content. -/
theorem measure_nonneg {α : Type} (content : Content α)
    (event : α → Bool) : 0 ≤ content.measure event :=
  eventWeight_nonneg content.atoms event

/-- Every event's measurement is at most the same retained content's total weight. -/
theorem measure_le_total {α : Type} (content : Content α)
    (event : α → Bool) : content.measure event ≤ content.total :=
  eventWeight_le_totalWeight content.atoms event

open Purelib.Data.Rat in
/-- The everywhere-false event has content zero.

Every original occurrence contributes scalar zero. The same recursive tail
has zero event weight, and scalar zero addition identifies its retained
measurement with zero. -/
@[simp] theorem measure_empty {α : Type} (content : Content α) :
    content.measure (fun _ => false) = 0 := by
  unfold measure
  induction content.atoms with
  | nil => rfl
  | cons atom remaining ih =>
      change 0 + eventWeight remaining (fun _ => false) = 0
      exact (Fraction.Field.zero_add _).trans ih

/-- The everywhere-true event has the exact retained content total.

Every original occurrence contributes its retained weight. Scalar
congruence transports the equal event and total sums on the original tail,
so no payload or weight is reconstructed. -/
@[simp] theorem measure_univ {α : Type} (content : Content α) :
    content.measure (fun _ => true) = content.total := by
  unfold measure total
  induction content.atoms with
  | nil => rfl
  | cons atom remaining ih =>
      exact congrArg (fun tail => atom.weight + tail) ih

/-- The measurements of two events sum to those of their union and intersection. -/
theorem valuation {α : Type} (content : Content α)
    (first second : α → Bool) :
    content.measure first + content.measure second =
      content.measure (unionEvent first second) +
        content.measure (intersectionEvent first second) :=
  eventWeight_valuation content.atoms first second

/-- An event and its Boolean complement sum to the exact retained total content. -/
theorem add_complement {α : Type} (content : Content α)
    (event : α → Bool) :
    content.measure event + content.measure (complementEvent event) =
      content.total :=
  eventWeight_add_complement content.atoms event

/-- Events disjoint on the retained occurrences have additive union content. -/
theorem union_of_disjoint {α : Type} (content : Content α)
    {first second : α → Bool}
    (disjoint : DisjointOn content.atoms first second) :
    content.measure (unionEvent first second) =
      content.measure first + content.measure second :=
  eventWeight_union_of_disjoint disjoint

/-- Implication on the retained content occurrences makes event measurement monotone. -/
theorem mono {α : Type} (content : Content α)
    {first second : α → Bool}
    (implication : EventImpliesOn content.atoms first second) :
    content.measure first ≤ content.measure second :=
  eventWeight_mono implication

end Content

namespace Distribution
end Distribution

end Purelib.Measure

end
