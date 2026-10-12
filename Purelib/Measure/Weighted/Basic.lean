module

import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Fraction
public import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Finite rational contents and event bounds

Weights are attached only to a displayed finite list.  Event measurement is
a three-way finite classification: inside, outside, or unresolved.  The
unresolved weight is exactly the width of the returned rational enclosure.
-/

@[expose] public section

namespace Purelib.Measure

open Purelib.Data.Rat in
set_option genInjectivity false in
/-- Retain one payload with its exact nonnegative rational weight.

The record keeps the original payload and a proof for the stored weight. Lists of these records retain ordered
occurrences, including repeated payloads and zero-weight entries. -/
structure Weighted (α : Type) where
  /-- The original payload retained by this occurrence. -/ item : α
  /-- The exact rational weight of this occurrence. -/ weight : Fraction.Rational
  /-- The retained occurrence weight is nonnegative. -/ nonnegative : 0 ≤ weight

constructive_injectivity Weighted

namespace Weighted

open Purelib.Data.Rat in
/-- Read the exact rational weight retained by this weighted payload. -/
def amount {α : Type} (entry : Weighted α) : Fraction.Rational :=
  entry.weight

end Weighted

open Purelib.Data.Rat in
/-- Sum the retained nonnegative rational weights in the exact finite list order. -/
def totalWeight {α : Type} : List (Weighted α) → Fraction.Rational
  | [] => 0
  | entry :: remaining => entry.weight + totalWeight remaining

/-- The empty weighted list has total weight zero. -/
@[simp] theorem totalWeight_nil {α : Type} :
    totalWeight ([] : List (Weighted α)) = 0 := rfl

/-- The total of a nonempty weighted list is its head weight plus the exact tail total. -/
@[simp] theorem totalWeight_cons {α : Type} (entry : Weighted α)
    (remaining : List (Weighted α)) :
    totalWeight (entry :: remaining) =
      entry.weight + totalWeight remaining := rfl

/-- The total weight of every finite list of nonnegative weighted entries is nonnegative. -/
theorem totalWeight_nonneg {α : Type} :
    ∀ entries : List (Weighted α), 0 ≤ totalWeight entries
  | [] => le_rfl
  | entry :: remaining =>
      add_nonneg entry.nonnegative (totalWeight_nonneg remaining)

open Purelib.Data.Rat in
/-- Appending weighted lists adds their exact total weights.

The recursive sum retains both original lists and their occurrence order.
Scalar associativity transports the recursive tail total without changing
any retained weight or nonnegativity witness. -/
theorem totalWeight_append {α : Type}
    (left right : List (Weighted α)) :
    totalWeight (left ++ right) = totalWeight left + totalWeight right := by
  induction left with
  | nil => exact (Fraction.Field.zero_add _).symm
  | cons entry remaining ih =>
      change entry.weight + totalWeight (remaining ++ right) =
        (entry.weight + totalWeight remaining) + totalWeight right
      exact (congrArg (fun tail => entry.weight + tail) ih).trans
        (Fraction.Field.add_assoc _ _ _).symm
end Purelib.Measure

end
