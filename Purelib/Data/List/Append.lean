module
public import Purelib.Polynomial.Dense.Basic

import Purelib.Tactic.QuotientFreeOmega

namespace Purelib.Data.List.Append

/-- Regrouping three appended lists preserves the displayed entries.

Structural recursion on the first spine compares the same heads and transports
the equality of the remaining concatenations without changing their order. -/
public theorem append_assoc {Alpha : Type u} (first second third : List Alpha) :
    (first ++ second) ++ third = first ++ (second ++ third) := by
  induction first with
  | nil => rfl
  | cons head tail ih => exact congrArg (List.cons head) ih

/-- Appending two retained lists adds their displayed lengths.

Every entry of the original left spine contributes one successor to the
result's length; the unchanged right spine supplies the remaining length. -/
public theorem length_append {Alpha : Type u} (left right : List Alpha) :
    (left ++ right).length = left.length + right.length := by
  induction left with
  | nil => exact (Nat.zero_add right.length).symm
  | cons head tail ih =>
      change (tail ++ right).length + 1 = (tail.length + 1) + right.length
      rw [ih, Nat.succ_add]

/-- Appending an empty right list retains every original entry.

Structural recursion follows the original left spine. Each head is retained
unchanged, and scalar constructor congruence transports the empty-tail identity. -/
public theorem append_nil {Alpha : Type u} (entries : List Alpha) :
    entries ++ [] = entries := by
  induction entries with
  | nil => rfl
  | cons head tail ih => exact congrArg (List.cons head) ih

/-- A bounded position in the left list reads the same entry after concatenation.

Both bounds refer to the supplied original lists and the same natural coordinate.
Structural recursion removes matching head occurrences and retains the unchanged
right list throughout the readback. -/
public theorem getElem_append_left {Alpha : Type u} (left right : List Alpha)
    (index : Nat) (bound : index < left.length)
    (combinedBound : index < (left ++ right).length) :
    (left ++ right)[index]'combinedBound = left[index]'bound := by
  induction left generalizing index with
  | nil => cases bound
  | cons head tail retained =>
      cases index with
      | zero => rfl
      | succ index =>
          exact retained index (Nat.lt_of_succ_lt_succ bound)
            (Nat.lt_of_succ_lt_succ combinedBound)

/-- A right-list position reads the same entry at its concatenation offset.

The original left length supplies the offset, and the retained right bound
certifies the same displayed entry. Structural recursion removes exactly the
left prefix while keeping the right list and its coordinate unchanged. -/
public theorem getElem_append_right {Alpha : Type u} (left right : List Alpha)
    (index : Nat) (bound : index < right.length)
    (combinedBound : left.length + index < (left ++ right).length) :
    (left ++ right)[left.length + index]'combinedBound = right[index]'bound := by
  induction left with
  | nil => exact getElem_congr rfl (Nat.zero_add index) combinedBound
  | cons head tail retained =>
      have shift : (head :: tail).length + index = (tail.length + index) + 1 :=
        Nat.succ_add tail.length index
      have shiftedBound : (tail.length + index) + 1 < (tail ++ right).length + 1 :=
        shift ▸ combinedBound
      have tailBound : tail.length + index < (tail ++ right).length :=
        Nat.lt_of_succ_lt_succ shiftedBound
      exact (getElem_congr rfl shift combinedBound).trans (retained tailBound)

/-- Taking a list-concatenation prefix splits at the exact original first-list length. -/
public theorem take_append_direct {α : Type*} (first second : List α) (count : Nat) :
    (first ++ second).take count =
      first.take count ++ second.take (count - first.length) := by
  induction first generalizing count with
  | nil =>
      simp only [List.nil_append, List.take_nil, List.length_nil, Nat.sub_zero, -eq_self]
      rfl
  | cons entry remaining ih =>
      cases count with
      | zero =>
          simp only [List.take_zero, Nat.zero_sub, List.nil_append, -eq_self]
          rfl
      | succ count =>
          simpa only [List.cons_append, List.take_succ_cons, List.length_cons,
            Nat.succ_sub_succ_eq_sub, -eq_self, -iff_self] using
            congrArg (List.cons entry) (ih count)

/-- The head of concatenation comes from the first list when it is nonempty.

If the first list is empty, the second list supplies its original optional
head. Otherwise the first displayed occurrence is retained unchanged. -/
public theorem head?_append {Alpha : Type u} (first second : List Alpha) :
    (first ++ second).head? = first.head?.or second.head? := by
  cases first <;> rfl

/-- Appending a nonempty original list makes its last element the last of the concatenation.

The nonempty right spine supplies the final retained occurrence. Structural recursion removes only the original left
heads and leaves that right list unchanged. -/
public theorem getLast_append_nonempty
    {α : Type*} (left : List α) {right : List α} (nonempty : right ≠ []) :
    (left ++ right).getLast? = right.getLast? := by
  induction left with
  | nil => rfl
  | cons first remaining inductionHypothesis =>
      cases remaining with
      | nil =>
          cases right with
          | nil => exact (nonempty rfl).elim
          | cons head tail => rfl
      | cons second tail => exact inductionHypothesis

end Purelib.Data.List.Append

namespace Purelib.Data.List
open Purelib.Polynomial.Dense

/-- Prepend one retained coefficient list to another by structural recursion.

The empty prefix returns the existing list. A nonempty prefix retains its head
and recursively prepends its remaining entries, preserving order and the
original exact coefficient-polynomial carrier. -/
@[expose] public def prependConditions :
    List Polynomial.Dense.BoundaryFactorization.CoefficientPolynomial →
      List Polynomial.Dense.BoundaryFactorization.CoefficientPolynomial →
      List Polynomial.Dense.BoundaryFactorization.CoefficientPolynomial
  | [], existing => existing
  | condition :: remaining, existing =>
      condition :: Purelib.Data.List.prependConditions remaining existing

end Purelib.Data.List
