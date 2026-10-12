module
import Purelib.Data.Gaussian.Basic
public import Purelib.Geometry.Rational.Box.Basic

import Purelib.Tactic.QuotientFreeOmega
import Init.Prelude
import Purelib.Data.List.Membership

open Purelib.Data
open Purelib.Geometry

/-!
# First containing-box search

The finite scan returns the first original list index whose box contains the
query point. Its certificates retain the same ordered list and selected box.
-/

namespace Purelib.Geometry.Rational.Box.Search

/-! ## A total finite partition lookup -/

/-- Search a finite list for the first item whose associated box contains the point.

A successful result is an index bounded by the original list length. The recursive scan preserves list order and returns
none when no test succeeds. -/
@[expose] public def findContainingIndex
    {α : Type} (boxOf : α → Rational.Box) (point : Gaussian.Basic.Canonical) :
    (values : List α) → Option (Fin values.length)
  | [] => none
  | head :: tail =>
      if (boxOf head).Contains point then some 0
      else
        match findContainingIndex boxOf point tail with
        | none => none
        | some index => some index.succ

/-- A returned index selects an item whose box contains the query point.

The certificate follows the original head test and recursive tail result,
retaining the selected occurrence and its bound in the input list. -/
public theorem findContainingIndex_sound
    {α : Type} (boxOf : α → Rational.Box) (point : Gaussian.Basic.Canonical) :
    ∀ (values : List α) (index : Fin values.length),
      findContainingIndex boxOf point values = some index →
        (boxOf (values.get index)).Contains point
  | [], index, _ => Fin.elim0 index
  | head :: tail, index, found => by
      by_cases headContains : (boxOf head).Contains point
      · rw [findContainingIndex, if_pos headContains] at found
        have indexZero : index = 0 := Option.some.inj found.symm
        subst index
        exact headContains
      · rw [findContainingIndex, if_neg headContains] at found
        cases recursive : findContainingIndex boxOf point tail with
        | none => rw [recursive] at found; contradiction
        | some tailIndex =>
            rw [recursive] at found
            have indexSucc : index = tailIndex.succ :=
              Option.some.inj found.symm
            subst index
            exact findContainingIndex_sound boxOf point tail tailIndex
              recursive

/-- A displayed containing item guarantees a successful finite search.

A head occurrence either passes its containment test or moves the same witness
to the tail. No choice or reordering is needed to exclude the absent result. -/
public theorem findContainingIndex_ne_none_of_exists
    {α : Type} (boxOf : α → Rational.Box) (point : Gaussian.Basic.Canonical) :
    ∀ (values : List α),
      (∃ value ∈ values, (boxOf value).Contains point) →
        findContainingIndex boxOf point values ≠ none := by
  intro values witness
  induction values with
  | nil =>
      rcases witness with ⟨value, member, _⟩
      exact (List.not_mem_nil member).elim
  | cons head tail inductionHypothesis =>
      by_cases headContains : (boxOf head).Contains point
      · intro foundNone
        rw [findContainingIndex, if_pos headContains] at foundNone
        exact Option.some_ne_none 0 foundNone
      · have tailExists : ∃ value ∈ tail,
            (boxOf value).Contains point := by
          rcases witness with ⟨value, member, contains⟩
          rcases List.Membership.mem_cons.mp member with rfl | tailMember
          · exact (headContains contains).elim
          · exact ⟨value, tailMember, contains⟩
        have recursive := inductionHypothesis tailExists
        intro foundNone
        rw [findContainingIndex, if_neg headContains] at foundNone
        cases found : findContainingIndex boxOf point tail with
        | none => exact (recursive found).elim
        | some index =>
            rw [found] at foundNone
            exact Option.some_ne_none index.succ foundNone
end Purelib.Geometry.Rational.Box.Search
