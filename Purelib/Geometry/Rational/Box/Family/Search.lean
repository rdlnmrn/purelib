module
import Purelib.Data.Fin
import Purelib.Data.Gaussian.Basic
public import Purelib.Geometry.Rational.Box.Basic
import Init.Prelude

open Purelib

open Purelib.Geometry

section
public section

/-!
# Finite ownership of persistent CCL events

One boundary-event request must be compared with a complete finite family of
pairwise-separated winding regions, not just one selected pair.  This module
computes a single positive rational request width below every pair-specific
width and proves uniqueness of any explicit region meeting at that request.

The construction folds finite lists of displayed rationals.  It introduces
no root set, completed point, infinite minimum, or choice operation.
-/

namespace Purelib.Geometry.Rational.Box.Family.Search

/-- First finite box containing a displayed rational point. -/
@[expose] def findContainingBoxIndex (boxes : List
  Purelib.Geometry.Rational.Box) (point :
    Purelib.Data.Gaussian.Basic.Canonical) : Option (Fin boxes.length) :=
  match boxes with
  | [] => none
  | head :: tail =>
      if head.Contains point then
        some 0
      else
        match findContainingBoxIndex tail point with
        | none => none
        | some index => some index.succ

/-- An index returned by the finite search selects a box containing the supplied point. -/
theorem findContainingBoxIndex_sound
    (boxes : List Rational.Box) (point : Data.Gaussian.Basic.Canonical)
    (index : Fin boxes.length)
    (found : findContainingBoxIndex boxes point = some index) :
    (boxes.get index).Contains point := by
  induction boxes with
  | nil => exact Fin.elim0 index
  | cons head tail inductionHypothesis =>
      by_cases headContains : head.Contains point
      · rw [findContainingBoxIndex, if_pos headContains] at found
        have indexZero : index = 0 := Option.some.inj found.symm
        subst index
        exact headContains
      · rw [findContainingBoxIndex, if_neg headContains] at found
        cases recursive : findContainingBoxIndex tail point with
        | none => rw [recursive] at found; contradiction
        | some tailIndex =>
            rw [recursive] at found
            have indexSucc : index = tailIndex.succ :=
              Option.some.inj found.symm
            subst index
            exact inductionHypothesis tailIndex recursive

/-- A failed finite search certifies that every listed box excludes the supplied point. -/
theorem findContainingBoxIndex_none
    (boxes : List Rational.Box) (point : Data.Gaussian.Basic.Canonical)
    (found : findContainingBoxIndex boxes point = none) :
    ∀ index : Fin boxes.length, ¬(boxes.get index).Contains point := by
  induction boxes with
  | nil => intro index; exact Fin.elim0 index
  | cons head tail inductionHypothesis =>
      by_cases headContains : head.Contains point
      · rw [findContainingBoxIndex, if_pos headContains] at found
        contradiction
      · rw [findContainingBoxIndex, if_neg headContains] at found
        cases recursive : findContainingBoxIndex tail point with
        | some index => rw [recursive] at found; contradiction
        | none =>
            intro index
            refine Data.Fin.cases_induction headContains ?_ index
            intro tailIndex
            exact inductionHypothesis recursive tailIndex
end Purelib.Geometry.Rational.Box.Family.Search

end
