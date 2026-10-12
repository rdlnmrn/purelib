module

import Purelib.Tactic.QuotientFreeOmega
public import Mathlib.Order.Basic
public import Mathlib.Data.Nat.Basic
import Purelib.Data.Nat.Subtraction
import Purelib.Data.Nat.Addition

open Purelib.Data.Nat

/-!
# Removing a retained finite position

The original comparison removes one index and compresses the other indices.
Direct predecessor reconstruction proves injectivity on the retained domain.
-/

namespace Purelib.Data.Fin.Remove

/-- Delete one finite position and compress every distinct retained index.

Indices below the removed position keep their value; indices above it move down by
one. The displayed inequality witness rules out the removed position and certifies
the smaller bound. -/
@[expose] public def removeFinIndex {m : Nat} (removed value : Fin (m + 1))
    (different : value ≠ removed) : Fin m :=
  if lower : value.val < removed.val then
    ⟨value.val, lower.trans_le (Nat.le_of_lt_succ removed.isLt)⟩
  else
    ⟨value.val - 1, by
      have greater : removed.val < value.val := by
        have unequal : value.val ≠ removed.val := fun equal =>
          different (Fin.ext equal)
        exact Nat.lt_of_le_of_ne (Nat.le_of_not_gt lower) (Ne.symm unequal)
      exact (Nat.sub_lt (Nat.zero_lt_of_lt greater) (by decide)).trans_le
        (Nat.le_of_lt_succ value.isLt)⟩

/-- Deleting one position remains injective on indices different from that position.

The two value ranges remain separated at the removed position. Within either range,
equality of compressed natural values recovers equality of the original retained
indices. -/
public theorem removeFinIndex_injective {m : Nat}
    (removed : Fin (m + 1)) :
    ∀ {x y : Fin (m + 1)} (xDifferent : x ≠ removed)
      (yDifferent : y ≠ removed),
      removeFinIndex removed x xDifferent =
        removeFinIndex removed y yDifferent → x = y := by
  intro x y xDifferent yDifferent equal
  unfold removeFinIndex at equal
  split at equal <;> split at equal
  · have values := congrArg Fin.val equal
    change x.val = y.val at values
    exact Fin.ext values
  · rename_i xLower yNotLower
    have yGreater : removed.val < y.val := by
      have unequal : y.val ≠ removed.val := fun values =>
        yDifferent (Fin.ext values)
      exact Nat.lt_of_le_of_ne (Nat.le_of_not_gt yNotLower) (Ne.symm unequal)
    have values := congrArg Fin.val equal
    change x.val = y.val - 1 at values
    have removedLeYPredecessor : removed.val ≤ y.val - 1 :=
      by
        have restored : y.val - 1 + 1 = y.val :=
          (Nat.add_comm (y.val - 1) 1).trans
            (Subtraction.add_sub_of_le
              (Nat.succ_le_of_lt (Nat.zero_lt_of_lt yGreater)))
        have shifted : removed.val + 1 ≤ y.val - 1 + 1 :=
          restored.symm ▸ Nat.succ_le_of_lt yGreater
        obtain ⟨extra, equation⟩ := Nat.le.dest shifted
        rewrite [Nat.add_assoc, Nat.add_comm 1 extra, ← Nat.add_assoc] at equation
        exact Nat.le.intro (Addition.add_right_cancel equation)
    rw [← values] at removedLeYPredecessor
    exact False.elim ((Nat.not_le_of_gt xLower) removedLeYPredecessor)
  · rename_i xNotLower yLower
    have xGreater : removed.val < x.val := by
      have unequal : x.val ≠ removed.val := fun values =>
        xDifferent (Fin.ext values)
      exact Nat.lt_of_le_of_ne (Nat.le_of_not_gt xNotLower) (Ne.symm unequal)
    have values := congrArg Fin.val equal
    change x.val - 1 = y.val at values
    have removedLeXPredecessor : removed.val ≤ x.val - 1 :=
      by
        have restored : x.val - 1 + 1 = x.val :=
          (Nat.add_comm (x.val - 1) 1).trans
            (Subtraction.add_sub_of_le
              (Nat.succ_le_of_lt (Nat.zero_lt_of_lt xGreater)))
        have shifted : removed.val + 1 ≤ x.val - 1 + 1 :=
          restored.symm ▸ Nat.succ_le_of_lt xGreater
        obtain ⟨extra, equation⟩ := Nat.le.dest shifted
        rewrite [Nat.add_assoc, Nat.add_comm 1 extra, ← Nat.add_assoc] at equation
        exact Nat.le.intro (Addition.add_right_cancel equation)
    rw [values] at removedLeXPredecessor
    exact False.elim ((Nat.not_le_of_gt yLower) removedLeXPredecessor)
  · rename_i xNotLower yNotLower
    have xGreater : removed.val < x.val := by
      have unequal : x.val ≠ removed.val := fun values =>
        xDifferent (Fin.ext values)
      exact Nat.lt_of_le_of_ne (Nat.le_of_not_gt xNotLower) (Ne.symm unequal)
    have yGreater : removed.val < y.val := by
      have unequal : y.val ≠ removed.val := fun values =>
        yDifferent (Fin.ext values)
      exact Nat.lt_of_le_of_ne (Nat.le_of_not_gt yNotLower) (Ne.symm unequal)
    have values := congrArg Fin.val equal
    change x.val - 1 = y.val - 1 at values
    have xPredecessor : x.val - 1 + 1 = x.val :=
      (Nat.add_comm (x.val - 1) 1).trans
        (Subtraction.add_sub_of_le
          (Nat.succ_le_of_lt (Nat.zero_lt_of_lt xGreater)))
    have yPredecessor : y.val - 1 + 1 = y.val :=
      (Nat.add_comm (y.val - 1) 1).trans
        (Subtraction.add_sub_of_le
          (Nat.succ_le_of_lt (Nat.zero_lt_of_lt yGreater)))
    apply Fin.ext
    calc
      x.val = x.val - 1 + 1 := xPredecessor.symm
      _ = y.val - 1 + 1 := congrArg (fun value => value + 1) values
      _ = y.val := yPredecessor

end Purelib.Data.Fin.Remove
