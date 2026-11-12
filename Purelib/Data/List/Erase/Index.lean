module

public import Purelib.Data.List.GetD
import Purelib.Tactic.QuotientFreeOmega

/-!
# Original bounded coordinates after deleting a list position

The original list deletion retains every other occurrence in order. Both
directions of bounded coordinate transport read the same original entries;
no equality on entries or replacement list enumeration is required.
-/

public section

namespace Purelib.Data.List.Erase

universe u

variable {Alpha : Type u}

/-- Removing an original bounded position removes exactly one original list entry. -/
theorem length_eraseIdx (values : List Alpha) (position : Nat) (bound : position < values.length) :
    (values.eraseIdx position).length = values.length - 1 := by
  induction values generalizing position with
  | nil => exact False.elim (Nat.not_lt_zero position bound)
  | cons head remaining previous =>
      cases position with
      | zero => rfl
      | succ position =>
          change (remaining.eraseIdx position).length + 1 = remaining.length
          rw [previous position (Nat.lt_of_succ_lt_succ bound)]
          have positive : 0 < remaining.length :=
            Nat.lt_of_le_of_lt (Nat.zero_le position) (Nat.lt_of_succ_lt_succ bound)
          omega0

/-- An optional coordinate after original deletion skips precisely the removed position. -/
private theorem optional_eraseIdx (values : List Alpha) (removed position : Nat) :
    getElem? (values.eraseIdx removed) position =
      if position < removed then getElem? values position else getElem? values (position + 1) := by
  induction values generalizing removed position with
  | nil =>
      change none = if position < removed then none else none
      by_cases before : position < removed
      · rw [if_pos before]
      · rw [if_neg before]
  | cons head remaining previous =>
      cases removed with
      | zero =>
          rw [if_neg (Nat.not_lt_zero position)]
          rfl
      | succ removed =>
          cases position with
          | zero =>
              rw [if_pos (Nat.zero_lt_succ removed)]
              rfl
          | succ position =>
              change getElem? (remaining.eraseIdx removed) position =
                if position + 1 < removed + 1 then getElem? remaining position else getElem? remaining (position + 1)
              rw [previous removed position]
              by_cases before : position < removed
              · rw [if_pos before, if_pos (Nat.succ_lt_succ before)]
              · rw [if_neg before, if_neg (fun next => before (Nat.lt_of_succ_lt_succ next))]

/-- Read the original bounded source coordinate of a retained position after deletion. -/
@[expose] def sourceIndex (values : List Alpha) (removed : Fin values.length)
    (retained : Fin (values.eraseIdx removed.val).length) : Fin values.length :=
  if before : retained.val < removed.val then
    ⟨retained.val, Nat.lt_trans before removed.isLt⟩
  else ⟨retained.val + 1, by
    have bound : retained.val < values.length - 1 :=
      (congrArg (fun size => retained.val < size) (length_eraseIdx values removed.val removed.isLt)).mp retained.isLt
    have removedBound := removed.isLt
    omega0⟩

/-- A retained bounded coordinate reads its same original entry at its transported source index. -/
theorem getElem_sourceIndex (values : List Alpha) (removed : Fin values.length)
    (retained : Fin (values.eraseIdx removed.val).length) :
    (values.eraseIdx removed.val)[retained.val]'retained.isLt =
      values[(sourceIndex values removed retained).val]'(sourceIndex values removed retained).isLt := by
  have reading := optional_eraseIdx values removed.val retained.val
  rw [getElem?_eq_getElem _ retained.val retained.isLt] at reading
  by_cases before : retained.val < removed.val
  · rw [if_pos before, getElem?_eq_getElem values retained.val (Nat.lt_trans before removed.isLt)] at reading
    have scalar := Option.some.inj reading
    rw [sourceIndex, dif_pos before]
    exact scalar
  · have bound : retained.val < values.length - 1 :=
      (congrArg (fun size => retained.val < size) (length_eraseIdx values removed.val removed.isLt)).mp retained.isLt
    have originalBound : retained.val + 1 < values.length := by
      have removedBound := removed.isLt
      omega0
    rw [if_neg before, getElem?_eq_getElem values (retained.val + 1) originalBound] at reading
    have scalar := Option.some.inj reading
    rw [sourceIndex, dif_neg before]
    exact scalar

/-- Rebind an original different bounded position after deleting another original occurrence. -/
@[expose] def index (values : List Alpha) (removed original : Fin values.length)
    (different : original ≠ removed) : Fin (values.eraseIdx removed.val).length :=
  if before : original.val < removed.val then
    ⟨original.val, by
      rw [length_eraseIdx values removed.val removed.isLt]
      have removedBound := removed.isLt
      omega0⟩
  else ⟨original.val - 1, by
    rw [length_eraseIdx values removed.val removed.isLt]
    have originalBound := original.isLt
    have removedBound := removed.isLt
    have distinct : original.val ≠ removed.val := fun same => different (Fin.ext same)
    omega0⟩

/-- Rebinding a different original occurrence and returning to the source preserves its complete bounded index. -/
theorem sourceIndex_index (values : List Alpha) (removed original : Fin values.length)
    (different : original ≠ removed) :
    sourceIndex values removed (index values removed original different) = original := by
  by_cases before : original.val < removed.val
  · rw [index, dif_pos before]
    rw [sourceIndex, dif_pos before]
  · rw [index, dif_neg before]
    have distinct : original.val ≠ removed.val := fun same => different (Fin.ext same)
    have after : ¬original.val - 1 < removed.val := by omega0
    rw [sourceIndex, dif_neg after]
    apply Fin.ext
    change original.val - 1 + 1 = original.val
    omega0

/-- Rebinding an original different bounded occurrence preserves its same original entry. -/
theorem getElem_index (values : List Alpha) (removed original : Fin values.length)
    (different : original ≠ removed) :
    (values.eraseIdx removed.val)[(index values removed original different).val]'
      (index values removed original different).isLt = values[original.val]'original.isLt := by
  have reading := getElem_sourceIndex values removed (index values removed original different)
  have same := sourceIndex_index values removed original different
  exact reading.trans (congrArg (fun coordinate : Fin values.length => values[coordinate.val]'coordinate.isLt) same)

end Purelib.Data.List.Erase

end
