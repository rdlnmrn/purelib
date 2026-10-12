module

import Purelib.Data.List.Nodup
import Purelib.Data.List.Range.Basic

/-!
# Distinct entries in finite natural ranges

The original range below a displayed count contains each of its labels once.
Appending the final label preserves duplicate-freeness because every retained
prefix member is strictly below it.
-/

namespace Purelib.Data.List.Range.Nodup

open Purelib.Data.List

/-- The finite natural range below any displayed count has no repeated entries.

The successor range appends its last label to the original prefix. Strict
membership bounds exclude that label from every retained prefix occurrence. -/
public theorem range_nodup (count : Nat) : (List.range count).Nodup := by
  induction count with
  | zero => exact List.nodup_nil
  | succ count inductionHypothesis =>
      rw [Basic.range_succ]
      apply Nodup.nodup_append inductionHypothesis (Nodup.nodup_singleton count)
      intro left leftMember right rightMember equality
      have leftBelow : left < count := Basic.mem_range.mp leftMember
      have rightEquals : right = count := by
        cases rightMember with
        | head => rfl
        | tail _ impossible => nomatch impossible
      have leftEquals : left = count := equality.trans rightEquals
      exact Nat.lt_irrefl count (leftEquals ▸ leftBelow)

end Purelib.Data.List.Range.Nodup
