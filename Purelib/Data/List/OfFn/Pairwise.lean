module

import Purelib.Data.List.OfFn.Basic

/-!
# Pairwise relations on indexed lists

Increasing finite-index comparisons certify the corresponding ordered list.
-/

public section

namespace Purelib.Data.List.OfFn.Pairwise

open Purelib.Data.List

/-- A relation holding at each increasing pair of finite indices holds pairwise in the
materialized list.

Structural induction keeps the original first entry and each successor-indexed
tail entry. The supplied relation is required only at increasing indices. -/
theorem pairwise_ofFn_direct
    {item : Type} {relation : item → item → Prop} {count : Nat}
    (values : Fin count → item)
    (ordered : ∀ first second, first < second →
      relation (values first) (values second)) :
    (List.ofFn values).Pairwise relation := by
  induction count with
  | zero => exact .nil
  | succ count inductionHypothesis =>
      rw [OfFn.Basic.ofFn_succ]
      apply List.Pairwise.cons
      · intro value member
        rcases OfFn.Basic.mem_ofFn.mp member with ⟨index, equal⟩
        subst value
        apply ordered (0 : Fin (count + 1)) index.succ
        change 0 < index.val + 1
        exact Nat.zero_lt_succ index.val
      · apply inductionHypothesis (fun index => values index.succ)
        intro first second indexOrder
        apply ordered first.succ second.succ
        exact Fin.succ_lt_succ_iff.mpr indexOrder

end Purelib.Data.List.OfFn.Pairwise
