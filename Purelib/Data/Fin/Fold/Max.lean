module

import Purelib.Data.Fin
import Purelib.Data.Nat.Order
import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic

/-!
# Maxima of retained finite natural families
-/

namespace Purelib.Data.Fin.Fold.Max

open Purelib.Data

public section

/-- Compute the maximum of a natural-valued finite family.

The empty family has maximum zero. A nonempty family is reduced by taking the maximum of its value at zero and the
recursively computed maximum over successor indices. -/
@[expose] def maxFin : (count : Nat) → (Fin count → Nat) → Nat
  | 0, _ => 0
  | count + 1, values => max (values ⟨0, Nat.zero_lt_succ count⟩) (maxFin count (fun index => values index.succ))

section
/-- A uniform bound on a finite natural-valued family bounds its maximum.

If every retained index has value at most bound, the recursively computed maximum is also at most bound, including the
empty family. -/
theorem maxFin_le {count : Nat} (values : Fin count → Nat)
    (bound : Nat) (within : ∀ index, values index ≤ bound) :
    maxFin count values ≤ bound := by
  induction count with
  | zero => exact Nat.zero_le _
  | succ count inductionHypothesis =>
      unfold maxFin
      rw [Nat.Order.max_eq_natMax]
      apply Nat.Order.max_le (within ⟨0, Nat.zero_lt_succ count⟩)
      exact inductionHypothesis (fun index => values index.succ)
        (fun index => within index.succ)
end

/-- Every value of a finite natural-valued family is bounded by its maximum.

The displayed index witnesses a nonempty family. Induction through its zero or successor position compares its value
with the same recursively computed maximum. -/
theorem le_maxFin {count : Nat} (values : Fin count → Nat)
    (index : Fin count) : values index ≤ maxFin count values := by
  induction count with
  | zero => exact Fin.elim0 index
  | succ count inductionHypothesis =>
      refine Data.Fin.cases_induction ?_ (fun tail => ?_) index
      · rw [maxFin, Nat.Order.max_eq_natMax]
        exact Nat.Order.le_max_left _ _
      · rw [maxFin, Nat.Order.max_eq_natMax]
        exact (inductionHypothesis (fun next => values next.succ) tail).trans
          (Nat.Order.le_max_right _ _)

end

end Purelib.Data.Fin.Fold.Max
