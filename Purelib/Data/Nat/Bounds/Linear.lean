module

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring

section
public section

/-!
# Resource bounds for displayed fraction-free Bézout cofactors

The separated-Sylvester scalar is only one component of the certificate.
This module also bounds the coefficient slots of every polynomial in the
scaled inverse.  The recurrence is source-only: a Schur round doubles the
matrix slot bound, and unwinding a block adds twice the current bound.
-/

section

namespace Purelib.Data.Nat.Bounds.Linear
/-- Bound a four-term natural weighted sum when every weight is at most eight.

The three displayed variable contributions and the constant contribution together are
at most eight times the sum of the three variables plus one. -/
theorem weighted_sum_le_eight_mul_sum
    (slots recursiveSlots count slotWeight recursiveWeight countWeight
      constantWeight : Nat)
    (slotWeightLe : slotWeight ≤ 8)
    (recursiveWeightLe : recursiveWeight ≤ 8)
    (countWeightLe : countWeight ≤ 8)
    (constantWeightLe : constantWeight ≤ 8) :
    slotWeight * slots + recursiveWeight * recursiveSlots +
        countWeight * count + constantWeight ≤
      8 * (slots + recursiveSlots + count + 1) := by
  calc
    slotWeight * slots + recursiveWeight * recursiveSlots +
          countWeight * count + constantWeight ≤
        8 * slots + 8 * recursiveSlots + 8 * count + 8 :=
      Nat.add_le_add
        (Nat.add_le_add
          (Nat.add_le_add
            (Nat.mul_le_mul_right slots slotWeightLe)
            (Nat.mul_le_mul_right recursiveSlots recursiveWeightLe))
          (Nat.mul_le_mul_right count countWeightLe))
        constantWeightLe
    _ = 8 * (slots + recursiveSlots + count + 1) := by ring1
end Purelib.Data.Nat.Bounds.Linear

end

end

section

namespace Purelib.Data.Nat.Bounds.Linear
/-- An explicitly bounded positive natural below seven is one of the six
displayed possibilities. -/
public theorem eq_one_through_six_of_bounds
    (index : Nat) (positive : 1 ≤ index) (below : index < 7) :
    index = 1 ∨ index = 2 ∨ index = 3 ∨
      index = 4 ∨ index = 5 ∨ index = 6 := by
  cases index with
  | zero => exact False.elim (Nat.not_succ_le_zero 0 positive)
  | succ index =>
      cases index with
      | zero => exact Or.inl rfl
      | succ index =>
          cases index with
          | zero => exact Or.inr (Or.inl rfl)
          | succ index =>
              cases index with
              | zero => exact Or.inr (Or.inr (Or.inl rfl))
              | succ index =>
                  cases index with
                  | zero => exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
                  | succ index =>
                      cases index with
                      | zero =>
                          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
                      | succ index =>
                          cases index with
                          | zero =>
                              exact Or.inr (Or.inr (Or.inr
                                (Or.inr (Or.inr rfl))))
                          | succ index =>
                              exact False.elim
                                ((Nat.not_lt_of_ge
                                  (Nat.le_add_left 7 index)) below)
end Purelib.Data.Nat.Bounds.Linear
end
