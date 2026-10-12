module

import Purelib.Tactic.QuotientFreeOmega

section
public section

/-!
# The finite permutation of a positive torus band

The ascending Artin band moves strand zero to the last position and every
other strand down by one.  This file proves that fact by evaluating each
displayed adjacent transposition.  The auxiliary arithmetic acts only on a
bounded natural prefix and is fully executable.
-/

namespace Purelib.Data.Nat.Permutation.Adjacent

/-! ## Natural-index evaluation -/

/-- Exchange one natural pivot with its successor.

Every other natural label is returned unchanged, so the operation is a total adjacent
transposition on Nat. -/
@[expose] def adjacentNatSwap (pivot value : Nat) : Nat :=
  if value = pivot then pivot + 1
  else if value = pivot + 1 then pivot
  else value

open Purelib.Data.Nat.Permutation
/-- Apply the adjacent swaps with pivots zero through steps - 1 in order.

Zero steps leave the label unchanged. A successor first runs the shorter sequence and
then swaps its result at the new final pivot. -/
@[expose] def ascendingAction : Nat → Nat → Nat
  | 0, value => value
  | steps + 1, value => adjacentNatSwap steps (ascendingAction steps
    value)

/-- Compute the effect of an ascending sequence of adjacent natural swaps.

Zero moves to steps, labels from one through steps decrease by one, and larger labels
remain unchanged. -/
theorem ascendingAction_formula : ∀ (steps value : Nat),
    ascendingAction steps value =
      if value = 0 then steps
      else if value ≤ steps then value - 1 else value
  | 0, value => by
      by_cases zero : value = 0
      · subst value
        rfl
      · have notLe : ¬value ≤ 0 := by omega
        simp only [-eq_self, -iff_self, ascendingAction, if_neg zero, if_neg notLe]
        rfl
  | steps + 1, value => by
      rw [ascendingAction, ascendingAction_formula]
      by_cases zero : value = 0
      · subst value
        simp only [-eq_self, -iff_self, if_pos rfl, adjacentNatSwap]
        rfl
      · by_cases within : value ≤ steps
        · have withinSucc : value ≤ steps + 1 := by omega
          have predecessorNePivot : value - 1 ≠ steps := by omega
          have predecessorNeNext : value - 1 ≠ steps + 1 := by omega
          simp only [-eq_self, -iff_self, if_neg zero, if_pos within, if_pos withinSucc,
            adjacentNatSwap, if_neg predecessorNePivot, if_neg predecessorNeNext]
          rfl
        · by_cases atNext : value = steps + 1
          · subst value
            have nonzero : steps + 1 ≠ 0 := by omega
            have notWithin : ¬steps + 1 ≤ steps := by omega
            have withinSucc : steps + 1 ≤ steps + 1 := Nat.le_refl _
            have nextNePivot : steps + 1 ≠ steps := by omega
            have predecessor : steps + 1 - 1 = steps := by omega
            simp only [-eq_self, -iff_self, if_neg nonzero, if_neg notWithin, if_pos withinSucc,
              predecessor, adjacentNatSwap, if_neg nextNePivot, if_pos rfl]
            rfl
          · have aboveNext : steps + 1 < value := by omega
            have notWithinSucc : ¬value ≤ steps + 1 := by omega
            have valueNePivot : value ≠ steps := by omega
            simp only [-eq_self, -iff_self, if_neg zero, if_neg within, if_neg notWithinSucc, adjacentNatSwap,
              if_neg valueNePivot, if_neg atNext]
            rfl
end Purelib.Data.Nat.Permutation.Adjacent

end
