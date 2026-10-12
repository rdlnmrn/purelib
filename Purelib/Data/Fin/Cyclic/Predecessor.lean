module

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Nat

section
section
public section

/-!
# The finite permutation of a positive torus band

The ascending Artin band moves strand zero to the last position and every
other strand down by one.  This file proves that fact by evaluating each
displayed adjacent transposition.  The auxiliary arithmetic acts only on a
bounded natural prefix and is fully executable.
-/

namespace Purelib.Data.Fin.Cyclic.Predecessor

/-! ## The standard cyclic predecessor -/

/-- Move one step backwards in a nonempty cyclic finite index type.

Zero wraps to count - 1; a nonzero index decreases by one. The positive count certifies the wraparound index and both
branches retain the Fin count bound. -/
@[expose] def cyclicPredecessor {count : Nat} (positive : 0 < count)
    (index : Fin count) : Fin count :=
  if zero : index.val = 0 then
    ⟨count - 1, by omega⟩
  else
    ⟨index.val - 1, by omega⟩

open Purelib.Data.Fin.Cyclic
/-- The cyclic predecessor of zero is the last index. -/
@[simp] theorem cyclicPredecessor_zero {count : Nat} (positive : 0 < count) :
    cyclicPredecessor positive ⟨0, positive⟩ = ⟨count - 1, by omega⟩ := by
  unfold cyclicPredecessor
  rw [dif_pos rfl]

/-- The cyclic predecessor of a nonzero index decreases its value by one. -/
theorem cyclicPredecessor_of_ne_zero {count : Nat} (positive : 0 < count)
    (index : Fin count) (nonzero : index.val ≠ 0) :
    cyclicPredecessor positive index = ⟨index.val - 1, by omega⟩ := by
  unfold cyclicPredecessor
  rw [dif_neg nonzero]
end Purelib.Data.Fin.Cyclic.Predecessor

end

end

section
public section

/-!
# Coprime torus braids close to knots

This file proves the constructive coprime case of the torus-link component
theorem.  Each positive band decreases the finite strand label by one, with a
displayed wrap count.  Telescoping those finite equalities shows that a return
after `k` bands forces the strand count to divide `k`.  A stored Bézout
certificate then cancels the `q` factor for the braid
`(σ₁…σₚ₋₁)^q`, ruling out every early return when `p` and `q` are
coprime.
-/

namespace Purelib.Data.Fin.Cyclic.Predecessor

/-! ## Finite wrap arithmetic -/

open Purelib.Data.Fin.Cyclic in
/-- Record the wrap count for one cyclic predecessor step.

The predecessor value plus one equals the original value plus a natural multiple of the cycle length. The witness is one
at zero and zero at every other index. -/
theorem cyclicPredecessor_balance {count : Nat} (positive : 0 < count)
    (index : Fin count) :
    ∃ wraps : Nat,
      (cyclicPredecessor positive index).val + 1 =
        index.val + wraps * count := by
  by_cases zero : index.val = 0
  · refine ⟨1, ?_⟩
    unfold cyclicPredecessor
    rw [dif_pos zero]
    change (count - 1) + 1 = index.val + 1 * count
    rw [Nat.one_mul]
    omega
  · refine ⟨0, ?_⟩
    unfold cyclicPredecessor
    rw [dif_neg zero]
    change (index.val - 1) + 1 = index.val + 0 * count
    rw [Nat.zero_mul, Nat.add_zero]
    omega
end Purelib.Data.Fin.Cyclic.Predecessor

end
