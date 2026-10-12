module

public import Init.Data.Nat.Basic

namespace Purelib.Data.Nat.Subtraction

/-- Subtracting the left summand recovers the right summand.

The sum contains the whole subtrahend, so natural subtraction does not
discard any part of the remaining summand. -/
public theorem add_sub_cancel_left : ∀ left right : Nat, left + right - left = right
  | 0, right => by
      rw [Nat.zero_add, Nat.sub_zero]
  | left + 1, right => by
      rw [Nat.succ_add, Nat.succ_sub_succ]
      exact add_sub_cancel_left left right

/-- Subtracting a natural sum's retained right summand recovers the left summand.

Commuting the two original summands exposes the retained subtrahend on the
left. The subtraction operation then cancels that same natural summand. -/
public theorem add_sub_cancel_right (left right : Nat) : left + right - right = left := by
  rw [Nat.add_comm left right]
  exact add_sub_cancel_left right left

/-- Adding back a bounded subtrahend recovers the original natural number.

The retained inequality prevents natural subtraction from truncating the
original number below the subtrahend. -/
public theorem add_sub_of_le : ∀ {left right : Nat}, left ≤ right →
    left + (right - left) = right
  | 0, right, _ => by
      rw [Nat.sub_zero, Nat.zero_add]
  | left + 1, 0, bound => False.elim (Nat.not_succ_le_zero left bound)
  | left + 1, right + 1, bound => by
      rw [Nat.succ_sub_succ, Nat.succ_add]
      exact congrArg Nat.succ (add_sub_of_le (Nat.le_of_succ_le_succ bound))

/-- A bounded subtraction preserves the corresponding strict sum bound.

The lower bound permits reconstruction of the original value, while the
strict upper bound limits the remaining natural difference. -/
public theorem sub_lt_left_of_lt_add {left value right : Nat}
    (lower : left ≤ value) (upper : value < left + right) : value - left < right := by
  have reconstructed : left + (value - left) = value := add_sub_of_le lower
  have translated : left + (value - left) < left + right := reconstructed.symm ▸ upper
  exact Nat.lt_of_add_lt_add_left translated

/-- Successive natural subtractions equal subtraction of the summed subtrahends.

Both expressions use truncated natural subtraction, so the identity also
holds when the combined subtrahends exceed the original value. -/
public theorem sub_sub (value first second : Nat) :
    value - first - second = value - (first + second) := by
  induction second with
  | zero => rw [Nat.sub_zero, Nat.add_zero]
  | succ second ih =>
      rw [Nat.add_succ, Nat.sub_succ, Nat.add_succ, Nat.sub_succ, ih]

/-- Subtracting a natural upper bound truncates the difference to zero.

The retained bound states that the subtrahend contains the whole original
value, including equality and the zero-value case. -/
public theorem sub_eq_zero_of_le : ∀ {value subtrahend : Nat}, value ≤ subtrahend →
    value - subtrahend = 0
  | 0, subtrahend, _ => Nat.zero_sub subtrahend
  | value + 1, 0, bound => False.elim (Nat.not_succ_le_zero value bound)
  | value + 1, subtrahend + 1, bound => by
      rw [Nat.succ_sub_succ]
      exact sub_eq_zero_of_le (Nat.le_of_succ_le_succ bound)

/-- Adding back a bounded natural subtrahend on the right recovers the original value.

The supplied bound prevents truncation of the natural subtraction. Commuting the
retained summands then gives the reconstruction with the subtrahend on the right. -/
public theorem sub_add_cancel {value subtrahend : Nat} (bound : subtrahend ≤ value) :
    value - subtrahend + subtrahend = value := by
  rw [Nat.add_comm]
  exact add_sub_of_le bound

/-- A displayed natural sum determines its bounded subtraction.

The supplied equality identifies the whole value as its remainder plus
the retained subtrahend. Natural addition and subtraction recover that same remainder. -/
public theorem sub_eq_of_eq_add {value subtrahend remainder : Nat}
    (equation : value = remainder + subtrahend) : value - subtrahend = remainder := by
  rw [equation]
  exact add_sub_cancel_right remainder subtrahend

/-- Subtracting a strictly smaller natural value leaves a positive remainder.

If the displayed remainder were zero, reconstruction would identify the original
value with its strictly smaller subtrahend, contradicting the supplied strict bound. -/
public theorem sub_pos_of_lt {subtrahend value : Nat} (bound : subtrahend < value) :
    0 < value - subtrahend := by
  apply Nat.pos_of_ne_zero
  intro vanishes
  have reconstructed := add_sub_of_le (Nat.le_of_lt bound)
  rw [vanishes, Nat.add_zero] at reconstructed
  exact Nat.ne_of_lt bound reconstructed

/-- Successor commutes with a natural subtraction bounded by the original value.

The same retained bound prevents truncation before and after the successor step.
The original remainder therefore increases by exactly one. -/
public theorem succ_sub {subtrahend value : Nat} (bound : subtrahend ≤ value) :
    value + 1 - subtrahend = value - subtrahend + 1 := by
  have reconstructed := add_sub_of_le bound
  have displayed : value + 1 = (value - subtrahend + 1) + subtrahend := by
    rw [Nat.add_comm (value - subtrahend + 1) subtrahend,
      ← Nat.add_assoc, reconstructed]
  exact sub_eq_of_eq_add displayed

end Purelib.Data.Nat.Subtraction
