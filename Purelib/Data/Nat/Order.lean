module

import Mathlib.Data.List.Perm.Basic
import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Data.Nat.Init

/-!
# Direct scalar bounds and retained successor certificates

Natural comparisons, maxima and finite successor bounds are certified directly
from their original operations. The retained successor instances expose the
same constructor certificates through ordinary and scoped registration.
-/

namespace Purelib.Data.Nat

/-- Every natural successor supplies explicit evidence that it is nonzero.

The certificate follows from constructor disjointness. Ordinary imports and
the natural-number scope retain the same proof at the same priority. -/
public scoped instance (priority := 2000) successorNeZero {value : Nat} : NeZero (value + 1) :=
  ⟨fun impossible => Nat.noConfusion impossible⟩

/-- A nonzero natural predecessor certifies that its successor is at least two.

The predecessor's explicit nonzero evidence gives its positive bound.
Successor monotonicity transports that bound to the displayed numeral;
ordinary imports and the natural-number scope retain the same certificate. -/
public scoped instance (priority := 2000) successorAtLeastTwo {value : Nat} [nonzero : NeZero value] :
    Nat.AtLeastTwo (value + 1) :=
  ⟨Nat.succ_le_succ (Nat.pos_of_ne_zero nonzero.out)⟩

attribute [instance 2000] successorNeZero successorAtLeastTwo

end Purelib.Data.Nat

namespace Purelib.Data.Nat.Order

/-- Cancel a common natural factor from a strict product inequality.

If factor times left is strictly smaller than factor times right, then left is
strictly smaller than right; no separate positivity premise on the factor is
required. -/
public theorem lt_of_mul_lt_mul_left {factor left right : Nat}
    (strict : factor * left < factor * right) : left < right := by
  by_cases ordered : left < right
  · exact ordered
  · have reverse : right ≤ left := Nat.le_of_not_gt ordered
    have scaledReverse : factor * right ≤ factor * left :=
      Nat.mul_le_mul_left factor reverse
    exact False.elim ((Nat.not_le_of_gt strict) scaledReverse)

/-- A value below a half count has doubled value below the count's odd bound.

The doubled count is the successor of the supplied bound. Two occurrences of
an entry's successor fit below that count, leaving a strict bound for the same
original doubled entry after cancelling the retained successor. -/
public theorem two_mul_lt_of_lt_half {value count bound : Nat}
    (doubled : count + count = bound + 1) (below : value < count) :
    2 * value < bound := by
  have retained : value + value + 1 + 1 ≤ bound + 1 := by
    calc
      value + value + 1 + 1 = (value + 1) + (value + 1) :=
        ((congrArg (· + 1) (Nat.add_assoc value value 1)).trans
          (congrArg (fun term => value + term + 1) (Nat.add_comm value 1))).trans
            ((congrArg (· + 1) (Nat.add_assoc value 1 value).symm).trans
              (Nat.add_assoc (value + 1) value 1))
      _ ≤ count + count := Nat.add_le_add below below
      _ = bound + 1 := doubled
  exact (congrArg (· < bound) (Nat.two_mul value)).mpr
    (Nat.lt_of_succ_le (Nat.le_of_succ_le_succ retained))

/-- A true Boolean comparison with one certifies a natural number's positivity.

The supplied comparison excludes zero. Each remaining successor has its
original strict lower bound, without changing the Boolean comparison operation. -/
public theorem positive_of_ble_one (value : Nat) (positive : Nat.ble 1 value = true) :
    0 < value := by
  cases value with
  | zero => nomatch positive
  | succ value => exact Nat.zero_lt_succ value

/-- The original ordered maximum of two naturals equals their natural maximum.

Both operations use the same original decidable comparison and select the
same supplied argument. The equality preserves their existing operation
dictionaries while identifying the retained natural result. -/
public theorem max_eq_natMax (left right : Nat) : max left right = Nat.max left right := by
  by_cases ordered : left ≤ right
  · have actualChoice : max left right = right := by
      change (if left ≤ right then right else left) = right
      exact if_pos ordered
    have naturalChoice : Nat.max left right = right :=
      Nat.max_def.trans (if_pos ordered)
    exact actualChoice.trans naturalChoice.symm
  · have actualChoice : max left right = left := by
      change (if left ≤ right then right else left) = left
      exact if_neg ordered
    have naturalChoice : Nat.max left right = left :=
      Nat.max_def.trans (if_neg ordered)
    exact actualChoice.trans naturalChoice.symm

/-- The left natural argument does not exceed the displayed maximum. -/
public theorem le_max_left (left right : Nat) : left ≤ Nat.max left right := by
  change left ≤ if left ≤ right then right else left
  by_cases bound : left ≤ right
  · rw [if_pos bound]
    exact bound
  · rw [if_neg bound]
    exact Nat.le_refl left

/-- The right natural argument does not exceed the displayed maximum. -/
public theorem le_max_right (left right : Nat) : right ≤ Nat.max left right := by
  change right ≤ if left ≤ right then right else left
  by_cases bound : left ≤ right
  · rw [if_pos bound]
    exact Nat.le_refl right
  · rw [if_neg bound]
    cases Nat.le_total right left with
    | inl reverse => exact reverse
    | inr forward => exact (bound forward).elim

/-- Bounding both natural arguments bounds their displayed maximum.

The maximum chooses one of the two arguments by their decidable comparison;
the corresponding supplied bound proves the result. -/
public theorem max_le {left right bound : Nat} (leftBound : left ≤ bound)
    (rightBound : right ≤ bound) : Nat.max left right ≤ bound := by
  change (if left ≤ right then right else left) ≤ bound
  by_cases ordered : left ≤ right
  · rw [if_pos ordered]
    exact rightBound
  · rw [if_neg ordered]
    exact leftBound

/-- Swapping the natural arguments preserves their maximum. -/
public theorem max_comm (left right : Nat) : Nat.max left right = Nat.max right left :=
  Nat.le_antisymm
    (max_le (le_max_right right left) (le_max_left right left))
    (max_le (le_max_right left right) (le_max_left left right))

/-- Increasing both natural arguments cannot decrease their maximum.

Each retained argument bound transports its original maximum contribution
into the corresponding contribution of the larger maximum. -/
public theorem max_le_max {left right leftBound rightBound : Nat}
    (leftLe : left ≤ leftBound) (rightLe : right ≤ rightBound) :
    Nat.max left right ≤ Nat.max leftBound rightBound :=
  max_le (Nat.le_trans leftLe (le_max_left _ _))
    (Nat.le_trans rightLe (le_max_right _ _))

/-- Every natural number is bounded by its own square.

Zero gives equality. A positive displayed natural has a successor factor,
whose multiplication contains the original value as a retained summand. -/
public theorem le_mul_self (value : Nat) : value ≤ value * value := by
  cases value with
  | zero => exact Nat.le_refl 0
  | succ value =>
      rw [Nat.mul_succ]
      exact Nat.le_add_left _ _

/-- Adding two to a natural number gives a numeral that is at least two. -/
public theorem atLeastTwo_add_two (value : Nat) : Nat.AtLeastTwo (value + 2) :=
  ⟨Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le value))⟩

/-- The maximum with zero on the left retains the original natural value.

The original natural comparison selects the retained value because its
nonnegative bound is explicit. -/
public theorem zero_max (value : Nat) : Nat.max 0 value = value := by
  change (if 0 ≤ value then value else 0) = value
  rewrite [if_pos (Nat.zero_le value)]
  exact Eq.refl _

/-- The maximum with zero on the right retains the original natural value.

Commuting the same original maximum reduces the statement to its explicit
zero-left comparison certificate. -/
public theorem max_zero (value : Nat) : Nat.max value 0 = value :=
  (max_comm value 0).trans (zero_max value)

/-- Taking successors commutes with the maximum of two naturals.

Successor preserves and reflects the original scalar comparison. Both maxima
therefore select the same original argument, with one successor added. -/
public theorem succ_max_succ (left right : Nat) :
    Nat.max (Nat.succ left) (Nat.succ right) = Nat.succ (Nat.max left right) := by
  change (if Nat.succ left ≤ Nat.succ right then Nat.succ right else Nat.succ left) =
    Nat.succ (if left ≤ right then right else left)
  by_cases ordered : left ≤ right
  · rewrite [if_pos (Nat.succ_le_succ ordered), if_pos ordered]
    exact Eq.refl _
  · rewrite [if_neg (fun bound => ordered (Nat.le_of_succ_le_succ bound)), if_neg ordered]
    exact Eq.refl _

end Purelib.Data.Nat.Order
