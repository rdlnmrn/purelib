module

import Purelib.Data.List.Map
import Purelib.Data.List.Range.Basic
import Purelib.Data.List.Append
import Purelib.Data.List.Membership
import Purelib.Data.Int.Order
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring

/-!
# Bounded integer intervals

The exact signed-magnitude list retains increasing nonnegative magnitudes
followed by their negatives. The finite closed-interval certificates retain
original equalities for every integer in their stated bounds.
-/

namespace Purelib.Data.Int.Interval

open Purelib.Data.List

/-- Every integer between minus two and one equals one of those four integers.

The retained closed lower and upper bounds exclude every other integer, and
each disjunct records the equality with its corresponding original integer. -/
public theorem int_cases_neg_two_to_one {value : Int}
    (lower : (-2 : Int) ≤ value) (upper : value ≤ 1) :
    value = -2 ∨ value = -1 ∨ value = 0 ∨ value = 1 := by omega0

/-- Every integer between minus three and two equals one of those six integers.

The retained closed lower and upper bounds exclude every other integer, and
each disjunct records the equality with its corresponding original integer. -/
public theorem int_cases_neg_three_to_two {value : Int}
    (lower : (-3 : Int) ≤ value) (upper : value ≤ 2) :
    value = -3 ∨ value = -2 ∨ value = -1 ∨ value = 0 ∨
      value = 1 ∨ value = 2 := by omega0

/-- Enumerate both signs of every natural magnitude through a displayed bound.

The list contains nonnegative magnitudes in increasing order followed by their
negatives. Both halves include zero, so zero occurs twice. -/
@[expose] public def signedComponents (bound : Nat) : List Int :=
  (List.range (bound + 1)).map (fun (magnitude : Nat) => (magnitude : Int)) ++
    (List.range (bound + 1)).map
      (fun (magnitude : Nat) => -(magnitude : Int))

/-- Every integer of bounded absolute value occurs in the signed magnitude list.

The supplied bound places the magnitude in the finite range; the sign of the integer
selects the corresponding half of the enumeration. -/
public theorem mem_signedComponents {component : Int} {bound : Nat}
    (bounded : component.natAbs ≤ bound) :
    component ∈ signedComponents bound := by
  cases component with
  | ofNat magnitude =>
      change magnitude ≤ bound at bounded
      apply Membership.mem_append.mpr
      exact Or.inl (Map.mem_map_of_mem
        (Range.Basic.mem_range.mpr (Nat.lt_succ_of_le bounded)))
  | negSucc predecessor =>
      let magnitude := predecessor + 1
      have magnitudeBound : magnitude ≤ bound := by
        change predecessor + 1 ≤ bound at bounded
        exact bounded
      have member := Map.mem_map_of_mem
        (f := fun magnitude : Nat => -(magnitude : Int))
        (Range.Basic.mem_range.mpr (Nat.lt_succ_of_le magnitudeBound))
      apply Membership.mem_append.mpr
      exact Or.inr member

/-- The signed magnitude list has twice the successor of its bound many entries.

The two original mapped ranges have the same retained successor length.
Their ordered concatenation therefore contributes that length twice. -/
@[simp] public theorem signedComponents_length (bound : Nat) :
    (signedComponents bound).length = 2 * (bound + 1) := by
  unfold signedComponents
  rewrite [Append.length_append, Map.length_map, Map.length_map,
    Range.Basic.length_range]
  ring1

end Purelib.Data.Int.Interval
