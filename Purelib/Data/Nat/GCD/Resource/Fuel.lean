module

@[expose] public section

/-!
# Calculation-size bounds for canonical fractions

These bounds describe the integer and natural records actually formed by the
reduction-aware operations.  They retain the RFAP-2 discipline that a final
normalization must not hide an unnecessarily inflated intermediate product.
-/

namespace Purelib.Data.Nat.GCD.Resource.Fuel

/-- Supply the second gcd input plus one as its finite recursion fuel. -/
def gcdFuel (_leftInput rightInput : Nat) : Nat := rightInput + 1

open Purelib.Data.Nat.GCD.Resource in
/-- The supplied gcd recursion fuel is strictly positive. -/
theorem gcdFuel_pos (leftInput rightInput : Nat) :
    0 < gcdFuel leftInput rightInput :=
  Nat.zero_lt_succ rightInput
end Purelib.Data.Nat.GCD.Resource.Fuel

end
