module
public import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Data.Nat.GCD.Resource.Fuel
import Purelib.Data.Rat.Fraction

@[expose] public section

/-!
# Calculation-size bounds for canonical fractions

These bounds describe the integer and natural records actually formed by the
reduction-aware operations.  They retain the RFAP-2 discipline that a final
normalization must not hide an unnecessarily inflated intermediate product.
-/

namespace Purelib.Data.Rat.Fraction

section
open Purelib.Data.Nat
/-- Estimate canonical addition fuel from its two retained gcd computations and fixed arithmetic overhead.

The first gcd reduces the denominator pair; the second reduces the raw sum numerator against the shared denominator
factor. Both fuel arguments are taken from the original executable addition intermediates. -/
def Resource.Fuel.addSteps (left right : Rational) : Nat :=
  GCD.Resource.Fuel.gcdFuel left.den right.den + GCD.Resource.Fuel.gcdFuel (addRaw left right).num.natAbs
    (additionCommon left right) + 8

/-- Estimate canonical multiplication fuel from its two cross-cancellation gcd computations and fixed overhead.

Each numerator magnitude is paired with the opposite denominator for cross-cancellation. The estimate adds the two
concrete gcd fuel bounds and the fixed remaining arithmetic cost. -/
def Resource.Fuel.mulSteps (left right : Rational) : Nat :=
  GCD.Resource.Fuel.gcdFuel left.num.natAbs right.den +
    GCD.Resource.Fuel.gcdFuel right.num.natAbs left.den + 8

end

/-- Assign one arithmetic step to canonical rational negation. -/
def Resource.Fuel.negSteps (_source : Rational) : Nat := 1
/-- Assign two arithmetic steps to total canonical reciprocal. -/
def Resource.Fuel.invSteps (_source : Rational) : Nat := 2

end Purelib.Data.Rat.Fraction

end
