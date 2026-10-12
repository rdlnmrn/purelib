module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Cast.Order

public import Purelib.Data.Rat.Fraction.Field
public import Purelib.Data.Rat.Fraction.Order.Basic

section
@[expose] public section

/-!
# Positive natural casts to canonical rationals

The owned natural cast preserves strict positivity in the exact rational
order, with its original positive natural-number witness.
-/

namespace Purelib.Data.Rat.Cast.Order

open Purelib.Data.Rat in
/-- A positive natural number has positive canonical rational cast. -/
public theorem natCast_pos {n : Nat} (positive : 0 < n) :
    (0 : Fraction.Rational) < (n : Nat) := by
  exact Fraction.Cast.Order.natCast_pos_direct positive

end Purelib.Data.Rat.Cast.Order

end
