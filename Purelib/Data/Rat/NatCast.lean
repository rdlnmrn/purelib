module
import Purelib.Data.Rat.Fraction.Cast.Order
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Data.Rat.Fraction.Order.Basic

section
@[expose] public section

/-!
# Generated sample certificates for the horizontal quartic connector

This module connects the untrusted generated rational root data to the exact
prepared edges cached by the A-forward construction.  The common helpers keep
the proof cost linear in the 64 nonstationary horizontal edges.
-/

namespace Purelib.Data.Rat.NatCast

open Purelib.Data.Rat
/-- A positive natural number has positive canonical rational cast. -/
theorem horizontalNatPositive (n : Nat) (positive : 0 < n) :
    (0 : Fraction.Rational) < n :=
  Fraction.Cast.Order.natCast_pos_direct positive

/-- Every natural-number rational cast is nonnegative. -/
theorem horizontalNatNonnegative (n : Nat) : (0 : Fraction.Rational) <= n :=
  Fraction.Cast.Order.natCast_le_direct (Nat.zero_le n)

end Purelib.Data.Rat.NatCast

end
