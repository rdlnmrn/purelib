module
public import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction

section
@[expose] public section

/-!
# Executable, limit-free differential laws for the logarithm

This module works with the finite local coordinate `log(1+u)`, on the
displayed rational disk `normSq u ≤ 1/4`.  Its relative forms and derivative
are finite alternating sums.  The reciprocal derivative law is expressed by
an exact finite geometric remainder and then by finite-request operational
equivalence.  No infinitesimal, limit, infinite series, or global logarithm
branch is introduced.
-/

namespace Purelib.Data.Rat.Alternating

open Purelib.Data.Rat in
/-- Compute the rational alternating sign by starting at one and negating at each successor.

The finite recursion returns one at zero and applies canonical rational negation once per successor, retaining the exact
alternating sequence without a parity conversion. -/
def alternatingSign : Nat → Fraction.Rational
  | 0 => 1
  | index + 1 => -alternatingSign index
end Purelib.Data.Rat.Alternating

end
