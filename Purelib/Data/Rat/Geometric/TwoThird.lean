module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Data.Rat.Fraction.Order.Basic
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring

section
@[expose] public section

/-!
# Low-to-high finite polynomials for transcendental identities

This is a deliberately small, executable polynomial kernel.  A polynomial is
only a displayed finite list of rational coefficients, stored from constant
term upward.  It exists to prove finite Taylor identities without importing a
sparse-polynomial or formal-power-series API.
-/

namespace Purelib.Data.Rat.Geometric.TwoThird

open Purelib.Data.Rat
/-- Compute the finite sum of twice each positive-index power of two thirds up to the supplied count.

The recursion starts with zero and appends the next exact rational power at each successor. The accompanying remainder
identity is a finite equality for every supplied count. -/
def twoThirdSum : Nat → Fraction.Rational
  | 0 => 0
  | count + 1 =>
      twoThirdSum count + 2 * (2 / 3 : Fraction.Rational) ^ (count + 1)

/-- The finite weighted two-third-power sum plus its exact geometric remainder is four. -/
theorem twoThirdSum_remainder : ∀ count,
    twoThirdSum count + 4 * (2 / 3 : Fraction.Rational) ^ count = 4
  | 0 => by rw [twoThirdSum, pow_zero]; decide
  | count + 1 => by
      rw [twoThirdSum, pow_succ]
      calc
        twoThirdSum count + 2 * (2 / 3 : Fraction.Rational) ^ (count + 1) +
            4 * ((2 / 3 : Fraction.Rational) ^ count * (2 / 3)) =
          twoThirdSum count +
            (2 * (2 / 3 : Fraction.Rational) + 4 * (2 / 3)) *
              (2 / 3 : Fraction.Rational) ^ count := by
            rw [pow_succ]
            ring1
        _ = twoThirdSum count + 4 * (2 / 3 : Fraction.Rational) ^ count := by
          rw [show (2 : Fraction.Rational) * (2 / 3) + 4 * (2 / 3) = 4 by decide]
        _ = 4 := twoThirdSum_remainder count

/-- Every finite weighted sum of the specified two-third powers is at most four. -/
theorem twoThirdSum_le_four (count : Nat) : twoThirdSum
  count ≤ 4 := by
  have remainderNonnegative :
      0 ≤ (4 : Fraction.Rational) * (2 / 3 : Fraction.Rational) ^ count :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (Fraction.Order.Arithmetic.pow_nonneg_direct (by decide) count)
  calc
    twoThirdSum count ≤
        twoThirdSum count + 4 * (2 / 3 : Fraction.Rational) ^ count :=
      le_add_of_nonneg_right remainderNonnegative
    _ = 4 := twoThirdSum_remainder count
end Purelib.Data.Rat.Geometric.TwoThird

end
