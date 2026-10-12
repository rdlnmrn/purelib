module
import Purelib.Data.Nat.Order
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Data.Rat.Fraction.Order.Basic
public import Purelib.Data.Rat.Fraction.Field

/-! Exact rational bounds for doubled sums. -/

namespace Purelib.Data.Rat.Bounds.Sum

open Purelib.Data.Rat
open Purelib.Algebra
open scoped Purelib.Data.Nat

/-- A weak first-coordinate bound and strict second-coordinate bound give a strict comparison of the doubled sums.

Translation first combines the retained weak and strict comparisons into
a strict sum bound. Multiplication by the positive rational two preserves it. -/
public theorem twice_add_lt_twice_add_of_le_of_lt
    {a b c d : Fraction.Rational} (first : a ≤ c) (second : b < d) :
    2 * (a + b) < 2 * (c + d) := by
  apply Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide)
  exact
    (Fraction.Order.Arithmetic.add_le_add_right_direct first b).trans_lt
      (Fraction.Order.Arithmetic.add_lt_add_left_direct second c)

end Purelib.Data.Rat.Bounds.Sum
