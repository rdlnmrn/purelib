module

import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Data.Rat.Fraction.Order.Basic

/-!
# Rational maximum under nonnegative scaling

Multiplication by one displayed nonnegative rational preserves the comparison
that chooses a finite maximum. The original inputs and factor remain unchanged.
-/

namespace Purelib.Data.Rat

open Fraction.Order

/-- Multiplying by a nonnegative rational commutes with the maximum of two rationals.

The original weak comparison selects the larger input, and direct rational
multiplication preserves that comparison after scaling by the supplied factor. -/
public theorem max_mul_of_nonnegative_direct
    (left right factor : Fraction.Rational) (factorNonnegative : 0 ≤ factor) :
    max (left * factor) (right * factor) =
      max left right * factor := by
  by_cases order : left ≤ right
  · have scaled : left * factor ≤ right * factor :=
      Arithmetic.mul_le_mul_of_nonneg_right_direct order factorNonnegative
    rw [Basic.max_eq_right order, Basic.max_eq_right scaled]
  · have reverse : right ≤ left := (Arithmetic.lt_of_not_ge_direct order).le
    have scaled : right * factor ≤ left * factor :=
      Arithmetic.mul_le_mul_of_nonneg_right_direct reverse factorNonnegative
    rw [Basic.max_eq_left reverse, Basic.max_eq_left scaled]

end Purelib.Data.Rat
