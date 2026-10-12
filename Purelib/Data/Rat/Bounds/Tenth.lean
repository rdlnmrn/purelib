module
import Purelib.Data.Nat.Order
import Purelib.Data.Rat.Fraction
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Data.Rat.Fraction.Order.Basic

open scoped Purelib.Data.Nat

/-!
# Rational tenth bounds

The rational numeral ten is positive. Dividing a positive rational by this
fixed denominator gives a strictly smaller rational value.
-/

namespace Purelib.Data.Rat.Bounds.Tenth

open Purelib.Data.Rat
open Fraction.Order

/-- The canonical rational numeral ten is strictly positive. -/
public theorem ten_pos : (0 : Fraction.Rational) < 10 := by decide

/-- One tenth of a positive rational is strictly smaller than the original rational.

The positive denominator transports the comparison to multiplication by ten.
The strict bound then follows from the retained input positivity and `1 < 10`. -/
public theorem div_ten_lt_self {value : Fraction.Rational} (positive : 0 < value) :
    value / 10 < value := by
  apply (Field.div_lt_iff_pos ten_pos).2
  calc
    value = value * 1 :=
      (Fraction.Field.mul_one_direct value).symm
    _ < value * 10 :=
      Arithmetic.mul_lt_mul_of_pos_left_direct
        positive (by decide)

end Purelib.Data.Rat.Bounds.Tenth
