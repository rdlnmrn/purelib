module
import Purelib.Data.Nat.Order
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

/-! Exact rational fractional scaling and strict fraction bounds. -/

namespace Purelib.Data.Rat.Bounds.Fraction

open Purelib.Data.Rat
open Purelib.Algebra
open scoped Purelib.Data.Nat

/-- Sixteen times one sixteenth of a rational recovers that rational. -/
public theorem sixteenths (target : Fraction.Rational) :
    16 * (target / 16) = target := by
  rw [Fraction.Field.mul_comm]
  exact Fraction.Field.div_mul_cancel_of_ne target 16 (by decide)

/-- Ten sixteenths of a positive rational are strictly below the original rational.

Multiplication by the positive input transports the exact scalar comparison
`10/16 < 1`; the retained division and multiplication laws identify the result. -/
public theorem ten_sixteenths_lt {target : Fraction.Rational}
    (positive : 0 < target) : 10 * (target / 16) < target := by
  have scalarOrder : (10 / 16 : Fraction.Rational) < 1 := by decide
  have scaled := Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct
    scalarOrder positive
  calc
    10 * (target / 16) = (10 / 16 : Fraction.Rational) * target := by
      rw [Field.ExplicitField.div_eq_mul_inv,
        Field.ExplicitField.div_eq_mul_inv]
      ring1
    _ < 1 * target := scaled
    _ = target := Fraction.Field.one_mul _

/-- Twenty-four thirty-seconds of a positive rational are strictly below the original rational.

Multiplication by the positive input transports the exact scalar comparison
`24/32 < 1`; the retained division and multiplication laws identify the result. -/
public theorem twenty_four_thirty_seconds_lt {target : Fraction.Rational}
    (positive : 0 < target) : 24 * (target / 32) < target := by
  have scalarOrder : (24 / 32 : Fraction.Rational) < 1 := by decide
  have scaled := Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct
    scalarOrder positive
  calc
    24 * (target / 32) = (24 / 32 : Fraction.Rational) * target := by
      rw [Field.ExplicitField.div_eq_mul_inv,
        Field.ExplicitField.div_eq_mul_inv]
      ring1
    _ < 1 * target := scaled
    _ = target := Fraction.Field.one_mul _

end Purelib.Data.Rat.Bounds.Fraction
