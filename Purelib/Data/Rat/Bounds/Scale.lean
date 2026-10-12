module
import Purelib.Data.Nat.Order
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Data.Rat.Fraction.Order.Basic

/-!
# Rational scaling bounds

Nonnegative scalar factors preserve weak radius bounds. Positive
denominators and strict radius bounds supply the corresponding product estimates.
-/

namespace Purelib.Data.Rat.Bounds.Scale

open scoped Purelib.Data.Nat
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction
open Purelib.Algebra

/-- A nonnegative radius below a bound divided by one plus a nonnegative coefficient has coefficient product below that
bound.

Nonnegativity permits replacing the coefficient by one plus itself.
Strict comparison of the radius with the positive-denominator quotient bounds their product. -/
public theorem coefficient_mul_lt_of_radius_lt_div_add_one
    {coefficient radius bound : Fraction.Rational}
    (coefficientNonnegative : 0 ≤ coefficient)
    (radiusNonnegative : 0 ≤ radius)
    (small : radius < bound / (coefficient + 1)) :
    coefficient * radius < bound := by
  have denominatorPositive : 0 < coefficient + 1 := by
    calc
      0 < 1 := by decide
      _ ≤ coefficient + 1 :=
        add_le_add coefficientNonnegative (le_refl 1)
  calc
    coefficient * radius ≤ (coefficient + 1) * radius :=
      Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        (le_add_of_nonneg_right (by decide)) radiusNonnegative
    _ < (coefficient + 1) * (bound / (coefficient + 1)) :=
      Order.Arithmetic.mul_lt_mul_of_pos_left_direct
        denominatorPositive small
    _ = bound := by
      rw [Fraction.Field.mul_comm]
      exact Fraction.Field.div_mul_cancel_of_ne
        bound (coefficient + 1) denominatorPositive.ne'

/-- Division by six preserves weak rational comparison.

Both quotients use the same positive reciprocal of six, so the original
weak comparison transports directly under multiplication by that reciprocal. -/
public theorem div_six_mono {left right : Fraction.Rational}
    (order : left ≤ right) : left / 6 ≤ right / 6 := by
  simp only [Field.ExplicitField.div_eq_mul_inv]
  exact Order.Arithmetic.mul_le_mul_of_nonneg_right_direct order
    (Order.Field.inv_pos_direct
      (show (0 : Fraction.Rational) < 6 by decide)).le

end Purelib.Data.Rat.Bounds.Scale
