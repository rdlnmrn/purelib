module
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Rat.Fraction.Cast.Order
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Data.Rat.Fraction.Order.Basic

/-!
# Squared reciprocals of natural casts

Successor naturals give positive rational denominators with reciprocal square
at most one. A retained lower bound of two sharpens that bound to one quarter.
-/

open Purelib.Algebra
open Purelib.Data.Rat

namespace Purelib.Data.Rat.Bounds.ReciprocalNatural

/-- The squared reciprocal of a positive successor natural cast is at most one.

The successor cast is positive and at least one. Taking its reciprocal and
squaring therefore gives a nonnegative value no greater than one. -/
public theorem reciprocalNatSq_le_one (index : Nat) :
    (1 / ((index + 1 : Nat) : Fraction.Rational)) ^ 2 ≤ 1 := by
  have denominatorPositive :
      0 < ((index + 1 : Nat) : Fraction.Rational) :=
    Fraction.Cast.Order.natCast_pos_direct (by omega)
  have oneLeDenominator :
      (1 : Fraction.Rational) ≤ ((index + 1 : Nat) : Fraction.Rational) :=
    Fraction.Cast.Order.natCast_le_direct
      (show 1 ≤ index + 1 by omega)
  have inverseOrder :
      (((index + 1 : Nat) : Fraction.Rational))⁻¹ ≤ (1 : Fraction.Rational)⁻¹ :=
    Fraction.Order.Field.inv_le_inv_of_pos_direct (by decide)
      oneLeDenominator
  have inverseNonnegative :
      0 ≤ (((index + 1 : Nat) : Fraction.Rational))⁻¹ :=
    (Fraction.Order.Field.inv_pos_direct denominatorPositive).le
  have squared := Fraction.Order.Arithmetic.pow_le_pow_direct
    inverseNonnegative inverseOrder 2
  rw [show (1 : Fraction.Rational)⁻¹ = 1 by decide, one_pow] at squared
  simpa only [Field.ExplicitField.div_eq_mul_inv,
    Fraction.Field.one_mul] using squared

/-- The squared reciprocal of a natural cast at least two is at most one quarter.

The retained natural lower bound transports to the original rational cast.
Reciprocal comparison and a nonnegative square give the exact quarter bound. -/
public theorem reciprocal_nat_sq_le_quarter {denominator : Nat}
    (atLeastTwo : 2 ≤ denominator) :
    (1 / (denominator : Fraction.Rational)) ^ 2 ≤ (1 / 4 : Fraction.Rational) := by
  have denominatorOrder : (2 : Fraction.Rational) ≤ (denominator : Fraction.Rational) :=
    Fraction.Cast.Order.natCast_le_direct atLeastTwo
  have inverseOrder : (denominator : Fraction.Rational)⁻¹ ≤ (2 : Fraction.Rational)⁻¹ :=
    Fraction.Order.Field.inv_le_inv_of_pos_direct (by decide)
      denominatorOrder
  have inverseNonnegative : 0 ≤ (denominator : Fraction.Rational)⁻¹ :=
    (Fraction.Order.Field.inv_pos_direct
      (Fraction.Cast.Order.natCast_pos_direct (by omega))).le
  have squareOrder := Fraction.Order.Arithmetic.pow_le_pow_direct
    inverseNonnegative inverseOrder 2
  calc
    (1 / (denominator : Fraction.Rational)) ^ 2 =
        ((denominator : Fraction.Rational)⁻¹) ^ 2 := by
      rw [Field.ExplicitField.div_eq_mul_inv,
        Fraction.Field.one_mul]
    _ ≤ ((2 : Fraction.Rational)⁻¹) ^ 2 := squareOrder
    _ = 1 / 4 := by decide

end Purelib.Data.Rat.Bounds.ReciprocalNatural
