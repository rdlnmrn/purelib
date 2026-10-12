module

import Purelib.Algebra.Group.Negation
import Purelib.Data.Rat.Fraction
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

/-!
# Rational quadratic lower bounds

Completing the square gives a global floor for a quadratic with a positive
leading coefficient. Selecting the polynomial or its negative yields a
nonnegative lower bound for the magnitude at every rational parameter.
-/

namespace Purelib.Polynomial.Quadratic.RationalBounds

open Purelib.Data.Rat

/-- Evaluate a rational quadratic in Horner form.

The three coefficients are retained in descending order. Each parameter is
multiplied twice, with the linear and constant terms added at their Horner stages. -/
@[expose] public def value (a b c parameter : Fraction.Rational) : Fraction.Rational :=
  (a * parameter + b) * parameter + c

/-- The constant obtained by completing the square in a rational quadratic.

Its lower-bound theorem requires a positive quadratic coefficient; this raw expression itself retains total rational
division. -/
@[expose] public def floor (a b c : Fraction.Rational) : Fraction.Rational := c - (b * b) / (4 * a)

/-- Clearing the denominator gives the completing-square identity.

A nonzero quadratic coefficient permits cancellation of the displayed
rational denominator. The identity holds at every supplied rational parameter. -/
public theorem scaled_completion (a b c parameter : Fraction.Rational) (nonzero : a ≠ 0) :
    (4 * a) * (value a b c parameter - floor a b c) = (2 * a * parameter + b) ^ 2 := by
  have cancelled := Fraction.Field.div_mul_cancel_of_ne (b * b) (4 * a)
    (Fraction.Field.mul_ne_zero_direct (by decide) nonzero)
  calc
    _ = 4 * a * ((a * parameter + b) * parameter) + ((b * b) / (4 * a)) * (4 * a) := by
      unfold value floor
      ring1
    _ = _ := by rw [cancelled]; ring1

/-- A positive quadratic coefficient makes the completed-square constant a lower bound.

The square remainder is nonnegative. Multiplication by the positive factor
four times the leading coefficient transfers that comparison to the polynomial value. -/
public theorem floor_le_value (a b c parameter : Fraction.Rational) (positive : 0 < a) :
    floor a b c ≤ value a b c parameter := by
  apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct (c := 4 * a) _ (Fraction.Order.Arithmetic.mul_pos_direct
    (by decide) positive)
  apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
  calc
    0 ≤ (2 * a * parameter + b) ^ 2 := Fraction.Order.Arithmetic.sq_nonneg_direct _
    _ = value a b c parameter * (4 * a) - floor a b c * (4 * a) := by
      rw [← scaled_completion a b c parameter (ne_of_gt positive)]
      ring1

/-- Select a nonnegative magnitude floor from the leading coefficient's sign.

A positive coefficient uses the polynomial's completed-square floor; a negative
coefficient uses its negation. A zero coefficient gives the floor zero. -/
@[expose] public def quadraticFloor (a b c : Fraction.Rational) : Fraction.Rational :=
  if 0 < a then max 0 (floor a b c)
  else if a < 0 then max 0 (floor (-a) (-b) (-c)) else 0

/-- The sign-selected quadratic floor is nonnegative.

Each nonzero leading-coefficient branch retains the maximum of zero and its
completed-square floor. The remaining branch retains zero itself. -/
public theorem quadraticFloor_nonnegative (a b c : Fraction.Rational) : 0 ≤ quadraticFloor a b c := by
  unfold quadraticFloor
  split
  · exact Fraction.Order.Basic.le_max_left _ _
  · split
    · exact Fraction.Order.Basic.le_max_left _ _
    · exact le_rfl

/-- The sign-selected floor bounds every rational quadratic magnitude below.

The positive leading-coefficient branch bounds the value itself, and the
negative branch bounds its negative. Both are bounded by the canonical rational magnitude. -/
public theorem quadraticFloor_le_abs (a b c parameter : Fraction.Rational) :
    quadraticFloor a b c ≤ Fraction.abs (value a b c parameter) := by
  unfold quadraticFloor
  split
  · rename_i positive
    exact Fraction.Order.Basic.max_le (Fraction.Order.Arithmetic.abs_nonneg_direct _) ((floor_le_value a b c parameter
      positive).trans (Fraction.Order.Basic.le_max_left _ _))
  · split
    · rename_i negative
      have positive : 0 < -a := by
        simpa only [neg_zero] using Fraction.Order.Arithmetic.neg_lt_neg_direct negative
      have bound := floor_le_value (-a) (-b) (-c) parameter positive
      have opposite : value (-a) (-b) (-c) parameter = -value a b c parameter := by
        unfold value
        ring1
      rw [opposite] at bound
      exact Fraction.Order.Basic.max_le (Fraction.Order.Arithmetic.abs_nonneg_direct _) (bound.trans
        (Fraction.Order.Basic.le_max_right _ _))
    · exact Fraction.Order.Arithmetic.abs_nonneg_direct _
end Purelib.Polynomial.Quadratic.RationalBounds
