module
import Purelib.Data.Nat.Order
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Data.Rat.Fraction.Order.Basic
public import Purelib.Data.Rat.Fraction.Field

open scoped Purelib.Data.Nat

/-!
# Rational half-coordinate negation bounds

Negation reverses rational order at the retained positive and negative half
boundaries. These equivalences keep weak and strict endpoints distinct.
-/

namespace Purelib.Data.Rat.Bounds.Half

open Purelib.Data.Rat
open Fraction.Order
open Purelib.Algebra.Field (ExplicitField)

/-- Negative one divided by two is the negation of one half.

Division by the same rational denominator is multiplication by its reciprocal.
Negating the numerator therefore negates the entire rational quotient. -/
private theorem neg_one_div_two :
    (-1 / 2 : Fraction.Rational) = -(1 / 2) := by
  rw [ExplicitField.div_eq_mul_inv,
    ExplicitField.div_eq_mul_inv, neg_mul]

/-- One half is at most a rational negation exactly when the original rational is at most negative one half.

Negation reverses the retained weak comparison in both directions, and
negative one divided by two agrees with the negation of one half. -/
public theorem half_le_neg_iff
    (value : Fraction.Rational) :
    (1 / 2 : Fraction.Rational) ≤ -value
      ↔ value ≤ -1 / 2 := by
  rw [neg_one_div_two]
  constructor
  · intro h
    simpa only [neg_neg] using Arithmetic.neg_le_neg_direct h
  · intro h
    simpa only [neg_neg] using Arithmetic.neg_le_neg_direct h

/-- Negative one half is strictly below a rational negation exactly when the original rational is below one half.

Negation reverses the retained strict comparison in both directions, and
negative one divided by two agrees with the negation of one half. -/
public theorem neg_half_lt_neg_iff
    (value : Fraction.Rational) :
    (-1 / 2 : Fraction.Rational) < -value
      ↔ value < 1 / 2 := by
  rw [neg_one_div_two]
  constructor
  · intro h
    simpa only [neg_neg] using Arithmetic.neg_lt_neg_direct h
  · intro h
    exact Arithmetic.neg_lt_neg_direct h

/-- A rational negation is below one half exactly when the original rational is above negative one half.

Negation reverses the retained strict comparison in both directions, and
negative one divided by two agrees with the negation of one half. -/
public theorem neg_lt_half_iff
    (value : Fraction.Rational) :
    -value < (1 / 2 : Fraction.Rational)
      ↔ -1 / 2 < value := by
  rw [neg_one_div_two]
  constructor
  · intro h
    simpa only [neg_neg] using Arithmetic.neg_lt_neg_direct h
  · intro h
    simpa only [neg_neg] using Arithmetic.neg_lt_neg_direct h

end Purelib.Data.Rat.Bounds.Half
