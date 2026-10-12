module

import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Data.Rat.Fraction.Order.Basic
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Algebra.Group.Negation
import Purelib.Tactic.Ring

/-!
# Rational absolute-value certificates

The retained rational absolute value is the maximum of the original input
and its negation. Direct sign cases certify multiplication, nonzero values
and squares of that same operation.
-/

namespace Purelib.Data.Rat.Bounds.Abs

open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction

/-- A nonnegative rational is its retained absolute value.

Its negation is nonpositive. The original rational maximum therefore
selects the same input, including the zero boundary. -/
private theorem abs_of_nonnegative {value : Fraction.Rational}
    (nonnegative : 0 ≤ value) : Fraction.abs value = value := by
  change max value (-value) = value
  apply Order.Basic.max_eq_left
  have nonpositive := Order.Arithmetic.neg_le_neg_direct nonnegative
  rw [_root_.neg_zero] at nonpositive
  exact nonpositive.trans nonnegative

/-- A nonpositive rational has its negation as its retained absolute value.

Its negation is nonnegative. The original rational maximum selects that
same negated input, including the zero boundary. -/
private theorem abs_of_nonpositive {value : Fraction.Rational}
    (nonpositive : value ≤ 0) : Fraction.abs value = -value := by
  change max value (-value) = -value
  apply Order.Basic.max_eq_right
  have nonnegative := Order.Arithmetic.neg_le_neg_direct nonpositive
  rw [_root_.neg_zero] at nonnegative
  exact nonpositive.trans nonnegative

/-- The retained absolute value of a rational product is the product of its absolute values.

Each original input is negative, zero or positive. Direct rational product
signs select the same maximum branches and retain both original factors. -/
public theorem abs_mul_direct (x y : Fraction.Rational) :
    Fraction.abs (x * y) = Fraction.abs x * Fraction.abs y := by
  have absZero : Fraction.abs 0 = 0 := abs_of_nonnegative (le_refl 0)
  rcases lt_trichotomy x 0 with xNegative | rfl | xPositive <;>
    rcases lt_trichotomy y 0 with yNegative | rfl | yPositive
  · rw [abs_of_nonnegative (Order.Arithmetic.mul_pos_of_neg_of_neg_direct
        xNegative yNegative).le,
      abs_of_nonpositive xNegative.le, abs_of_nonpositive yNegative.le]
    ring1
  · rw [Fraction.Field.mul_zero_direct, absZero, Fraction.Field.mul_zero_direct]
  · rw [abs_of_nonpositive (Order.Arithmetic.mul_neg_of_neg_of_pos_direct
        xNegative yPositive).le,
      abs_of_nonpositive xNegative.le, abs_of_nonnegative yPositive.le]
    ring1
  · rw [Fraction.Field.zero_mul_direct, absZero, Fraction.Field.zero_mul_direct]
  · rw [Fraction.Field.zero_mul_direct, absZero, Fraction.Field.zero_mul_direct]
  · rw [Fraction.Field.zero_mul_direct, absZero, Fraction.Field.zero_mul_direct]
  · rw [abs_of_nonpositive (Order.Arithmetic.mul_neg_of_pos_of_neg_direct
        xPositive yNegative).le,
      abs_of_nonnegative xPositive.le, abs_of_nonpositive yNegative.le]
    ring1
  · rw [Fraction.Field.mul_zero_direct, absZero, Fraction.Field.mul_zero_direct]
  · rw [abs_of_nonnegative (Order.Arithmetic.mul_pos_direct xPositive yPositive).le,
      abs_of_nonnegative xPositive.le, abs_of_nonnegative yPositive.le]

/-- The retained absolute value of a nonzero rational is nonzero.

The negative and positive branches preserve respectively the negated and
original input. Negation can vanish only when that same input vanishes. -/
public theorem abs_ne_zero_direct {x : Fraction.Rational} (nonzero : x ≠ 0) :
    Fraction.abs x ≠ 0 := by
  rcases lt_trichotomy x 0 with negative | rfl | positive
  · rw [abs_of_nonpositive negative.le]
    intro negatedZero
    apply nonzero
    calc
      x = -(-x) := by ring1
      _ = -0 := by rw [negatedZero]
      _ = 0 := by ring1
  · exact (nonzero rfl).elim
  · rw [abs_of_nonnegative positive.le]
    exact nonzero

/-- Taking the retained rational absolute value leaves its square unchanged.

The original maximum selects the input or its negation according to its
sign. Squaring either selected rational gives the original input square. -/
public theorem abs_sq_direct (x : Fraction.Rational) : Fraction.abs x ^ 2 = x ^ 2 := by
  rcases lt_trichotomy x 0 with negative | rfl | positive
  · rw [abs_of_nonpositive negative.le]
    ring1
  · rw [abs_of_nonnegative (le_refl 0)]
  · rw [abs_of_nonnegative positive.le]

end Purelib.Data.Rat.Bounds.Abs
