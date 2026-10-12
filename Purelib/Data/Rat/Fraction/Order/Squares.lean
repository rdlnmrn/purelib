module

import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Data.Rat.Fraction.Field
public import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring
import Purelib.Algebra.Group.Negation

open Purelib.Algebra.Group in
attribute [local instance high] Negation.subNegZeroMonoid

/-!
# Rational square comparison

The square of a rational difference certifies the comparison between twice
the original product and the sum of the original squares.
-/

namespace Purelib.Data.Rat.Fraction.Order.Squares

open Purelib.Data.Rat
open Fraction.Order

/-- Twice the product of two rationals is at most the sum of their squares.

The upper bound minus the product is the square of the original difference.
Its nonnegativity gives the comparison through direct rational subtraction order. -/
public theorem twice_mul_le_sq_add_sq (left right : Fraction.Rational) :
    2 * left * right ≤ left * left + right * right := by
  apply Arithmetic.le_of_sub_nonneg_direct
  calc
    0 ≤ (left - right) ^ 2 := Arithmetic.sq_nonneg_direct _
    _ = (left * left + right * right) - 2 * left * right := by ring1

end Purelib.Data.Rat.Fraction.Order.Squares
