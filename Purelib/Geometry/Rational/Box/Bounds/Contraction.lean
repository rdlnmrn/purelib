module
public import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Geometry.Rational.Box.Dimensions
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Data.Rat

open Purelib.Geometry

section
/-!
# Choice-free raw-winding safe subdivision

Central-third eliminant-certified cuts split a clear box into four clear
children.  A finite first-nonzero scan retains raw winding while every round
contracts squared diagonal by `4/9`.
-/

@[expose] public section

namespace Purelib.Geometry.Rational.Box.Bounds.Contraction

/-- Contracting both side lengths by at least two thirds contracts the squared diagonal by at least four ninths. -/
theorem diagonalSq_le_four_ninths {child parent :
  Rational.Box}
    (widthX : child.widthX ≤ (2 / 3 : Fraction.Rational) * parent.widthX)
    (widthY : child.widthY ≤ (2 / 3 : Fraction.Rational) * parent.widthY) :
    child.diagonalSq ≤ (4 / 9 : Fraction.Rational) * parent.diagonalSq := by
  have childXNonnegative := child.widthX_nonneg
  have childYNonnegative := child.widthY_nonneg
  have scaledXNonnegative :
      0 ≤ (2 / 3 : Fraction.Rational) * parent.widthX :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      parent.widthX_nonneg
  have scaledYNonnegative :
      0 ≤ (2 / 3 : Fraction.Rational) * parent.widthY :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      parent.widthY_nonneg
  have squareX : child.widthX ^ 2 ≤
      ((2 / 3 : Fraction.Rational) * parent.widthX) ^ 2 := by
    rw [pow_two, pow_two]
    exact Fraction.Order.Arithmetic.mul_le_mul_direct widthX widthX
      childXNonnegative scaledXNonnegative
  have squareY : child.widthY ^ 2 ≤
      ((2 / 3 : Fraction.Rational) * parent.widthY) ^ 2 := by
    rw [pow_two, pow_two]
    exact Fraction.Order.Arithmetic.mul_le_mul_direct widthY widthY
      childYNonnegative scaledYNonnegative
  have scaleSquare : (2 / 3 : Fraction.Rational) ^ 2 = 4 / 9 := by
    decide
  calc
    child.diagonalSq = child.widthX ^ 2 + child.widthY ^ 2 := rfl
    _ ≤ ((2 / 3 : Fraction.Rational) * parent.widthX) ^ 2 +
          ((2 / 3 : Fraction.Rational) * parent.widthY) ^ 2 :=
      add_le_add squareX squareY
    _ = (2 / 3 : Fraction.Rational) ^ 2 *
          (parent.widthX ^ 2 + parent.widthY ^ 2) := by
      ring1
    _ = (4 / 9 : Fraction.Rational) * parent.diagonalSq := by
      rw [scaleSquare]
      rfl
end Purelib.Geometry.Rational.Box.Bounds.Contraction

end
