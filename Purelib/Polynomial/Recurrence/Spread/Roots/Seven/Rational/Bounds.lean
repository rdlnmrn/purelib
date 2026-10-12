module
-- Exposed integer powers retain the owned executable monoid.
public import Purelib.Algebra.Monoid.Int
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.Ring.IntCast
import Purelib.Algebra.Group.Negation
import Purelib.Data.Rat.Fraction.Cast.Order
public import Purelib.Data.Rat.Fraction.Construction
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Rat.Fraction.Field
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring
public import Purelib.Data.Rat.Fraction.Literal

open Purelib.Data.Rat.Fraction.Literal (rationalLiteral rationalLiteral_mul_denominator)

open Purelib.Data.Rat

open Purelib.Algebra.Group in
attribute [local instance high] Negation.subNegZeroMonoid

section
@[expose] public section

/-!
# Divine Proportions, Example 14.10

The rational exclusion is the finite Eisenstein-at-seven argument applied to
the computable gcd-reduced numerator and denominator.  The three decimal
displays are retained as exact rational sign-change brackets; no completed
decimal field, real root, or limit object is introduced.
-/

namespace Purelib.Polynomial.Recurrence.Spread.Roots.Seven.Rational.Bounds

section

/-- Evaluate the rational cubic factor 7−56x+112x²−64x³ of the seventh spread polynomial. -/
def cubic (value : Fraction.Rational) :
  Fraction.Rational :=
  7 - 56 * value + 112 * value ^ 2 - 64 * value ^ 3

/-- The denominator-cleared integer numerator of the seventh-spread cubic at a displayed rational label. -/
public def clearedCubic (numerator : Int)
  (denominator : Nat) : Int :=
  7 * (denominator : Int) ^ 3 -
    56 * numerator * (denominator : Int) ^ 2 +
    112 * numerator ^ 2 * (denominator : Int) - 64 * numerator ^ 3

open Purelib.Polynomial
/-- Multiplying the cubic at a displayed fraction by the denominator cube yields the cast of its exact integer
numerator. -/
private theorem cubic_mul_denominatorCube
    (numerator : Int) (denominator : Nat) (positive : 0 < denominator) :
    cubic (rationalLiteral numerator
      denominator positive) *
        (denominator : Fraction.Rational) ^ 3 =
      (clearedCubic numerator denominator : Fraction.Rational) := open
        Purelib.Algebra in by
  let point := rationalLiteral numerator denominator positive
  have clear : point * (denominator : Fraction.Rational) = (numerator : Fraction.Rational) :=
    rationalLiteral_mul_denominator numerator denominator positive
  calc
    cubic point * (denominator : Fraction.Rational) ^ 3 =
        7 * (denominator : Fraction.Rational) ^ 3 -
          56 * (numerator : Fraction.Rational) * (denominator : Fraction.Rational) ^ 2 +
          112 * (numerator : Fraction.Rational) ^ 2 * (denominator : Fraction.Rational) -
          64 * (numerator : Fraction.Rational) ^ 3 := by
      unfold cubic
      rw [← clear]
      ring1
    _ = (clearedCubic numerator denominator : Fraction.Rational) := by
      unfold clearedCubic
      simp only [-eq_self, -iff_self, Ring.IntCast.sub, Ring.IntCast.add, Ring.IntCast.intCast_mul,
        Ring.IntCast.intCast_pow,
        Int.cast_natCast, Int.cast_ofNat]
      rfl

/-- A positive cleared numerator certifies positive cubic value at the displayed fraction with positive denominator. -/
public theorem cubic_positive
    (numerator : Int) (denominator : Nat) (positive : 0 < denominator)
    (clearedPositive :
      (0 : Fraction.Rational) < (clearedCubic numerator denominator :
        Fraction.Rational)) :
    0 < cubic (rationalLiteral numerator
      denominator positive) := by
  have productPositive :
      0 < cubic (rationalLiteral numerator
        denominator positive) *
        (denominator : Fraction.Rational) ^ 3 := by
    rw [cubic_mul_denominatorCube numerator denominator positive]
    exact clearedPositive
  have denominatorPositive :
      0 < (denominator : Fraction.Rational) ^ 3 :=
    Fraction.Order.Arithmetic.pow_pos_direct
      (Fraction.Cast.Order.natCast_lt_direct positive) 3
  exact Fraction.Order.Arithmetic.pos_of_mul_pos_right_direct
    (by simpa only [mul_comm] using productPositive) (Fraction.Order.Arithmetic.le_of_lt_direct denominatorPositive)

/-- A negative cleared numerator certifies negative cubic value at the displayed fraction with positive denominator. -/
public theorem cubic_negative
    (numerator : Int) (denominator : Nat) (positive : 0 < denominator)
    (clearedNegative :
      (clearedCubic numerator denominator : Fraction.Rational) < 0) :
    cubic (rationalLiteral numerator
      denominator positive) < 0 := by
  have productNegative :
      cubic (rationalLiteral numerator
        denominator positive) *
          (denominator : Fraction.Rational) ^ 3 < 0 := by
    rw [cubic_mul_denominatorCube numerator denominator positive]
    exact clearedNegative
  have denominatorPositive :
      0 < (denominator : Fraction.Rational) ^ 3 :=
    Fraction.Order.Arithmetic.pow_pos_direct
      (Fraction.Cast.Order.natCast_lt_direct positive) 3
  have negatedProductPositive :
      0 < (denominator : Fraction.Rational) ^ 3 *
        (-cubic (rationalLiteral numerator
          denominator positive)) := by
    calc
      (0 : Fraction.Rational) <
          -(cubic (rationalLiteral
            numerator denominator positive) *
            (denominator : Fraction.Rational) ^ 3) := by
        have positive := Fraction.Order.Arithmetic.neg_lt_neg_direct productNegative
        rewrite [neg_zero] at positive
        exact positive
      _ = (denominator : Fraction.Rational) ^ 3 *
          (-cubic (rationalLiteral
            numerator denominator positive)) := by
        ring1
  have negatedPositive :=
    Fraction.Order.Arithmetic.pos_of_mul_pos_right_direct
      negatedProductPositive (Fraction.Order.Arithmetic.le_of_lt_direct denominatorPositive)
  have negative := Fraction.Order.Arithmetic.neg_lt_neg_direct negatedPositive
  rewrite [neg_neg, neg_zero] at negative
  exact negative

end

end Purelib.Polynomial.Recurrence.Spread.Roots.Seven.Rational.Bounds

end
