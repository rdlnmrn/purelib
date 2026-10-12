module

import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.QuotientFreeOmega
public import Purelib.Data.Rat.Fraction.Field
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

/-!
# Rational quadratic bounds on a unit square

The original radial quadratic retains its two coordinate values and four
coefficients. Explicit corner and slope inequalities determine positivity
on the stated finite coordinate region.
-/

namespace Purelib.Polynomial.Multivariate.Rational.QuadraticBox

open Purelib.Data.Rat
open Purelib.Polynomial

/-- Evaluate the rational quadratic A(x²+y²)+Bx+Cy+D at two displayed coordinates.

The original finite expression retains its radial coefficient, both linear
coefficients, constant and displayed coordinates. -/
@[expose] public def tablePolynomial
    (A B C D x y : Fraction.Rational) : Fraction.Rational :=
  A * (x ^ 2 + y ^ 2) + B * x + C * y + D

/-- A concave radial quadratic is positive on the half-open unit square under the retained corner conditions.

The origin value is positive, the other corner values are nonnegative, and the shared quadratic coefficient is
nonpositive. -/
public theorem concave_table_positive
    {A B C D x y : Fraction.Rational}
    (alphaNonpositive : A ≤ 0)
    (originPositive : 0 < D)
    (realCornerNonnegative : 0 ≤ A + B + D)
    (imagCornerNonnegative : 0 ≤ A + C + D)
    (farCornerNonnegative : 0 ≤ 2 * A + B + C + D)
    (realNonnegative : 0 ≤ x) (realSmall : x < 1)
    (imagNonnegative : 0 ≤ y) (imagSmall : y < 1) :
    0 < Multivariate.Rational.QuadraticBox.tablePolynomial A B C D x y := by
  have oneMinusRealPositive : 0 < 1 - x :=
    Fraction.Order.Arithmetic.sub_pos_direct realSmall
  have oneMinusImagPositive : 0 < 1 - y :=
    Fraction.Order.Arithmetic.sub_pos_direct imagSmall
  have originTermPositive : 0 < D * (1 - x) * (1 - y) :=
    Fraction.Order.Arithmetic.mul_pos_direct
      (Fraction.Order.Arithmetic.mul_pos_direct originPositive
        oneMinusRealPositive)
      oneMinusImagPositive
  have realCornerTermNonnegative :
      0 ≤ (A + B + D) * x * (1 - y) :=
    Fraction.Order.Arithmetic.mul_nonneg_direct
      (Fraction.Order.Arithmetic.mul_nonneg_direct
        realCornerNonnegative realNonnegative)
      oneMinusImagPositive.le
  have imagCornerTermNonnegative :
      0 ≤ (A + C + D) * (1 - x) * y :=
    Fraction.Order.Arithmetic.mul_nonneg_direct
      (Fraction.Order.Arithmetic.mul_nonneg_direct
        imagCornerNonnegative oneMinusRealPositive.le)
      imagNonnegative
  have farCornerTermNonnegative :
      0 ≤ (2 * A + B + C + D) * x * y :=
    Fraction.Order.Arithmetic.mul_nonneg_direct
      (Fraction.Order.Arithmetic.mul_nonneg_direct
        farCornerNonnegative realNonnegative)
      imagNonnegative
  have negativeAlphaNonnegative : 0 ≤ -A := by
    have difference := Fraction.Order.Arithmetic.sub_nonneg_direct
      alphaNonpositive
    rw [show (0 : Fraction.Rational) - A = -A by ring1] at difference
    exact difference
  have interiorSumNonnegative :
      0 ≤ x * (1 - x) + y * (1 - y) :=
    add_nonneg
      (Fraction.Order.Arithmetic.mul_nonneg_direct realNonnegative
        oneMinusRealPositive.le)
      (Fraction.Order.Arithmetic.mul_nonneg_direct imagNonnegative
        oneMinusImagPositive.le)
  have correctionNonnegative :
      0 ≤ (-A) * (x * (1 - x) + y * (1 - y)) :=
    Fraction.Order.Arithmetic.mul_nonneg_direct negativeAlphaNonnegative
      interiorSumNonnegative
  have remainingNonnegative :
      0 ≤ (A + B + D) * x * (1 - y) +
        (A + C + D) * (1 - x) * y +
        (2 * A + B + C + D) * x * y +
        (-A) * (x * (1 - x) + y * (1 - y)) :=
    add_nonneg
      (add_nonneg (add_nonneg realCornerTermNonnegative
        imagCornerTermNonnegative) farCornerTermNonnegative)
      correctionNonnegative
  calc
    0 < D * (1 - x) * (1 - y) +
        ((A + B + D) * x * (1 - y) +
          (A + C + D) * (1 - x) * y +
          (2 * A + B + C + D) * x * y +
          (-A) * (x * (1 - x) + y * (1 - y))) :=
      Fraction.Order.Arithmetic.add_pos_of_pos_of_nonneg_direct originTermPositive remainingNonnegative
    _ = Multivariate.Rational.QuadraticBox.tablePolynomial A B C D x y := by
      unfold tablePolynomial
      ring1

/-- The scalar term x(Ax+B) is nonnegative when x, A and B are nonnegative.

The original real coordinate and both retained scalar coefficients are
nonnegative, so each factor has the same nonnegative sign. -/
private theorem convex_x_term_nonnegative
    {A B x : Fraction.Rational} (alphaNonnegative : 0 ≤ A)
    (betaNonnegative : 0 ≤ B) (realNonnegative : 0 ≤ x) :
    0 ≤ x * (A * x + B) := by
  exact Fraction.Order.Arithmetic.mul_nonneg_direct realNonnegative
    (add_nonneg
      (Fraction.Order.Arithmetic.mul_nonneg_direct alphaNonnegative
        realNonnegative)
      betaNonnegative)

/-- A quadratic with positive radial coefficient, nonnegative linear coefficients and positive constant is positive in
the nonnegative quadrant.

The supplied coefficient and coordinate inequalities retain the original
finite quadratic expression and its exact displayed sign conditions. -/
public theorem convex_table_positive_up
    {A B C D x y : Fraction.Rational}
    (alphaPositive : 0 < A) (betaNonnegative : 0 ≤ B)
    (etaNonnegative : 0 ≤ C) (originPositive : 0 < D)
    (realNonnegative : 0 ≤ x) (imagNonnegative : 0 ≤ y) :
    0 < Multivariate.Rational.QuadraticBox.tablePolynomial A B C D x y := by
  have xTermNonnegative := Multivariate.Rational.QuadraticBox.convex_x_term_nonnegative alphaPositive.le
    betaNonnegative realNonnegative
  have yTermNonnegative : 0 ≤ y * (A * y + C) :=
    Fraction.Order.Arithmetic.mul_nonneg_direct imagNonnegative
      (add_nonneg
        (Fraction.Order.Arithmetic.mul_nonneg_direct alphaPositive.le
          imagNonnegative)
        etaNonnegative)
  calc
    0 < D + y * (A * y + C) + x * (A * x + B) :=
      Fraction.Order.Arithmetic.add_pos_of_pos_of_nonneg_direct
        (Fraction.Order.Arithmetic.add_pos_of_pos_of_nonneg_direct originPositive yTermNonnegative)
        xTermNonnegative
    _ = Multivariate.Rational.QuadraticBox.tablePolynomial A B C D x y := by
      unfold tablePolynomial
      ring1

/-- Adding one to a rational below one gives a value at most two.

Translating the retained weak coordinate bound by one keeps its original
endpoints; the upper endpoint is the scalar sum one plus one. -/
private theorem y_plus_one_le_two {y : Fraction.Rational} (small : y < 1) :
    y + 1 ≤ 2 := by
  have shifted := Fraction.Order.Arithmetic.add_le_add_right_direct
    small.le 1
  calc
    y + 1 ≤ 1 + 1 := shifted
    _ = 2 := by ring1

/-- For nonnegative A and y below one, A(y+1)+C is bounded above by the upper-edge slope 2A+C.

The original bound on the imaginary coordinate limits its successor by two.
Multiplication by the retained nonnegative radial coefficient preserves that bound. -/
private theorem down_second_le_slope
    {A C y : Fraction.Rational} (alphaNonnegative : 0 ≤ A)
    (imagSmall : y < 1) :
    A * (y + 1) + C ≤ 2 * A + C := by
  have scaled := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Multivariate.Rational.QuadraticBox.y_plus_one_le_two imagSmall) alphaNonnegative
  have shifted := Fraction.Order.Arithmetic.add_le_add_right_direct scaled C
  exact shifted.trans_eq (by ring1)

/-- A nonpositive upper-edge slope bounds A(y+1)+C by zero for y below one.

The original nonpositive upper-edge slope bounds the retained linear
factor through the same imaginary coordinate inequality. -/
private theorem down_second_nonpositive
    {A C y : Fraction.Rational} (alphaNonnegative : 0 ≤ A)
    (imagSmall : y < 1) (slopeNonpositive : 2 * A + C ≤ 0) :
    A * (y + 1) + C ≤ 0 :=
  (Multivariate.Rational.QuadraticBox.down_second_le_slope alphaNonnegative imagSmall).trans slopeNonpositive

/-- A convex radial quadratic with nonpositive upper-edge slope and positive upper corner is positive for nonnegative x
and y below one.

The supplied coefficient and coordinate inequalities retain the original
finite quadratic expression and its exact displayed sign conditions. -/
public theorem convex_table_positive_down_corner
    {A B C D x y : Fraction.Rational}
    (alphaPositive : 0 < A) (betaNonnegative : 0 ≤ B)
    (slopeNonpositive : 2 * A + C ≤ 0)
    (cornerPositive : 0 < A + C + D)
    (realNonnegative : 0 ≤ x)
    (imagSmall : y < 1) :
    0 < Multivariate.Rational.QuadraticBox.tablePolynomial A B C D x y := by
  have xTermNonnegative := Multivariate.Rational.QuadraticBox.convex_x_term_nonnegative alphaPositive.le
    betaNonnegative realNonnegative
  have firstNonpositive : y - 1 ≤ 0 :=
    (Fraction.Order.Arithmetic.sub_neg_direct imagSmall).le
  have secondNonpositive := Multivariate.Rational.QuadraticBox.down_second_nonpositive alphaPositive.le
    imagSmall slopeNonpositive
  have yDifferenceNonnegative := Fraction.Order.Arithmetic.product_nonnegative_of_both_nonpositive
    firstNonpositive secondNonpositive
  calc
    0 < (A + C + D) +
        (y - 1) * (A * (y + 1) + C) + x * (A * x + B) :=
      Fraction.Order.Arithmetic.add_pos_of_pos_of_nonneg_direct
        (Fraction.Order.Arithmetic.add_pos_of_pos_of_nonneg_direct cornerPositive yDifferenceNonnegative)
        xTermNonnegative
    _ = Multivariate.Rational.QuadraticBox.tablePolynomial A B C D x y := by
      unfold tablePolynomial
      ring1

/-- A strictly negative upper-edge slope makes the convex quadratic positive below that edge when its upper corner value
is nonnegative.

The supplied coefficient and coordinate inequalities retain the original
finite quadratic expression and its exact displayed sign conditions. -/
public theorem convex_table_positive_down_slope
    {A B C D x y : Fraction.Rational}
    (alphaPositive : 0 < A) (betaNonnegative : 0 ≤ B)
    (slopeNegative : 2 * A + C < 0)
    (cornerNonnegative : 0 ≤ A + C + D)
    (realNonnegative : 0 ≤ x)
    (imagSmall : y < 1) :
    0 < Multivariate.Rational.QuadraticBox.tablePolynomial A B C D x y := by
  have xTermNonnegative := Multivariate.Rational.QuadraticBox.convex_x_term_nonnegative alphaPositive.le
    betaNonnegative realNonnegative
  have firstNegative := Fraction.Order.Arithmetic.sub_neg_direct imagSmall
  have secondNegative : A * (y + 1) + C < 0 :=
    (Multivariate.Rational.QuadraticBox.down_second_le_slope alphaPositive.le imagSmall).trans_lt slopeNegative
  have yDifferencePositive := Fraction.Order.Arithmetic.product_positive_of_both_negative
    firstNegative secondNegative
  have basePositive := Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct cornerNonnegative
    yDifferencePositive
  calc
    0 < (A + C + D) +
        (y - 1) * (A * (y + 1) + C) + x * (A * x + B) :=
      Fraction.Order.Arithmetic.add_pos_of_pos_of_nonneg_direct basePositive xTermNonnegative
    _ = Multivariate.Rational.QuadraticBox.tablePolynomial A B C D x y := by
      unfold tablePolynomial
      ring1

end Purelib.Polynomial.Multivariate.Rational.QuadraticBox
