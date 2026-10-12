module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
public import Purelib.Data.Gaussian.Cast
import Purelib.Data.Rat.Bounds.Square
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order

import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

section
section
public section

/-!
# Integral affine Gaussian norm bounds

A retained squared imaginary gap controls the squared norm of every integral
row. The real-coefficient case and the imaginary-coefficient case preserve
the original integer casts, coordinate values and squared lower bound.
-/

namespace Purelib.Data.Gaussian.Affine.Integral.Bounds

open Purelib.Data.Rat.Fraction renaming Rational -> Q

open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian

open Purelib.Data.Rat in
/-- Compute a squared-norm lower bound for an integral affine row from its imaginary gap.

When the imaginary row coefficient vanishes, retain the square of the real coefficient. Otherwise use the imaginary
coefficient square times the gap square; positivity requires a nonzero row and a positive gap. -/
@[expose] def rowLower (a b : Int) (epsilon : Fraction.Rational) : Fraction.Rational :=
  if b = 0 then (a : Fraction.Rational) ^ 2 else (b : Fraction.Rational) ^ 2 * epsilon ^ 2

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- A squared imaginary-gap bound gives the retained integral row lower bound on the affine Gaussian norm. -/
theorem rowLower_le_of_squared (a b : Int) (gap : Q) (value : Gaussian)
    (lower : gap ^ 2 ≤ value.im ^ 2) :
    rowLower a b gap ≤ Norm.Basic.normSq (Cast.integralGaussian a +
      Cast.integralGaussian b * value) := by
  unfold rowLower
  split
  next equal =>
    subst b
    change (a : Q) ^ 2 ≤
      ((a : Q) + (0 * value.re - 0 * value.im)) ^ 2 +
      (0 + (0 * value.im + 0 * value.re)) ^ 2
    simp only [-eq_self, -iff_self, MulZeroClass.zero_mul, Fraction.Arithmetic.sub_eq_add_neg_direct, (show -(0 :
      Fraction.Rational) = 0 from rfl), AddZeroClass.add_zero, zero_pow (by decide : 2 ≠ 0)]
    exact le_rfl
  next _ =>
    have scaled := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      lower (Fraction.Order.Arithmetic.sq_nonneg_direct (b : Q))
    apply scaled.trans
    change (b : Q) ^ 2 * value.im ^ 2 ≤
      ((a : Q) + ((b : Q) * value.re - 0 * value.im)) ^ 2 +
      (0 + ((b : Q) * value.im + 0 * value.re)) ^ 2
    simp only [-eq_self, -iff_self, MulZeroClass.zero_mul, AddZeroClass.add_zero, _root_.zero_add,
      Fraction.Arithmetic.sub_eq_add_neg_direct, (show -(0 : Fraction.Rational) = 0 from rfl)]
    calc
      (b : Q) ^ 2 * value.im ^ 2 = ((b : Q) * value.im) ^ 2 := by ring1
      _ ≤ ((a : Q) + (b : Q) * value.re) ^ 2 + ((b : Q) * value.im) ^ 2 :=
        le_add_of_nonneg_left (Fraction.Order.Arithmetic.sq_nonneg_direct _)
end Purelib.Data.Gaussian.Affine.Integral.Bounds

end

end

section
public section

/-!
# Positive integral row bounds

A positive imaginary gap and a nonzero coefficient pair make the retained
row bound positive. The same original row and Gaussian coordinate satisfy
the displayed squared-norm comparison.
-/

namespace Purelib.Data.Gaussian.Affine.Integral.Bounds

open Purelib.Data.Gaussian
open Purelib.Data.Rat
/-- A positive gap and a nonzero pair of integer row coefficients make the row lower bound positive. -/
theorem rowLower_positive (a b : Int) (epsilon : Fraction.Rational)
    (positive : 0 < epsilon) (nonzero : a ≠ 0 ∨ b ≠ 0) :
    0 < rowLower a b epsilon := by
  unfold rowLower
  split
  next equal =>
    have aNonzero : a ≠ 0 := nonzero.resolve_right (fun h => h equal)
    exact Bounds.Square.integer_square_positive a aNonzero
  next different =>
    apply Fraction.Order.Arithmetic.mul_pos_direct
    · exact Bounds.Square.integer_square_positive b different
    · exact Fraction.Order.Arithmetic.pow_pos_direct positive 2

/-- A positive lower bound on the imaginary coordinate bounds the integral affine row norm from below. -/
theorem rowLower_le (a b : Int) (epsilon : Fraction.Rational) (value : Basic.Canonical)
    (positive : 0 < epsilon) (lower : epsilon ≤ value.im) :
    rowLower a b epsilon ≤ Norm.Basic.normSq (Cast.integralGaussian a +
      Cast.integralGaussian b * value) := by
  unfold rowLower
  split
  next equal =>
    subst b
    change (a : Fraction.Rational) ^ 2 ≤
      ((a : Fraction.Rational) + (0 * value.re - 0 * value.im)) ^ 2 +
      (0 + (0 * value.im + 0 * value.re)) ^ 2
    simp only [-eq_self, -iff_self, MulZeroClass.zero_mul, Fraction.Arithmetic.sub_eq_add_neg_direct, (show -(0 :
      Fraction.Rational) = 0 from rfl), AddZeroClass.add_zero, zero_pow (by decide : 2 ≠ 0)]
    exact le_rfl
  next _ =>
    have squareLe := Fraction.Order.Arithmetic.pow_le_pow_direct
      positive.le lower 2
    have scaled := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      squareLe (Fraction.Order.Arithmetic.sq_nonneg_direct (b : Fraction.Rational))
    calc
      (b : Fraction.Rational) ^ 2 * epsilon ^ 2 ≤ (b : Fraction.Rational) ^ 2 * value.im ^ 2 := scaled
      _ ≤ Norm.Basic.normSq (Cast.integralGaussian a + Cast.integralGaussian b * value) := by
        change (b : Fraction.Rational) ^ 2 * value.im ^ 2 ≤
          ((a : Fraction.Rational) + ((b : Fraction.Rational) * value.re - 0 * value.im)) ^ 2 +
          (0 + ((b : Fraction.Rational) * value.im + 0 * value.re)) ^ 2
        simp only [-eq_self, -iff_self, MulZeroClass.zero_mul, AddZeroClass.add_zero, _root_.zero_add,
          Fraction.Arithmetic.sub_eq_add_neg_direct, (show -(0 : Fraction.Rational) = 0 from rfl)]
        calc
          (b : Fraction.Rational) ^ 2 * value.im ^ 2 = ((b : Fraction.Rational) * value.im) ^ 2 := by ring1
          _ ≤ ((a : Fraction.Rational) + (b : Fraction.Rational) * value.re) ^ 2 +
              ((b : Fraction.Rational) * value.im) ^ 2 :=
            le_add_of_nonneg_left (Fraction.Order.Arithmetic.sq_nonneg_direct
              ((a : Fraction.Rational) + (b : Fraction.Rational) * value.re))
end Purelib.Data.Gaussian.Affine.Integral.Bounds

end
