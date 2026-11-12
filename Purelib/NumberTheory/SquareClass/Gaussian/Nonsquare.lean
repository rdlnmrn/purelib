module

public import Purelib.Data.Gaussian.Basic
import Purelib.NumberTheory.SquareClass.Rational.Nonsquare
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-! # The rational Gaussian field does not contain a square root of two -/

public section

namespace Purelib.NumberTheory.SquareClass.Gaussian.Nonsquare

open Purelib.Data
open Purelib.Data.Gaussian
open Purelib.Data.Rat

/-- No Gaussian rational squares to two.

The imaginary equation forces one coordinate to vanish. A zero real
coordinate gives a negative real square; a zero imaginary coordinate
would give the excluded rational square root of two.
-/
theorem mul_self_ne_two (point : Basic.Canonical) : point * point ≠ 2 := by
  intro equal
  have realEquation : point.re * point.re - point.im * point.im = 2 := congrArg Basic.Canonical.re equal
  have imaginaryEquation : point.re * point.im + point.im * point.re = 0 := congrArg Basic.Canonical.im equal
  by_cases realZero : point.re = 0
  · have negativeSquare : point.im ^ 2 = -(2 : Fraction.Rational) := by
      calc
        point.im ^ 2 = -(point.re * point.re - point.im * point.im) := by rewrite [realZero]; ring1
        _ = -2 := congrArg Neg.neg realEquation
    have nonnegative : (0 : Fraction.Rational) ≤ -2 :=
      negativeSquare ▸ Fraction.Order.Arithmetic.sq_nonneg_direct point.im
    exact (not_le_of_gt (by decide : (-2 : Fraction.Rational) < 0)) nonnegative
  · by_cases imaginaryZero : point.im = 0
    · have square : point.re ^ 2 = (2 : Fraction.Rational) := by
        calc
          point.re ^ 2 = point.re * point.re - point.im * point.im := by rewrite [imaginaryZero]; ring1
          _ = 2 := realEquation
      exact Rational.Nonsquare.square_ne_two point.re square
    · have twice : (2 : Fraction.Rational) * (point.re * point.im) = 0 := by
        calc
          2 * (point.re * point.im) = point.re * point.im + point.im * point.re := by ring1
          _ = 0 := imaginaryEquation
      exact (Fraction.Field.mul_ne_zero_direct (by decide : (2 : Fraction.Rational) ≠ 0)
        (Fraction.Field.mul_ne_zero_direct realZero imaginaryZero)) twice

end Purelib.NumberTheory.SquareClass.Gaussian.Nonsquare

end
