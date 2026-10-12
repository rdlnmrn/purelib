module
import Purelib.Data.Rat.Fraction.Cast
import Purelib.Data.Gaussian.Basic
import Purelib.Algebra.Ring.IntCast
public import Purelib.Data.GaussianInt.Embedding
import Purelib.Data.GaussianInt.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Data.Rat.Rounding.Floor
public import Purelib.Geometry.Region.Gaussian.UnitSquare

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring

open Purelib.Data
open Purelib.Algebra.Ring

open Purelib.Data.Gaussian.Basic

open Purelib.Data.GaussianInt

open Purelib.Data.Rat.Fraction

open Purelib.Data.Rat.Fraction.Order

open Purelib.Geometry.Region.Gaussian

/-!
# Gaussian-integer floor and rational fractional part

Coordinatewise Euclidean quotients retain the original integer endpoints.
Subtracting their original Gaussian embedding gives fractional coordinates
in the half-open unit square.
-/

namespace Purelib.Data.GaussianInt.Floor

/-- Take the exact rational floor independently in both Gaussian coordinates.

Both integer coordinates retain the Euclidean quotients of the original
signed numerators and positive denominators. The Gaussian floor stores those
two exact integer endpoints. -/
@[expose] public def floor (z : Canonical) : GaussianInt :=
  ⟨Rat.Rounding.Floor.floor z.re,
    Rat.Rounding.Floor.floor z.im⟩

/-- The real coordinate of Gaussian-integer floor is the original rational
real-coordinate floor. -/
@[simp] public theorem floor_re (z : Canonical) :
    (floor z).re = Rat.Rounding.Floor.floor z.re := rfl

/-- The imaginary coordinate of Gaussian-integer floor is the original rational
imaginary-coordinate floor. -/
@[simp] public theorem floor_im (z : Canonical) :
    (floor z).im = Rat.Rounding.Floor.floor z.im := rfl

/-- Subtract the embedded coordinatewise floor from a Gaussian rational.

The original Gaussian subtraction removes the exact integer endpoints in both
coordinates. Each remaining rational coordinate is the corresponding fractional
part of the same input. -/
@[expose] public def fract (z : Canonical) : Canonical := z - GaussianInt.toGaussian (floor z)

/-- The coordinatewise fractional part belongs to the half-open rational unit square.

Each coordinate is at least zero and strictly below one by the exact lower and upper
floor inequalities. -/
public theorem fract_sq (z : Canonical) : UnitSquare.Sq (fract z) := by
  have realLower := Rat.Rounding.Floor.intCast_floor_le z.re
  have realUpper := Rat.Rounding.Floor.lt_intCast_floor_add_one z.re
  have imagLower := Rat.Rounding.Floor.intCast_floor_le z.im
  have imagUpper := Rat.Rounding.Floor.lt_intCast_floor_add_one z.im
  constructor
  · simp only [-eq_self, -iff_self, fract, GaussianInt.toGaussian, ← Rat.Fraction.Cast.intCast_eq_fromInt]
    change 0 ≤ z.re -
      ((Rat.Rounding.Floor.floor z.re : Int) : Rational)
    exact Arithmetic.sub_nonneg_direct realLower
  constructor
  · simp only [-eq_self, -iff_self, fract, GaussianInt.toGaussian, ← Rat.Fraction.Cast.intCast_eq_fromInt]
    change z.re -
      ((Rat.Rounding.Floor.floor z.re : Int) : Rational) < 1
    have shifted := Arithmetic.add_lt_add_right_direct
      realUpper (-((Rat.Rounding.Floor.floor z.re : Int) : Rational))
    calc
      z.re - ((Rat.Rounding.Floor.floor z.re : Int) : Rational) =
          z.re + -((Rat.Rounding.Floor.floor z.re : Int) : Rational) := rfl
      _ < ((Rat.Rounding.Floor.floor z.re : Int) : Rational) + 1 +
          -((Rat.Rounding.Floor.floor z.re : Int) : Rational) := by
        rewrite [IntCast.add, Int.cast_one] at shifted
        exact shifted
      _ = 1 := by ring1
  constructor
  · simp only [-eq_self, -iff_self, fract, GaussianInt.toGaussian, ← Rat.Fraction.Cast.intCast_eq_fromInt]
    change 0 ≤ z.im -
      ((Rat.Rounding.Floor.floor z.im : Int) : Rational)
    exact Arithmetic.sub_nonneg_direct imagLower
  · simp only [-eq_self, -iff_self, fract, GaussianInt.toGaussian, ← Rat.Fraction.Cast.intCast_eq_fromInt]
    change z.im -
      ((Rat.Rounding.Floor.floor z.im : Int) : Rational) < 1
    have shifted := Arithmetic.add_lt_add_right_direct
      imagUpper (-((Rat.Rounding.Floor.floor z.im : Int) : Rational))
    calc
      z.im - ((Rat.Rounding.Floor.floor z.im : Int) : Rational) =
          z.im + -((Rat.Rounding.Floor.floor z.im : Int) : Rational) := rfl
      _ < ((Rat.Rounding.Floor.floor z.im : Int) : Rational) + 1 +
          -((Rat.Rounding.Floor.floor z.im : Int) : Rational) := by
        rewrite [IntCast.add, Int.cast_one] at shifted
        exact shifted
      _ = 1 := by ring1
end Purelib.Data.GaussianInt.Floor
