module
import Purelib.Data.Rat.Fraction.Cast
import Purelib.Data.Gaussian.Basic
public import Purelib.Data.GaussianInt.Embedding
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.GaussianInt.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Data.Rat.Rounding.Nearest

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Data

open Purelib.Data.Gaussian.Basic

open Purelib.Data.Gaussian.Norm.Basic

open Purelib.Data.GaussianInt

open Purelib.Data.Rat.Fraction

open Purelib.Data.Rat.Fraction.Order

open Purelib.Data.Rat.Rounding

@[expose] public section

/-!
# Constructive nearest-Gaussian-integer arithmetic

This is the finite arithmetic kernel for a Hurwitz continued fraction over
the Gaussian integers.  Ties are resolved coordinatewise toward the positive
integer: `nearestCoordinate x = floor (x + 1/2)`.  Consequently the displayed
remainder lies in the half-open square `[-1/2, 1/2)²` and has quadrance at
most `1/2`.
-/

namespace Purelib.Data.GaussianInt.Nearest

/-- Select the nearest Gaussian integer by independent exact rational coordinate
rounding.

Half-integer ties are resolved toward the positive integer, preserving the original
deterministic nearestCoordinate convention. -/
def nearest (value : Canonical) : GaussianInt :=
  ⟨Nearest.nearestCoordinate value.re, Nearest.nearestCoordinate value.im⟩

/-- Subtract the embedded selected nearest Gaussian integer from the original rational
value. -/
def remainder (value : Canonical) : Canonical :=
  value - GaussianInt.toGaussian (nearest value)

/-- Require both rational coordinates to lie in the half-open interval from negative one
half to one half. -/
def InFundamentalSquare (value : Canonical) : Prop :=
  -(1 / 2 : Rational) ≤ value.re ∧ value.re < 1 / 2 ∧
    -(1 / 2 : Rational) ≤ value.im ∧ value.im < 1 / 2

/-- The deterministic nearest-integer remainder lies in the retained half-open
fundamental square. -/
theorem remainder_mem (value : Canonical) :
    InFundamentalSquare (remainder value) := by
  have realBounds := Nearest.nearestCoordinate_error_bounds value.re
  have imaginaryBounds := Nearest.nearestCoordinate_error_bounds value.im
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [-eq_self, -iff_self, remainder, nearest, Gaussian.Basic.sub_re, Gaussian.Basic.sub_im,
      GaussianInt.toGaussian,
      ← Rat.Fraction.Cast.intCast_eq_fromInt] using realBounds.1
  · simpa only [-eq_self, -iff_self, remainder, nearest, Gaussian.Basic.sub_re, Gaussian.Basic.sub_im,
      GaussianInt.toGaussian,
      ← Rat.Fraction.Cast.intCast_eq_fromInt] using realBounds.2
  · simpa only [-eq_self, -iff_self, remainder, nearest, Gaussian.Basic.sub_re, Gaussian.Basic.sub_im,
      GaussianInt.toGaussian,
      ← Rat.Fraction.Cast.intCast_eq_fromInt] using imaginaryBounds.1
  · simpa only [-eq_self, -iff_self, remainder, nearest, Gaussian.Basic.sub_re, Gaussian.Basic.sub_im,
      GaussianInt.toGaussian,
      ← Rat.Fraction.Cast.intCast_eq_fromInt] using imaginaryBounds.2

/-- A rational coordinate in the half-open centered unit interval has square at most one
quarter. -/
private theorem square_le_quarter {value : Rational}
    (lower : -(1 / 2 : Rational) ≤ value)
    (upper : value < 1 / 2) :
    value ^ 2 ≤ (1 / 2 : Rational) ^ 2 := by
  have leftNonnegative :
      0 ≤ (1 / 2 : Rational) - value :=
    Arithmetic.sub_nonneg_direct upper.le
  have rightNonnegative :
      0 ≤ value + (1 / 2 : Rational) := by
    have translated :=
      Arithmetic.add_le_add_right_direct lower
        (1 / 2 : Rational)
    calc
      0 = -(1 / 2 : Rational) + 1 / 2 := by ring1
      _ ≤ value + 1 / 2 := translated
  have productNonnegative := Arithmetic.mul_nonneg_direct
    leftNonnegative rightNonnegative
  have differenceNonnegative :
      0 ≤ (1 / 2 : Rational) ^ 2 - value ^ 2 := by
    calc
      0 ≤ ((1 / 2 : Rational) - value) * (value + 1 / 2) :=
        productNonnegative
      _ = (1 / 2 : Rational) ^ 2 - value ^ 2 := by ring1
  have shifted := Arithmetic.add_le_add_right_direct
    differenceNonnegative (value ^ 2)
  calc
    value ^ 2 = 0 + value ^ 2 := by ring1
    _ ≤ ((1 / 2 : Rational) ^ 2 - value ^ 2) + value ^ 2 := shifted
    _ = (1 / 2 : Rational) ^ 2 := by ring1

/-- The nearest Gaussian-integer residual has squared norm at most one half.

Both retained coordinate errors have square at most one quarter, and their direct
rational sum gives the bound. -/
theorem remainder_normSq_le_half (value : Canonical) :
    Data.Gaussian.Norm.Basic.normSq (remainder value) ≤ 1 / 2 := by
  have inside := remainder_mem value
  have realBound := square_le_quarter inside.1 inside.2.1
  have imaginaryBound := square_le_quarter inside.2.2.1 inside.2.2.2
  calc
    Data.Gaussian.Norm.Basic.normSq (remainder value) =
        (remainder value).re ^ 2 + (remainder value).im ^ 2 := rfl
    _ ≤ (1 / 2 : Rational) ^ 2 + (remainder value).im ^ 2 :=
      Arithmetic.add_le_add_right_direct realBound _
    _ ≤ (1 / 2 : Rational) ^ 2 + (1 / 2 : Rational) ^ 2 := by
      have shifted := Arithmetic.add_le_add_right_direct
        imaginaryBound ((1 / 2 : Rational) ^ 2)
      calc
        (1 / 2 : Rational) ^ 2 + (remainder value).im ^ 2 =
            (remainder value).im ^ 2 + (1 / 2 : Rational) ^ 2 :=
          _root_.add_comm _ _
        _ ≤ (1 / 2 : Rational) ^ 2 + (1 / 2 : Rational) ^ 2 := shifted
    _ = 1 / 2 := by decide

/-- The selected Gaussian integer minimizes squared residual norm among all displayed
integral competitors.

Coordinatewise nearest-integer minimality adds directly to the two-dimensional
comparison, with the same original rational value and competitor. -/
theorem remainder_normSq_le_competitor (value : Canonical)
    (competitor : GaussianInt) :
    Data.Gaussian.Norm.Basic.normSq (remainder value) ≤
      Data.Gaussian.Norm.Basic.normSq (value - GaussianInt.toGaussian competitor) := by
  have realBound := Nearest.nearestCoordinate_sq_le value.re competitor.re
  have imaginaryBound := Nearest.nearestCoordinate_sq_le value.im competitor.im
  simp only [-eq_self, -iff_self, remainder, nearest, GaussianInt.toGaussian,
    ← Rat.Fraction.Cast.intCast_eq_fromInt]
  change
    (value.re - (Nearest.nearestCoordinate value.re : Rational)) ^ 2 +
        (value.im - (Nearest.nearestCoordinate value.im : Rational)) ^ 2 ≤
      (value.re - (competitor.re : Rational)) ^ 2 +
        (value.im - (competitor.im : Rational)) ^ 2
  calc
    (value.re - (Nearest.nearestCoordinate value.re : Rational)) ^ 2 +
        (value.im - (Nearest.nearestCoordinate value.im : Rational)) ^ 2 ≤
      (value.re - (competitor.re : Rational)) ^ 2 +
        (value.im - (Nearest.nearestCoordinate value.im : Rational)) ^ 2 :=
      Arithmetic.add_le_add_right_direct realBound _
    _ ≤ (value.re - (competitor.re : Rational)) ^ 2 +
        (value.im - (competitor.im : Rational)) ^ 2 := by
      have shifted := Arithmetic.add_le_add_right_direct
        imaginaryBound ((value.re - (competitor.re : Rational)) ^ 2)
      calc
        (value.re - (competitor.re : Rational)) ^ 2 +
            (value.im - (Nearest.nearestCoordinate value.im : Rational)) ^ 2 =
          (value.im - (Nearest.nearestCoordinate value.im : Rational)) ^ 2 +
            (value.re - (competitor.re : Rational)) ^ 2 :=
          _root_.add_comm _ _
        _ ≤ (value.im - (competitor.im : Rational)) ^ 2 +
            (value.re - (competitor.re : Rational)) ^ 2 := shifted
        _ = (value.re - (competitor.re : Rational)) ^ 2 +
            (value.im - (competitor.im : Rational)) ^ 2 :=
          _root_.add_comm _ _

end Purelib.Data.GaussianInt.Nearest

end
