module

import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-!
# Rational rotations of Gaussian coordinates

Multiplication by `1 - slope * i` provides an exact rational projection
direction. Its positive scale factor controls squared norms and oriented
coordinate determinants without a trigonometric or completed scalar model.
-/

public section

namespace Purelib.Data.Gaussian.Coordinates.Rotation

open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat

/-- Rotate and scale a Gaussian point by the exact factor one minus slope times the imaginary unit. -/
@[expose] def rotate (slope : Fraction.Rational) (point : Canonical) : Canonical :=
  (⟨1, -slope⟩ : Canonical) * point

/-- The rotated real coordinate is the original real coordinate plus slope times the imaginary coordinate. -/
theorem rotate_real (slope : Fraction.Rational) (point : Canonical) :
    (rotate slope point).re = point.re + slope * point.im := by
  change 1 * point.re - (-slope) * point.im = point.re + slope * point.im
  ring1

/-- The rotated imaginary coordinate is the original imaginary coordinate minus slope times the real coordinate. -/
theorem rotate_imaginary (slope : Fraction.Rational) (point : Canonical) :
    (rotate slope point).im = point.im - slope * point.re := by
  change 1 * point.im + (-slope) * point.re = point.im - slope * point.re
  ring1

/-- The exact squared scale factor of every retained rational rotation is strictly positive. -/
theorem scale_positive (slope : Fraction.Rational) : 0 < 1 + slope ^ 2 := by
  have squareNonnegative := Fraction.Order.Arithmetic.sq_nonneg_direct slope
  exact ⟨add_nonneg (by decide) squareNonnegative,
    fun upper => (by decide : ¬ (1 : Fraction.Rational) ≤ 0)
      ((le_add_of_nonneg_right squareNonnegative).trans upper)⟩

/-- Equal rotated real readings scale the relative imaginary height by the positive rotation factor.

The same real-reading equality eliminates the original real-coordinate
difference. The remaining signed imaginary difference is multiplied by
one plus the square of the retained rational slope. -/
theorem relative_imaginary_of_real_eq (slope : Fraction.Rational) {first second : Canonical}
    (same : (rotate slope first).re = (rotate slope second).re) :
    (rotate slope first).im - (rotate slope second).im =
      (1 + slope ^ 2) * (first.im - second.im) := by
  rewrite [rotate_real, rotate_real] at same
  rewrite [rotate_imaginary, rotate_imaginary]
  calc
    _ = (1 + slope ^ 2) * (first.im - second.im) -
        slope * ((first.re + slope * first.im) - (second.re + slope * second.im)) := by ring1
    _ = (1 + slope ^ 2) * (first.im - second.im) := by rewrite [same]; ring1

/-- Rotation multiplies squared distance from the origin by its exact positive scale factor. -/
theorem normSq_rotate (slope : Fraction.Rational) (point : Canonical) :
    Norm.Basic.normSq (rotate slope point) = (1 + slope ^ 2) * Norm.Basic.normSq point := by
  change (1 * point.re - (-slope) * point.im) ^ 2 + (1 * point.im + (-slope) * point.re) ^ 2 =
    (1 + slope ^ 2) * (point.re ^ 2 + point.im ^ 2)
  ring1

/-- Rotation scales the oriented determinant of two coordinate vectors by the same positive factor.

Both vectors retain their original Gaussian owners. The coordinate identity
therefore preserves their planar orientation under the exact rational rotation. -/
theorem determinant_rotate (slope : Fraction.Rational) (first second : Canonical) :
    (rotate slope first).re * (rotate slope second).im -
        (rotate slope first).im * (rotate slope second).re =
      (1 + slope ^ 2) * (first.re * second.im - first.im * second.re) := by
  rewrite [rotate_real, rotate_real, rotate_imaginary, rotate_imaginary]
  ring1

/-- Multiplication by one minus the imaginary unit sends the real coordinate to the sum
of the original coordinates. -/
theorem diagonalRotation_real (point : Canonical) :
    (⟨1, -1⟩ * point : Canonical).re = point.re + point.im := by
  change (1 : Fraction.Rational) * point.re - (-1) * point.im =
    point.re + point.im
  ring1
end Purelib.Data.Gaussian.Coordinates.Rotation
