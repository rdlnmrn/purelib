module
public import Purelib.Data.Gaussian.Coordinates.Rotation
public import Purelib.Data.Rat.Interval.Arithmetic
public import Purelib.Geometry.Rational.Box.Intervals
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring

/-!
# Rational enclosures of rotated boxes

The original coordinate intervals determine exact enclosing intervals after
multiplication by one minus slope times the imaginary unit. The resulting box
encloses the rotated image and preserves strict widths of a proper source box.
-/

public section

namespace Purelib.Geometry.Rational.Box.Rotation

open Purelib.Data.Gaussian
open Purelib.Data.Rat

/-- Enclose the rotated real coordinate by the original horizontal interval plus the scaled vertical interval. -/
@[expose] def realBounds (slope : Fraction.Rational) (box : Rational.Box) : Interval.Bounds :=
  Interval.Arithmetic.add (Intervals.horizontalInterval box)
    (Interval.Arithmetic.scale slope (Intervals.verticalInterval box))

/-- Enclose the rotated imaginary coordinate by the original vertical interval plus the negatively scaled horizontal.
-/
@[expose] def imaginaryBounds (slope : Fraction.Rational) (box : Rational.Box) : Interval.Bounds :=
  Interval.Arithmetic.add (Intervals.verticalInterval box)
    (Interval.Arithmetic.scale (-slope) (Intervals.horizontalInterval box))

/-- Construct the axis-aligned rational enclosure from the two computed rotated coordinate intervals.

Both coordinate intervals retain the original source endpoints and one shared
rotation slope. The resulting box is an enclosure of the rotated image. -/
@[expose] def enclosure (slope : Fraction.Rational) (box : Rational.Box) : Rational.Box :=
  let real := realBounds slope box
  let imaginary := imaginaryBounds slope box
  { xLower := real.lower
    xUpper := real.upper
    yLower := imaginary.lower
    yUpper := imaginary.upper
    x_valid := real.valid
    y_valid := imaginary.valid }

/-- The rotated real reading of an original contained point lies in the computed real interval. -/
theorem realBounds_contains (slope : Fraction.Rational) (box : Rational.Box)
    {point : Data.Gaussian.Basic.Canonical} (inside : box.Contains point) :
    (realBounds slope box).Contains (Coordinates.Rotation.rotate slope point).re := by
  rewrite [Coordinates.Rotation.rotate_real]
  exact Interval.Arithmetic.add_contains _ _ ⟨inside.1, inside.2.1⟩
    (Interval.Arithmetic.scale_contains slope _ ⟨inside.2.2.1, inside.2.2.2⟩)

/-- The rotated imaginary reading of an original contained point lies in the computed imaginary interval. -/
theorem imaginaryBounds_contains (slope : Fraction.Rational) (box : Rational.Box)
    {point : Data.Gaussian.Basic.Canonical} (inside : box.Contains point) :
    (imaginaryBounds slope box).Contains (Coordinates.Rotation.rotate slope point).im := by
  rewrite [Coordinates.Rotation.rotate_imaginary,
    show point.im - slope * point.re = point.im + (-slope) * point.re by ring1]
  exact Interval.Arithmetic.add_contains _ _ ⟨inside.2.2.1, inside.2.2.2⟩
    (Interval.Arithmetic.scale_contains (-slope) _ ⟨inside.1, inside.2.1⟩)

/-- The computed enclosure contains the actual rotation of every point in the original box. -/
theorem enclosure_contains (slope : Fraction.Rational) (box : Rational.Box)
    {point : Data.Gaussian.Basic.Canonical} (inside : box.Contains point) :
    (enclosure slope box).Contains (Coordinates.Rotation.rotate slope point) :=
  let real := realBounds_contains slope box inside
  let imaginary := imaginaryBounds_contains slope box inside
  ⟨real.1, real.2, imaginary.1, imaginary.2⟩

/-- A proper source box has a proper rotated enclosure for every rational slope.

The unscaled horizontal and vertical widths remain strictly positive. Each
additional scaled interval has nonnegative width, preserving both strict bounds. -/
theorem enclosure_proper (slope : Fraction.Rational) (box : Rational.Box) (proper : box.Proper) :
    (enclosure slope box).Proper := by
  constructor
  · change box.xLower + (Interval.Arithmetic.scale slope (Intervals.verticalInterval box)).lower <
      box.xUpper + (Interval.Arithmetic.scale slope (Intervals.verticalInterval box)).upper
    exact (Fraction.Order.Arithmetic.add_lt_add_right_direct proper.1 _).trans_le
      (Fraction.Order.Arithmetic.add_le_add_direct le_rfl
        (Interval.Arithmetic.scale slope (Intervals.verticalInterval box)).valid)
  · change box.yLower + (Interval.Arithmetic.scale (-slope) (Intervals.horizontalInterval box)).lower <
      box.yUpper + (Interval.Arithmetic.scale (-slope) (Intervals.horizontalInterval box)).upper
    exact (Fraction.Order.Arithmetic.add_lt_add_right_direct proper.2 _).trans_le
      (Fraction.Order.Arithmetic.add_le_add_direct le_rfl
        (Interval.Arithmetic.scale (-slope) (Intervals.horizontalInterval box)).valid)

/-- The zero-slope enclosure restores the original box, including its exact endpoints. -/
theorem enclosure_zero (box : Rational.Box) : enclosure 0 box = box := by
  apply Box.ext
  · change box.xLower + min (0 * box.yLower) (0 * box.yUpper) = box.xLower
    rewrite [Fraction.Field.zero_mul_direct, Fraction.Field.zero_mul_direct]
    change box.xLower + 0 = box.xLower
    ring1
  · change box.xUpper + max (0 * box.yLower) (0 * box.yUpper) = box.xUpper
    rewrite [Fraction.Field.zero_mul_direct, Fraction.Field.zero_mul_direct, Fraction.Order.Basic.max_self]
    ring1
  · change box.yLower + min (-(0 : Fraction.Rational) * box.xLower)
      (-(0 : Fraction.Rational) * box.xUpper) = box.yLower
    rewrite [show -(0 : Fraction.Rational) = 0 by decide,
      Fraction.Field.zero_mul_direct, Fraction.Field.zero_mul_direct]
    change box.yLower + 0 = box.yLower
    ring1
  · change box.yUpper + max (-(0 : Fraction.Rational) * box.xLower)
      (-(0 : Fraction.Rational) * box.xUpper) = box.yUpper
    rewrite [show -(0 : Fraction.Rational) = 0 by decide,
      Fraction.Field.zero_mul_direct, Fraction.Field.zero_mul_direct, Fraction.Order.Basic.max_self]
    ring1

end Purelib.Geometry.Rational.Box.Rotation
