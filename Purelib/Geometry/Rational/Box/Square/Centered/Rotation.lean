module

public import Purelib.Geometry.Rational.Box.Rotation
public import Purelib.Geometry.Rational.Box.Square.Centered
import Purelib.Data.Gaussian.Coordinates.Rotation
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

/-!
# Exact enclosures of rotated centered squares

Rotating a retained square gives a square enclosure about the actual rotated
center. Its half-width is the original radius times one plus the absolute
slope, for either sign of slope and including a zero radius.
-/

public section

namespace Purelib.Geometry.Rational.Box.Rotation

open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Fraction.Order

/-- The computed half-width of a rotated square is nonnegative when its original radius is nonnegative. -/
theorem rotatedRadius_nonnegative (slope radius : Fraction.Rational) (nonnegative : 0 ≤ radius) :
    0 ≤ (1 + Fraction.abs slope) * radius := by
  have factorNonnegative := Arithmetic.add_le_add_direct
    (show (0 : Fraction.Rational) ≤ 1 by decide)
    (Arithmetic.abs_nonneg_direct slope)
  change 0 ≤ 1 + Fraction.abs slope at factorNonnegative
  exact Arithmetic.mul_nonneg_direct factorNonnegative nonnegative

/-- Scaling a centered interval gives endpoints at the center product plus or minus the absolute radius cost.

The sign of the retained slope determines which original endpoint is the
minimum. The absolute slope gives the same nonnegative half-width in both
cases, including a zero slope or radius. -/
private theorem scaled_endpoints (slope center radius : Fraction.Rational) (nonnegative : 0 ≤ radius) :
    min (slope * (center - radius)) (slope * (center + radius)) =
        slope * center - Fraction.abs slope * radius ∧
      max (slope * (center - radius)) (slope * (center + radius)) =
        slope * center + Fraction.abs slope * radius := by
  have endpoints : center - radius ≤ center + radius := by
    calc
      center - radius ≤ center - 0 :=
        Arithmetic.sub_le_sub_left_direct nonnegative center
      _ = center + 0 := by ring1
      _ ≤ center + radius := Arithmetic.add_le_add_direct le_rfl nonnegative
  rcases le_total 0 slope with slopeNonnegative | slopeNonpositive
  · have scaled := Arithmetic.mul_le_mul_of_nonneg_left_direct endpoints slopeNonnegative
    have absolute : Fraction.abs slope = slope := by
      change max slope (-slope) = slope
      exact Basic.max_eq_left
        (Arithmetic.neg_le_self_of_nonnegative slopeNonnegative)
    constructor
    · rewrite [Basic.min_eq_left scaled, absolute]
      ring1
    · rewrite [Basic.max_eq_right scaled, absolute]
      ring1
  · have scaled := Arithmetic.mul_le_mul_of_nonpositive_left endpoints slopeNonpositive
    have absolute : Fraction.abs slope = -slope := by
      change max slope (-slope) = -slope
      have negativeNonnegative := Arithmetic.neg_le_neg_direct slopeNonpositive
      rewrite [_root_.neg_zero] at negativeNonnegative
      exact Basic.max_eq_right (slopeNonpositive.trans negativeNonnegative)
    constructor
    · rewrite [Basic.min_eq_right scaled, absolute]
      ring1
    · rewrite [Basic.max_eq_left scaled, absolute]
      ring1

/-- The exact rotation enclosure of a centered square is centered at its actual rotated point.

Each retained coordinate interval has the same original half-width. The
signed interval products select their true minimum and maximum endpoints,
giving half-width one plus the absolute slope times the original radius. -/
theorem enclosure_centeredSquare (slope : Fraction.Rational) (center : Data.Gaussian.Basic.Canonical)
    (radius : Fraction.Rational) (nonnegative : 0 ≤ radius) :
    enclosure slope (Square.Centered.Affine.centeredSquare center radius nonnegative) =
      Square.Centered.Affine.centeredSquare (Coordinates.Rotation.rotate slope center)
        ((1 + Fraction.abs slope) * radius) (rotatedRadius_nonnegative slope radius nonnegative) := by
  have realEndpoints := scaled_endpoints slope center.im radius nonnegative
  have imaginaryEndpoints := scaled_endpoints (-slope) center.re radius nonnegative
  have negativeAbsolute : Fraction.abs (-slope) = Fraction.abs slope := by
    change max (-slope) (-(-slope)) = max slope (-slope)
    rewrite [_root_.neg_neg]
    exact Basic.max_comm _ _
  apply Box.ext
  · change center.re - radius + min (slope * (center.im - radius)) (slope * (center.im + radius)) =
      (Coordinates.Rotation.rotate slope center).re - (1 + Fraction.abs slope) * radius
    rewrite [realEndpoints.1, Coordinates.Rotation.rotate_real]
    ring1
  · change center.re + radius + max (slope * (center.im - radius)) (slope * (center.im + radius)) =
      (Coordinates.Rotation.rotate slope center).re + (1 + Fraction.abs slope) * radius
    rewrite [realEndpoints.2, Coordinates.Rotation.rotate_real]
    ring1
  · change center.im - radius + min ((-slope) * (center.re - radius)) ((-slope) * (center.re + radius)) =
      (Coordinates.Rotation.rotate slope center).im - (1 + Fraction.abs slope) * radius
    rewrite [imaginaryEndpoints.1, negativeAbsolute, Coordinates.Rotation.rotate_imaginary]
    ring1
  · change center.im + radius + max ((-slope) * (center.re - radius)) ((-slope) * (center.re + radius)) =
      (Coordinates.Rotation.rotate slope center).im + (1 + Fraction.abs slope) * radius
    rewrite [imaginaryEndpoints.2, negativeAbsolute, Coordinates.Rotation.rotate_imaginary]
    ring1

/-- A paid rotated height difference strictly separates the enclosures of the same original centered squares.

The two enclosures have the same computed half-width. Subtracting their
original rotated center heights and paying twice that width orders the
actual upper and lower endpoints of those same enclosures. -/
theorem enclosure_centeredSquare_ySeparated (slope : Fraction.Rational)
    (bottom top : Data.Gaussian.Basic.Canonical) (radius : Fraction.Rational) (nonnegative : 0 ≤ radius)
    (paid : 2 * ((1 + Fraction.abs slope) * radius) <
      (Coordinates.Rotation.rotate slope top).im - (Coordinates.Rotation.rotate slope bottom).im) :
    (enclosure slope (Square.Centered.Affine.centeredSquare bottom radius nonnegative)).yUpper <
      (enclosure slope (Square.Centered.Affine.centeredSquare top radius nonnegative)).yLower := by
  rewrite [enclosure_centeredSquare, enclosure_centeredSquare]
  change (Coordinates.Rotation.rotate slope bottom).im + (1 + Fraction.abs slope) * radius <
    (Coordinates.Rotation.rotate slope top).im - (1 + Fraction.abs slope) * radius
  apply Arithmetic.lt_of_sub_pos_direct
  have positive := Arithmetic.sub_pos_direct paid
  calc
    0 < ((Coordinates.Rotation.rotate slope top).im - (Coordinates.Rotation.rotate slope bottom).im) -
        2 * ((1 + Fraction.abs slope) * radius) := positive
    _ = _ := by ring1

/-- A paid rotated real difference strictly orders the enclosures of the same original centered squares.

The same computed half-width applies to both original squares. Paying
twice that width below their actual rotated center-reading difference
strictly separates the original enclosure endpoints. -/
theorem enclosure_centeredSquare_xOrdered (slope : Fraction.Rational)
    (left right : Data.Gaussian.Basic.Canonical) (radius : Fraction.Rational) (nonnegative : 0 ≤ radius)
    (paid : 2 * ((1 + Fraction.abs slope) * radius) <
      (Coordinates.Rotation.rotate slope right).re - (Coordinates.Rotation.rotate slope left).re) :
    (enclosure slope (Square.Centered.Affine.centeredSquare left radius nonnegative)).xUpper <
      (enclosure slope (Square.Centered.Affine.centeredSquare right radius nonnegative)).xLower := by
  rewrite [enclosure_centeredSquare, enclosure_centeredSquare]
  change (Coordinates.Rotation.rotate slope left).re + (1 + Fraction.abs slope) * radius <
    (Coordinates.Rotation.rotate slope right).re - (1 + Fraction.abs slope) * radius
  apply Arithmetic.lt_of_sub_pos_direct
  have positive := Arithmetic.sub_pos_direct paid
  calc
    0 < ((Coordinates.Rotation.rotate slope right).re - (Coordinates.Rotation.rotate slope left).re) -
        2 * ((1 + Fraction.abs slope) * radius) := positive
    _ = _ := by ring1

end Purelib.Geometry.Rational.Box.Rotation
