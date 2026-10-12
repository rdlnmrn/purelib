module

public import Purelib.Geometry.Rational.Box.Square.Centered
public import Purelib.Data.Rat.Bounds.Radius
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Rational rectangular bands around a retained centre

The original box endpoints carry eight comparisons locating its sides
between one radius and twice that radius from the same Gaussian centre.
The displayed widest band keeps those endpoints and comparisons.
-/

open Purelib
open Purelib.Data.Rat
open Purelib.Geometry
open Purelib.Geometry.Rational.Box.Square.Centered

namespace Purelib.Geometry.Rational.Box.Band.Basic

@[expose] public section

set_option genInjectivity false in
/-- A retained rectangle with each side at distance between the radius and twice the radius from its centre.

The original Gaussian centre and rational radius index all eight endpoint
comparisons. The retained box supplies those same endpoints and its
original ordering certificates. -/
structure BandBox (center : Data.Gaussian.Basic.Canonical) (r : Fraction.Rational) where
  /-- The retained rectangle whose sides satisfy the radial axis-band bounds. -/ box : Rational.Box
  /-- The left side is no farther than twice the radius to the left of the center. -/ left_lower : center.re - 2 * r ≤
    box.xLower
  /-- The left side is at least one radius to the left of the center. -/ left_upper : box.xLower ≤ center.re - r
  /-- The right side is at least one radius to the right of the center. -/ right_lower : center.re + r ≤ box.xUpper
  /-- The right side is no farther than twice the radius to the right of the center. -/ right_upper : box.xUpper ≤
    center.re + 2 * r
  /-- The bottom side is no farther than twice the radius below the center. -/ bottom_lower : center.im - 2 * r ≤
    box.yLower
  /-- The bottom side is at least one radius below the center. -/ bottom_upper : box.yLower ≤ center.im - r
  /-- The top side is at least one radius above the center. -/ top_lower : center.im + r ≤ box.yUpper
  /-- The top side is no farther than twice the radius above the center. -/ top_upper : box.yUpper ≤ center.im + 2 * r

constructive_injectivity BandBox

end

/-- The centred square attains the outer endpoints allowed by the retained band constraints.

The original positive radius gives a square of twice that half-width
about the same centre. The same rectangle and scalar radius comparisons
supply all eight retained side certificates. -/
@[expose] public def widestBand (center : Data.Gaussian.Basic.Canonical) (r : Fraction.Rational) (positive : 0 < r) :
    Geometry.Rational.Box.Band.Basic.BandBox center r :=
  { box := Affine.centeredSquare center (2 * r)
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) positive.le)
    left_lower := le_rfl
    left_upper := (Bounds.Radius.sub_twice_lt_sub positive).le
    right_lower := (Bounds.Radius.add_lt_add_twice positive).le
    right_upper := le_rfl
    bottom_lower := le_rfl
    bottom_upper := (Bounds.Radius.sub_twice_lt_sub positive).le
    top_lower := (Bounds.Radius.add_lt_add_twice positive).le
    top_upper := le_rfl }

end Purelib.Geometry.Rational.Box.Band.Basic
