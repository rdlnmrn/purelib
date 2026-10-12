module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Gaussian.Grid.Basic
import Purelib.Approximation.Rational.Grid.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Geometry.Rational.Box.Band.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Gaussian.Fraction.NaturalDenominator
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Tactic.Ring

/-!
# Grid fractions inside rational bands

A positive band radius bounds both nearest grid-coordinate errors and places the
retained Gaussian fraction strictly inside the original band box.
-/

public section

namespace Purelib.Geometry.Rational.Box.Band.Grid

open Purelib
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Rational
open Purelib.Data.Rat
open Purelib.Geometry.Rational.Box

/-- The constructed grid fraction lies strictly inside every selected Newton band of the
same center and radius. -/
theorem gridFraction_strictly_inside
    {center : Data.Gaussian.Basic.Canonical} {radius : Fraction.Rational}
    (positive : 0 < radius)
    (band : Band.Basic.BandBox center radius) :
    band.box.StrictContains (Grid.Basic.gridFraction center radius).value := by
  have denominatorPositive := Grid.Basic.gridDenominator_pos radius
  have mesh := Grid.Basic.half_reciprocal_gridDenominator_lt positive
  have realBounds := Grid.Basic.gridCoordinate_bounds center.re denominatorPositive
  have imaginaryBounds := Grid.Basic.gridCoordinate_bounds center.im denominatorPositive
  have negativeMesh := Fraction.Order.Arithmetic.neg_lt_neg_direct mesh
  have realLower : center.re - radius <
      Grid.Basic.gridCoordinate center.re (Grid.Basic.gridDenominator radius) :=
    (show center.re - radius <
        center.re - (1 / 2 : Fraction.Rational) / Grid.Basic.gridDenominator radius by
      calc
        center.re - radius = -radius + center.re := by ring1
        _ < (-((1 / 2 : Fraction.Rational) / Grid.Basic.gridDenominator radius)) + center.re :=
          Fraction.Order.Arithmetic.add_lt_add_right_direct negativeMesh _
        _ = center.re - (1 / 2 : Fraction.Rational) / Grid.Basic.gridDenominator radius := by
          ring1).trans realBounds.1
  have realUpper : Grid.Basic.gridCoordinate center.re (Grid.Basic.gridDenominator radius) <
      center.re + radius :=
    realBounds.2.trans_lt
      (Fraction.Order.Arithmetic.add_lt_add_left_direct mesh center.re)
  have imaginaryLower : center.im - radius <
      Grid.Basic.gridCoordinate center.im (Grid.Basic.gridDenominator radius) :=
    (show center.im - radius <
        center.im - (1 / 2 : Fraction.Rational) / Grid.Basic.gridDenominator radius by
      calc
        center.im - radius = -radius + center.im := by ring1
        _ < (-((1 / 2 : Fraction.Rational) / Grid.Basic.gridDenominator radius)) + center.im :=
          Fraction.Order.Arithmetic.add_lt_add_right_direct negativeMesh _
        _ = center.im - (1 / 2 : Fraction.Rational) / Grid.Basic.gridDenominator radius := by
          ring1).trans imaginaryBounds.1
  have imaginaryUpper : Grid.Basic.gridCoordinate center.im (Grid.Basic.gridDenominator radius) <
      center.im + radius :=
    imaginaryBounds.2.trans_lt
      (Fraction.Order.Arithmetic.add_lt_add_left_direct mesh center.im)
  exact
    ⟨by simpa only [Grid.Basic.gridFraction_value_re] using
        band.left_upper.trans_lt realLower,
      by simpa only [Grid.Basic.gridFraction_value_re] using
        realUpper.trans_le band.right_lower,
      by simpa only [Grid.Basic.gridFraction_value_im] using
        band.bottom_upper.trans_lt imaginaryLower,
      by simpa only [Grid.Basic.gridFraction_value_im] using
        imaginaryUpper.trans_le band.top_lower⟩

end Purelib.Geometry.Rational.Box.Band.Grid
