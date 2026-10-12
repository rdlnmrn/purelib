module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
public import Purelib.Data.Gaussian.Components.Basic

open Purelib.Data.Gaussian

open Purelib.Data.Gaussian.Basic

open Purelib.Data.Rat.Fraction

section
@[expose] public section

/-!
# Nonzero Gaussian points

A point with a nonzero real or imaginary rational coordinate is nonzero in
the original Gaussian carrier.
-/

namespace Purelib.Data.Gaussian.Components.Nonzero

/-- A Gaussian point with nonzero imaginary coordinate is nonzero. -/
public theorem point_ne_zero_of_im_ne_zero (x y :
  Rational) (hy : y ≠ 0) :
    Components.Basic.point x y ≠ 0 := by
  intro equal
  have imaginary := congrArg (fun z : Canonical => z.im) equal
  exact hy imaginary

/-- A Gaussian point with nonzero real coordinate is nonzero. -/
public theorem point_ne_zero_of_re_ne_zero (x y :
  Rational) (hx : x ≠ 0) :
    Components.Basic.point x y ≠ 0 := by
  intro equal
  have real := congrArg (fun z : Canonical => z.re) equal
  exact hx real

end Purelib.Data.Gaussian.Components.Nonzero

end
