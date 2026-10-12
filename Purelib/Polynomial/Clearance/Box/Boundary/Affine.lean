module
import Purelib.Geometry.Rational.Box.Square.Centered
public import Purelib.Polynomial.Clearance.Box.Boundary.Operations
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
public import Purelib.Polynomial.Clearance.Box.Boundary.Constant
public import Purelib.Polynomial.Clearance.Box.Boundary.Translated
public import Purelib.Polynomial.Dense.Gaussian.Linear.Affine

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Gaussian.Constants
import Purelib.Polynomial.Dense.Gaussian.Linear.Translated

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

section
@[expose] public section

/-!
# Choice-free winding of a Newton affine factor

The translated coordinate `Z-c` is represented by the exact two-coefficient
list `[1,-c]`.  Its four Cauchy indices are computed directly on the positive
square centered at `c`; multiplication by a nonzero constant slope is then
handled by the finite product formula.
-/

namespace Purelib.Polynomial.Clearance.Box.Boundary.Affine

/-- Exact quantitative clearance of a nonzero affine factor on a centered
square. -/
def affineCoordinate_boundaryClearance
    {s : Gaussian.Basic.Canonical} (slopeNonzero : s ≠ 0) (c : Gaussian.Basic.Canonical)
    {r : Fraction.Rational} (positive : 0 < r) :
    Clearance.Box.Boundary.Basic.BoundaryClearance
      (Dense.Gaussian.Linear.Affine.affineCoordinate s c) (Box.Square.Centered.Affine.centeredSquare c r positive.le) :=
        by
  exact (Clearance.Box.Boundary.Constant.gaussianConstant_boundaryClearance slopeNonzero
    (Box.Square.Centered.Affine.centeredSquare c r positive.le)).mul
      (Clearance.Box.Boundary.Translated.translatedCoordinate_boundaryClearance c positive)

/-- Quantitative clearance of a nonzero affine factor on an arbitrary
rectangle whose strict interior contains its zero. -/
def affineCoordinate_boundaryClearanceBox
    {s : Gaussian.Basic.Canonical} (slopeNonzero : s ≠ 0) (c : Gaussian.Basic.Canonical) {box : Box}
    (left : box.xLower < c.re) (right : c.re < box.xUpper)
    (below : box.yLower < c.im) (above : c.im < box.yUpper) :
    Clearance.Box.Boundary.Basic.BoundaryClearance
      (Dense.Gaussian.Linear.Affine.affineCoordinate s c) box :=
  (Clearance.Box.Boundary.Constant.gaussianConstant_boundaryClearance slopeNonzero box).mul
    (Clearance.Box.Boundary.Translated.Affine.translatedCoordinate_boundaryClearanceBox c left right below above)
end Purelib.Polynomial.Clearance.Box.Boundary.Affine

end
