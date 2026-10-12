module
import Purelib.Data.Gaussian.Basic
public import Purelib.Curves.Legendre.Polynomial
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Clearance.Box.Boundary.Operations
import Purelib.Polynomial.Dense.Gaussian.Linear.Translated
import Purelib.Polynomial.Winding.Box.Basic
import Purelib.Polynomial.Winding.Box.Product

open Purelib

open Purelib.Curves.Legendre

open Purelib.Geometry

open Purelib.Polynomial

open Purelib.Polynomial.Clearance.Box

open Purelib.Polynomial.Clearance.Box.Boundary.Basic

open Purelib.Polynomial.Dense.Gaussian.Linear.Translated

section
@[expose] public section

/-!
# One explicit rational Legendre crossing segment

This module certifies a single positive projected crossing of the moving
Legendre root over the fixed root at zero.  The parameter moves horizontally
from `1/4 + 2i` to `-1/4 + 2i`.  Broad chamber-owner boxes retain the
same three roots across the coefficient overlap, while much smaller sample
owners certify the change in left-to-right projection order.
-/

namespace Purelib.Curves.Legendre.Polynomial.Winding

/-- The product of the three retained affine factors has quadrupled box winding four when their individual windings sum
to four.

Each factor keeps its own boundary-clearance certificate on the same proper box; the finite product formula adds their
winding contributions. -/
theorem factors_winding_of_sum {lambda :
  Data.Gaussian.Basic.Canonical} {box : Rational.Box}
    (proper : box.Proper)
    (zeroClearance : Boundary.Basic.BoundaryClearance
      (translatedCoordinate 0) box)
    (movingClearance : Boundary.Basic.BoundaryClearance
      (translatedCoordinate lambda) box)
    (oneClearance : Boundary.Basic.BoundaryClearance
      (translatedCoordinate 1) box)
    (sum :
      Winding.Box.Basic.quadrupledBoxWinding
          (translatedCoordinate 0) box +
        Winding.Box.Basic.quadrupledBoxWinding
          (translatedCoordinate lambda) box +
        Winding.Box.Basic.quadrupledBoxWinding
          (translatedCoordinate 1) box = 4) :
    Winding.Box.Basic.quadrupledBoxWinding (Polynomial.factorsAt lambda) box = 4 := by
  rw [Polynomial.factorsAt,
    Winding.Box.Product.quadrupledBoxWinding_mul_of_boundaryClearances
      _ _ box proper
        (BoundaryClearance.mul
          zeroClearance movingClearance) oneClearance,
    Winding.Box.Product.quadrupledBoxWinding_mul_of_boundaryClearances
      _ _ box proper zeroClearance movingClearance]
  exact sum
end Purelib.Curves.Legendre.Polynomial.Winding

end
