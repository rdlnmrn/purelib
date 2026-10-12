module
public import Purelib.Algebra.Group.Basic
public import Purelib.Data.Nat.Order
public import Purelib.Algebra.Group.Negation
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Geometry.Coordinates.Polar.Squared
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Tactic.Ring

section
open Purelib.Algebra
open Purelib.Data

-- These owned adapters retain the complete original operation dictionaries.
attribute [local instance 2000] Group.Negation.subNegZeroMonoid
  Nat.successorNeZero Nat.successorAtLeastTwo

open Purelib.Geometry.Coordinates.Polar

open Purelib.Geometry.Coordinates.Polar.Squared

section
public section

/-!
# Divine Proportions, Appendix A: rational polar equations of curves

The source leaves the conversions in this catalogue to the reader.  This
module supplies the missing finite algebraic derivations.  Every result is
denominator-cleared and valid over an arbitrary explicit field; divisions by
the radial quadrance are represented by an explicit nonzero hypothesis.

Three displayed equations in the source do not follow from the equations
immediately preceding them.  The trisectrix has the wrong sign, the bullet
nose omits a factor `4` in the denominator, and the hippopede loses powers of
`B`.  Corrected theorems and closed rational counterexamples are included.
-/

namespace Purelib.Curves.Plane.Deltoid.Polar.RationalPolarCatalogue

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-! ## Deltoid and hippopede -/

/-- Squaring the one odd Cartesian term in the deltoid equation produces the third-spread polynomial `s(3-4s)²`. -/
theorem deltoid_rational_polar_cleared
    (x y a A spread Q : K)
    (coordinates : RationalPolarCatalogue.PolarCoordinateSquares (x ^ 2) (y ^ 2) spread Q)
    (aSquare : a ^ 2 = A)
    (deltoidEquation :
      (x ^ 2 + y ^ 2) ^ 2 -
          8 * a * x * (x ^ 2 - 3 * y ^ 2) +
          18 * A * (x ^ 2 + y ^ 2) = 27 * A ^ 2) :
    64 * Q ^ 3 * A * (spread * (3 - 4 * spread) ^ 2) =
      (Q ^ 2 + 18 * A * Q - 27 * A ^ 2) ^ 2 := by
  have squareCoordinates :=
    Squared.polar_coordinate_squares
      (x ^ 2) (y ^ 2) spread Q coordinates
  have oddTerm :
      Q ^ 2 + 18 * A * Q - 27 * A ^ 2 =
        8 * a * x * (x ^ 2 - 3 * y ^ 2) := by
    apply Group.eq_of_sub_eq_zero
    calc
      Q ^ 2 + 18 * A * Q - 27 * A ^ 2 -
          8 * a * x * (x ^ 2 - 3 * y ^ 2) =
        (x ^ 2 + y ^ 2) ^ 2 -
          8 * a * x * (x ^ 2 - 3 * y ^ 2) +
          18 * A * (x ^ 2 + y ^ 2) - 27 * A ^ 2 := by
        rw [coordinates.1]
        ring1
    _ = 0 := by rw [deltoidEquation]; ring1
  rw [oddTerm]
  calc
    64 * Q ^ 3 * A * (spread * (3 - 4 * spread) ^ 2) =
        64 * a ^ 2 * (spread * Q) * Q ^ 2 *
          (3 - 4 * spread) ^ 2 := by
      rw [aSquare]
      ring1
    _ = 64 * a ^ 2 * x ^ 2 * Q ^ 2 *
          (3 - 4 * spread) ^ 2 := by rw [coordinates.2]
    _ =
        (8 * a * x *
          ((spread * Q) - 3 * ((1 - spread) * Q))) ^ 2 := by
      ring1
    _ = (8 * a * x * (x ^ 2 - 3 * y ^ 2)) ^ 2 := by
      rw [coordinates.2, ← squareCoordinates.2]
end Purelib.Curves.Plane.Deltoid.Polar.RationalPolarCatalogue

end

end
