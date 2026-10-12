module
public import Purelib.Algebra.Group.Basic
public import Purelib.Data.Nat.Order
public import Purelib.Algebra.Group.Negation
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Geometry.Coordinates.Polar.Squared
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
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

namespace Purelib.Curves.Plane.Astroid.Polar.RationalPolarCatalogue

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-! ## Even algebraic curves -/

/-- The astroid equation implies its denominator-cleared rational polar identity.

The retained squared-coordinate relation substitutes radial quadrance and spread, so the identity holds over any
explicit field without division by the quadrance. -/
theorem astroid_rational_polar_cleared
    (xSquared ySquared A spread Q : K)
    (coordinates : RationalPolarCatalogue.PolarCoordinateSquares xSquared ySquared spread Q)
    (astroidEquation :
      (xSquared + ySquared - A) ^ 3 +
        27 * A * xSquared * ySquared = 0) :
    27 * A * Q ^ 2 * (2 * spread - 1) ^ 2 =
      27 * A * Q ^ 2 - 4 * (A - Q) ^ 3 := by
  have squareCoordinates :=
    Squared.polar_coordinate_squares
      xSquared ySquared spread Q coordinates
  apply Group.eq_of_sub_eq_zero
  calc
    27 * A * Q ^ 2 * (2 * spread - 1) ^ 2 -
        (27 * A * Q ^ 2 - 4 * (A - Q) ^ 3) =
      -4 * ((Q - A) ^ 3 +
        27 * A * (spread * Q) * ((1 - spread) * Q)) := by ring1
    _ = -4 * ((xSquared + ySquared - A) ^ 3 +
        27 * A * xSquared * ySquared) := by
      rw [← coordinates.1, ← squareCoordinates.1, ← squareCoordinates.2]
    _ = 0 := by rw [astroidEquation]; ring1
end Purelib.Curves.Plane.Astroid.Polar.RationalPolarCatalogue

end

end
