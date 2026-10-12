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

namespace Purelib.Curves.Plane.BulletNose.Polar.RationalPolarCatalogue

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- The bullet-nose equation gives the completed-square rational polar identity.

The cleared expression includes the factor four in the radial term and follows from the displayed squared-coordinate
relations over any explicit field. -/
theorem bullet_nose_rational_polar_corrected
    (xSquared ySquared A B spread Q : K)
    (coordinates : RationalPolarCatalogue.PolarCoordinateSquares xSquared ySquared spread Q)
    (bulletNoseEquation :
      A * ySquared - B * xSquared = xSquared * ySquared) :
    (2 * Q * spread - (A + B + Q)) ^ 2 =
      (A + B + Q) ^ 2 - 4 * A * Q := by
  have squareCoordinates :=
    Squared.polar_coordinate_squares
      xSquared ySquared spread Q coordinates
  apply Group.eq_of_sub_eq_zero
  calc
    (2 * Q * spread - (A + B + Q)) ^ 2 -
        ((A + B + Q) ^ 2 - 4 * A * Q) =
      4 * Q *
        (A * (1 - spread) - B * spread -
          spread * (1 - spread) * Q) := by ring1
    _ = 4 *
        (A * ySquared - B * xSquared - xSquared * ySquared) := by
      rw [squareCoordinates.1, squareCoordinates.2]
      ring1
    _ = 0 := by rw [bulletNoseEquation]; ring1
end Purelib.Curves.Plane.BulletNose.Polar.RationalPolarCatalogue

end

end
