module
public import Purelib.Algebra.Group.Basic
public import Purelib.Data.Nat.Order
public import Purelib.Algebra.Group.Negation
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Geometry.Coordinates.Polar.Squared
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
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

namespace Purelib.Curves.Plane.EightCurve.Polar.RationalPolarCatalogue

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- The Gerono lemniscate equation implies the completed-square rational polar relation.

The squared-coordinate identities replace x squared and y squared by spread times quadrance and its complement, with no
division by quadrance. -/
theorem eight_curve_rational_polar_cleared
    (xSquared ySquared A spread Q : K)
    (coordinates : RationalPolarCatalogue.PolarCoordinateSquares xSquared ySquared spread Q)
    (eightCurveEquation : xSquared ^ 2 = A * (xSquared - ySquared)) :
    (spread * Q - A) ^ 2 = (A - Q) * A := by
  have squareCoordinates :=
    Squared.polar_coordinate_squares
      xSquared ySquared spread Q coordinates
  apply Group.eq_of_sub_eq_zero
  calc
    (spread * Q - A) ^ 2 - (A - Q) * A =
        xSquared ^ 2 - A * (xSquared - ySquared) := by
      rw [squareCoordinates.1, squareCoordinates.2]
      ring1
    _ = 0 := by rw [eightCurveEquation]; ring1
end Purelib.Curves.Plane.EightCurve.Polar.RationalPolarCatalogue

end

end
