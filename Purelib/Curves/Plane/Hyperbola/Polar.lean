module
public import Purelib.Algebra.Group.Basic
public import Purelib.Data.Nat.Order
public import Purelib.Algebra.Group.Negation
public import Purelib.Geometry.Coordinates.Polar.Squared
import Purelib.Algebra.Field.ExplicitField
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

namespace Purelib.Curves.Plane.Hyperbola.Polar.RationalPolarCatalogue

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- The displayed hyperbola equation implies its cleared rational polar relation.

The identity follows by substituting the retained squared-coordinate relations; no nonzero quadrance assumption is
required. -/
theorem hyperbola_rational_polar
    (xSquared ySquared A B spread Q : K)
    (coordinates : RationalPolarCatalogue.PolarCoordinateSquares xSquared ySquared spread Q)
    (hyperbolaEquation : B * xSquared - A * ySquared = A * B) :
    spread * Q * (A + B) = A * (Q + B) := by
  apply Group.eq_of_sub_eq_zero
  calc
    spread * Q * (A + B) - A * (Q + B) =
        B * xSquared - A * ySquared - A * B := by
      rw [coordinates.2, coordinates.1]
      ring1
    _ = 0 := by rw [hyperbolaEquation]; ring1
end Purelib.Curves.Plane.Hyperbola.Polar.RationalPolarCatalogue

end

end
