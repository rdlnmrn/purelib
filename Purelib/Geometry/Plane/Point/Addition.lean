module
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Geometry.Plane.Point.Basic
import Mathlib.Algebra.Ring.Defs

open Purelib.Geometry

section
@[expose] public section

/-!
# Divine Proportions, Chapter 23: physics applications

The calculus passages in the source are retained through their finite
polynomial stationarity equations.  Extremum conclusions are separated from
those equations, so no completed real line, limit, or general derivative
operator enters the formalization.
-/

namespace Purelib.Geometry.Plane.Point.Addition

section

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- Add two Cartesian points coordinatewise. -/
def pointAdd (left right : Purelib.Geometry.Plane.Point K) :
  Purelib.Geometry.Plane.Point K :=
  ⟨left.x + right.x, left.y + right.y⟩
end
end Purelib.Geometry.Plane.Point.Addition

end
