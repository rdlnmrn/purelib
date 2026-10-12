module
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Geometry.Plane.Point.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs

open Purelib.Geometry

/-!
# Divine Proportions, Chapter 9: finite oriented areas

An oriented polygon is represented by a finite `List` of points.  The
denominator-free primitive is twice its signed area; the book's signed area is
obtained by dividing that finite sum by two.  This keeps the cancellation and
characteristic assumptions visible while the core shoelace and
Bretschneider identities remain polynomial.
-/

@[expose] public section

namespace Purelib.Geometry.Plane.Point.Determinant

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- Oriented determinant of two position vectors. -/
def positionDeterminant (first second : Plane.Point K) : K
  :=
  first.x * second.y - second.x * first.y
end Purelib.Geometry.Plane.Point.Determinant

end
