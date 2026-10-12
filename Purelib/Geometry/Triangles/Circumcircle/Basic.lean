module
public import Purelib.Geometry.Circles.Conic.Basic
import Purelib.Algebra.Field.ExplicitField
import Purelib.Curves.Plane.Conic.Basic
import Purelib.Geometry.Plane.Point.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
meta import Mathlib.Tactic.Linter.Lint

open Purelib.Curves.Plane

open Purelib.Geometry

section
@[expose] public section

/-!
# Divine Proportions, §16.1: diameters

The source's midpoint proof of Theorem 103 requires a non-null diameter side,
the same visible hypothesis as the already formalized midpoint-uniqueness
theorem.  The statement below exposes that characteristic-dependent omission.
-/

namespace Purelib.Curves.Plane.Conic

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

section

/-- A displayed circle through the three vertices of a triangle. -/
def IsCircumcircleOf (circle : Conic K)
    (first second third center : Plane.Point K) (circleQuadrance : K) : Prop :=
  circle.IsCirclePresentation center circleQuadrance ∧
    circle.Contains first ∧ circle.Contains second ∧ circle.Contains third
end

end Purelib.Curves.Plane.Conic

end
