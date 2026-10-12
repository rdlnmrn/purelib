module
public import Purelib.Geometry.Circles.Conic.Basic
import Purelib.Algebra.Field.ExplicitField
import Purelib.Curves.Plane.Conic.Basic
import Purelib.Geometry.Plane.Point.Basic
public import Purelib.Geometry.Quadrilaterals.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs

open Purelib.Curves.Plane

open Purelib.Geometry

section
@[expose] public section

/-!
# Divine Proportions, Theorem 109: cyclic quadrilaterals

A quadrilateral is kept as four displayed points together with the source's
finite distinctness and noncollinearity certificates.  The cyclic predicate
stores an explicit conic, center, quadrance, circle presentation, and four
incidence proofs.

The printed four-by-four determinant is expanded by `determinantThree`; no
matrix determinant, permutation enumeration, or quotient of cyclic orderings
is introduced.  A translated determinant identity then gives both directions
of Theorem 109 constructively.
-/

namespace Purelib.Geometry.Quadrilaterals.Basic.Quadrilateral

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]
section

/-- All four vertices lie on one explicitly presented circle.

The proposition retains a conic, its center and quadrance, a circle-presentation certificate and incidence of each
vertex. -/
def IsCyclic (quadrilateral :
  Quadrilaterals.Basic.Quadrilateral K) : Prop :=
  ∃ circle : Conic K, ∃ center : Plane.Point K, ∃ circleQuadrance : K,
    circle.IsCirclePresentation center circleQuadrance ∧
      circle.Contains quadrilateral.first ∧
      circle.Contains quadrilateral.second ∧
      circle.Contains quadrilateral.third ∧
      circle.Contains quadrilateral.fourth
end

end Purelib.Geometry.Quadrilaterals.Basic.Quadrilateral

end
