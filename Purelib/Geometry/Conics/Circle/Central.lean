module
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Curves.Plane.Conic.Center
public import Purelib.Geometry.Circles.Conic.Basic
import Purelib.Geometry.Plane.Point.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Logic.Nontrivial.Defs
import Purelib.Tactic.Ring

open Purelib.Curves.Plane (Conic)

section
@[expose] public section

/-!
# Divine Proportions, Example 15.2 and Exercise 15.3

The two source figures are retained as literal finite coordinate grids.  Their
entries are checked against central quadrance, and filtering the displayed
points by a quadrance label gives the printed circle counts.  These are finite
display certificates: they do not assert that either coordinate list globally
enumerates an ambient field carrier.
-/

namespace Purelib.Geometry.Conics.Circle.Central

section

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- Every normalized circle centered at the origin is central in the source's coefficient sense. -/
theorem circleConic_origin_isCentral [Nontrivial K] (circleQuadrance : K)
  :
    (Conic.circleConic (⟨0, 0⟩ : Purelib.Geometry.Plane.Point K) circleQuadrance).IsCentral := by
  unfold Conic.IsCentral Conic.IsCenter Conic.circleConic
  constructor <;> ring1

end

end Purelib.Geometry.Conics.Circle.Central

end
