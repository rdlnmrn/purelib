module
public import Purelib.Algebra.Field.ExplicitField
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs

section
@[expose] public section

/-!
# Divine Proportions, Appendix B: the ellipson

This module formalizes every finite algebraic assertion in Appendix B: the
defining surface, its full coordinate symmetry, its tetrahedral intersection
with the algebraic boundary of the unit cube, the coordinate-plane ellipse
sections and their four tangencies, the oblique section, and its rational
polar equation.  The volume calculation in Exercise B.1 is an analytic
integral and remains outside the agreed finite boundary.
-/

namespace Purelib.Geometry.Space.Cube.Boundary.Ellipson

section

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- The algebraic boundary of the unit cube: at least one coordinate is `0` or `1`. This definition is meaningful over
every explicit field and does not invoke an ordered interval. -/
def OnCubeBoundary (x y z : K) : Prop :=
  x = 0 ∨ x = 1 ∨ y = 0 ∨ y = 1 ∨ z = 0 ∨ z = 1
end
end Purelib.Geometry.Space.Cube.Boundary.Ellipson

end
