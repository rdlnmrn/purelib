module
import Purelib.Algebra.Field.ExplicitField
import Purelib.Geometry.Plane.Point.Basic
public import Purelib.Geometry.Plane.Point.Quadrance

open Purelib.Geometry

open Purelib.Geometry.Plane.Point

section
@[expose] public section

/-!
# Divine Proportions, Theorem 116: the Euler line

The centroid is an explicit finite affine combination.  The key identity is
the source's relation `G = (2/3)C + (1/3)O`, proved first for the already
formalized affine circumcenter and orthocenter weights and then transferred to
the geometric center constructions.  No completed line or infinite locus is
introduced: collinearity is the finite three-point determinant relation.
-/

namespace Purelib.Geometry.Triangles.Equilateral.Basic

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- A triangle is equilateral when its three finite quadrances agree. -/
def IsEquilateralTriangle (first second third :
  Plane.Point K) : Prop :=
  Quadrance.quadrance second third = Quadrance.quadrance first third ∧
    Quadrance.quadrance first third = Quadrance.quadrance first second
end Purelib.Geometry.Triangles.Equilateral.Basic

end
