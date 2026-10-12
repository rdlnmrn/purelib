module
import Purelib.Geometry.Plane.Point.Basic
public import Purelib.Geometry.Triangles.NonNull.Basic
import Purelib.Geometry.Triangles.Quadrance.Basic
public import Purelib.LinearAlgebra.Coordinates3.Vector.Permutation
import Purelib.Algebra.Field.ExplicitField

open Purelib

open Purelib.Geometry

open Purelib.Geometry.Triangles

open Purelib.LinearAlgebra.Coordinates3.Vector

section
@[expose] public section
namespace Purelib.Geometry.Triangles.Congruence.Basic
variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- The book's definition of congruence: equality of the unordered triple of side quadrances. No choice of a
corresponding side is hidden in the definition. -/
def CongruentTriangles
    (first second third otherFirst otherSecond otherThird : Plane.Point K) : Prop :=
  Permutation.SameEntries
    (Quadrance.Basic.triangleQuadrances first second third)
    (Quadrance.Basic.triangleQuadrances otherFirst otherSecond otherThird)
end Purelib.Geometry.Triangles.Congruence.Basic

end

section
@[expose] public section
namespace Purelib.Geometry.Triangles.NonNull.Basic.NonNullTriangle
variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]
section
variable [DecidableEq K]

/-- Congruence specialized to the vertices stored by two non-null triangles. -/
def Congruent (left right :
  NonNull.Basic.NonNullTriangle K) : Prop :=
  Geometry.Triangles.Congruence.Basic.CongruentTriangles left.first left.second left.third
    right.first right.second right.third
end
end Purelib.Geometry.Triangles.NonNull.Basic.NonNullTriangle

end
