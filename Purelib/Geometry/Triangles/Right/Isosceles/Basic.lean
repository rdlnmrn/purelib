module
public import Purelib.Geometry.Triangles.NonNull.Basic
import Purelib.Algebra.Field.ExplicitField
import Purelib.Geometry.Plane.Line.Incidence
import Purelib.Geometry.Plane.Line.Basic
import Purelib.Geometry.Plane.Point.Basic
import Purelib.LinearAlgebra.Coordinates3.Vector

open Purelib

open Purelib.Geometry.Plane.Line

open Purelib.Geometry.Triangles

section
@[expose] public section

/-!
# Divine Proportions, Exercises 10.10 and 10.11

The two small-field classifications are reduced to finite scalar certificates.
No list of field points, lines, or triangles is constructed.  The `F₅` null
case also makes explicit the boundary in the book's spread-based definition of
similarity: a triangle with two null sides has no vertex at which a spread is
defined.
-/

namespace Purelib.Geometry.Triangles.Right.Isosceles.Basic.NonNullTriangle

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]
section

variable [DecidableEq K]

/-- A right isosceles vertex at the first displayed point. -/
def RightIsoscelesAtFirst (triangle :
  NonNull.Basic.NonNullTriangle K) : Prop :=
  triangle.quadrances.r = triangle.quadrances.s ∧
    (Incidence.lineThrough triangle.second triangle.first
        triangle.firstSecondDistinct.symm).Perpendicular
      (Incidence.lineThrough triangle.third triangle.first
        triangle.firstThirdDistinct.symm)

/-- A right isosceles vertex at the second displayed point. -/
def RightIsoscelesAtSecond (triangle :
  NonNull.Basic.NonNullTriangle K) : Prop :=
  triangle.quadrances.t = triangle.quadrances.s ∧
    (Incidence.lineThrough triangle.first triangle.second
        triangle.firstSecondDistinct).Perpendicular
      (Incidence.lineThrough triangle.third triangle.second
        triangle.secondThirdDistinct.symm)

/-- A right isosceles vertex at the third displayed point. -/
def RightIsoscelesAtThird (triangle :
  NonNull.Basic.NonNullTriangle K) : Prop :=
  triangle.quadrances.t = triangle.quadrances.r ∧
    (Incidence.lineThrough triangle.first triangle.third
        triangle.firstThirdDistinct).Perpendicular
      (Incidence.lineThrough triangle.second triangle.third
        triangle.secondThirdDistinct)

/-- The three finite choices of a right isosceles vertex. -/
def IsRightIsosceles (triangle :
  NonNull.Basic.NonNullTriangle K) : Prop :=
  (RightIsoscelesAtFirst triangle) ∨
    (RightIsoscelesAtSecond triangle) ∨
    (RightIsoscelesAtThird triangle)

end

end Purelib.Geometry.Triangles.Right.Isosceles.Basic.NonNullTriangle

end
