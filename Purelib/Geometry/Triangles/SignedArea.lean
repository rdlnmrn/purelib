module
import Purelib.Algebra.Field.ExplicitField
import Purelib.Geometry.Plane.Line.Incidence
import Purelib.Geometry.Plane.Point.Basic
public import Purelib.Geometry.Plane.Point.Determinant
public import Purelib.Geometry.Triangles.Quadrea.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Tactic.Ring

open Purelib

open Purelib.Geometry

open Purelib.Geometry.Plane.Point

open Purelib.Geometry.Triangles

/-!
# Divine Proportions, Chapter 9: finite oriented areas

An oriented polygon is represented by a finite `List` of points.  The
denominator-free primitive is twice its signed area; the book's signed area is
obtained by dividing that finite sum by two.  This keeps the cancellation and
characteristic assumptions visible while the core shoelace and
Bretschneider identities remain polynomial.
-/

@[expose] public section

namespace Purelib.Geometry.Triangles.SignedArea

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- Twice the signed area of an oriented triangle. -/
def triangleDoubleSignedArea (first second third : Plane.Point
  K) : K :=
  Determinant.positionDeterminant first second + Determinant.positionDeterminant second third +
    Determinant.positionDeterminant third first

/-- The book's signed area of an oriented triangle. -/
def triangleSignedArea (first second third : Plane.Point K) : K
  :=
  triangleDoubleSignedArea first second third / 2

/-- The triangle quadrea is sixteen times the square of its signed area. -/
theorem triangle_quadrea_eq_sixteen_signed_area_square
    (first second third : Plane.Point K) (twoNonzero : (2 : K) ≠ 0) :
    Quadrea.Basic.quadrea first second third =
      16 * triangleSignedArea first second third ^ 2 := by
  have doubled :
      2 * triangleSignedArea first second third =
        triangleDoubleSignedArea first second third := by
    unfold triangleSignedArea
    calc
      2 * (triangleDoubleSignedArea first second third / 2) =
          (triangleDoubleSignedArea first second third / 2) * 2 := by ring1
      _ = triangleDoubleSignedArea first second third :=
        Algebra.Field.ExplicitField.div_mul_cancel _ twoNonzero
  calc
    Quadrea.Basic.quadrea first second third =
        4 * triangleDoubleSignedArea first second third ^ 2 := by
      rw [Quadrea.Basic.quadrea_coordinate_formula]
      unfold Plane.Line.Incidence.pointDeterminant triangleDoubleSignedArea Determinant.positionDeterminant
      ring1
    _ = 16 * triangleSignedArea first second third ^ 2 := by
      rw [← doubled]
      ring1
end Purelib.Geometry.Triangles.SignedArea

end
