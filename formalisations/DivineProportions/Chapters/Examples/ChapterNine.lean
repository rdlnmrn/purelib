module
import Purelib.Algebra.Field.ExplicitField
import Purelib.Geometry.Plane.Point.Basic
import Purelib.Geometry.Plane.Point.Determinant
public import Purelib.Geometry.Polygons.SignedArea.Basic
import Purelib.Tactic.Ring

open Purelib.Geometry

section
/-!
# Divine Proportions, Chapter 9: finite oriented areas

An oriented polygon is represented by a finite `List` of points.  The
denominator-free primitive is twice its signed area; the book's signed area is
obtained by dividing that finite sum by two.  This keeps the cancellation and
characteristic assumptions visible while the core shoelace and
Bretschneider identities remain polynomial.
-/

@[expose] public section

namespace formalisations.DivineProportions.Chapters.Examples.ChapterNine

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

open Purelib.Algebra.Field in
open Purelib.Geometry.Plane.Point in
open Purelib.Geometry.Polygons.SignedArea in
/-- Exercise 9.4: exact signed area of the displayed quadrilateral. -/
theorem exercise_9_4 (k l m n : K) :
    let first : Plane.Point K := ⟨k, 0⟩
    let second : Plane.Point K := ⟨l, 0⟩
    let third : Plane.Point K := ⟨l, n⟩
    let fourth : Plane.Point K := ⟨k, m⟩
    Basic.polygonSignedArea [first, second, third, fourth] =
      (m + n) * (l - k) / 2 := by
  dsimp only
  simp only [Basic.polygonSignedArea, Basic.polygonDoubleSignedArea,
    Basic.polygonDoubleSignedAreaAux, Determinant.positionDeterminant]
  simp only [ExplicitField.div_eq_mul_inv]
  ring1
end formalisations.DivineProportions.Chapters.Examples.ChapterNine

end

end
