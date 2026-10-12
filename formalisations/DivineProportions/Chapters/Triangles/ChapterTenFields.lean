module
import Purelib.Algebra.Field.ExplicitField
import Purelib.Geometry.Triangles.FiniteField.Five.Classification
import Purelib.Geometry.Triangles.FiniteField.Three.Classification
public import Purelib.Geometry.Triangles.Right.Isosceles.Basic
public import Purelib.Algebra.Field.Finite.Five
public import Purelib.Algebra.Field.Finite.Three
import Purelib.Geometry.Triangles.NonNull.Basic
public import Purelib.Geometry.Triangles.Similarity.Basic
import Purelib.LinearAlgebra.Coordinates3.Vector

open Purelib.Algebra

open Purelib

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

namespace formalisations.DivineProportions.Chapters.Triangles.ChapterTenFields

variable {K : Type*} [Field.ExplicitField K]

namespace FieldThree

/-- The complete two-triangle form of Exercise 10.10. -/
theorem exercise_10_10 (left right : Geometry.Triangles.NonNull.Basic.NonNullTriangle Field.Finite.Three.Element) :
    left.Similar right ∧ (Geometry.Triangles.Right.Isosceles.Basic.NonNullTriangle.IsRightIsosceles left) ∧
      (Geometry.Triangles.Right.Isosceles.Basic.NonNullTriangle.IsRightIsosceles right) :=
  ⟨Geometry.Triangles.FiniteField.Three.Classification.exercise_10_10_similar left right,
    Geometry.Triangles.FiniteField.Three.Classification.exercise_10_10_right_isosceles left,
    Geometry.Triangles.FiniteField.Three.Classification.exercise_10_10_right_isosceles right⟩

end FieldThree

namespace FieldFive

/-- The complete non-null part of Exercise 10.11. -/
theorem exercise_10_11_nonNull
    (left right : Geometry.Triangles.NonNull.Basic.NonNullTriangle Field.Finite.Five.Element) :
    left.Similar right ∧
      (left.quadrances.t = left.quadrances.r ∨
        left.quadrances.t = left.quadrances.s ∨
        left.quadrances.r = left.quadrances.s) ∧
      (right.quadrances.t = right.quadrances.r ∨
        right.quadrances.t = right.quadrances.s ∨
        right.quadrances.r = right.quadrances.s) :=
  ⟨Geometry.Triangles.FiniteField.Five.Classification.exercise_10_11_similar left right,
    Geometry.Triangles.FiniteField.Five.Classification.exercise_10_11_isosceles left,
      Geometry.Triangles.FiniteField.Five.Classification.exercise_10_11_isosceles right⟩
end FieldFive

end formalisations.DivineProportions.Chapters.Triangles.ChapterTenFields

end
