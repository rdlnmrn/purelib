module
import Purelib.Geometry.Triangles.Sides.Nonparallel
import Purelib.Algebra.Field.ExplicitField
import Purelib.Geometry.Plane.Line.Basic
public import Purelib.Geometry.Plane.Line.Incidence
import Purelib.Geometry.Plane.Line.Relations
import Purelib.Geometry.Plane.Point.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs

open Purelib.Geometry.Plane (Line)

open Purelib.Geometry

open Purelib.Geometry.Plane.Line

open Purelib.Geometry.Plane.Line.Basic

@[expose] public section

/-!
# Divine Proportions, Exercises 3.11–3.12

A triangle is kept as three displayed points with explicit distinctness and
noncollinearity certificates.  Right vertices are perpendicularity equations
between its three finite side lines.  Null-side impossibility exposes the
book's standing characteristic-not-two assumption.
-/

namespace Purelib.Geometry.Triangles.Right.Uniqueness

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- Exercise 3.11: among the three displayed vertex-perpendicularity conditions of a noncollinear triangle, no two can
hold simultaneously. -/
theorem right_vertex_unique [DecidableEq K]
    (first second third : Purelib.Geometry.Plane.Point K)
    (firstSecondDistinct : first ≠ second)
    (firstThirdDistinct : first ≠ third)
    (secondThirdDistinct : second ≠ third)
    (notCollinear : ¬ Incidence.Collinear first second third) :
    let firstSide := Incidence.lineThrough first second firstSecondDistinct
    let secondSide := Incidence.lineThrough second third secondThirdDistinct
    let thirdSide := Incidence.lineThrough first third firstThirdDistinct
    let rightAtFirst := firstSide.Perpendicular thirdSide
    let rightAtSecond := firstSide.Perpendicular secondSide
    let rightAtThird := thirdSide.Perpendicular secondSide
    ¬ (rightAtFirst ∧ rightAtSecond) ∧
      ¬ (rightAtSecond ∧ rightAtThird) ∧
      ¬ (rightAtThird ∧ rightAtFirst) := by
  dsimp only
  rcases Triangles.Sides.Nonparallel.triangle_side_pairs_nonparallel first second third
      firstSecondDistinct firstThirdDistinct secondThirdDistinct
      notCollinear with
    ⟨firstSecondNonparallel, secondThirdNonparallel,
      thirdFirstNonparallel⟩
  constructor
  · rintro ⟨rightAtFirst, rightAtSecond⟩
    apply secondThirdNonparallel
    exact Line.parallel_symm (Relations.exercise_3_5
      (Incidence.lineThrough first third firstThirdDistinct)
      (Incidence.lineThrough first second firstSecondDistinct)
      (Incidence.lineThrough second third secondThirdDistinct)
      (Line.perpendicular_symm rightAtFirst) rightAtSecond)
  constructor
  · rintro ⟨rightAtSecond, rightAtThird⟩
    apply thirdFirstNonparallel
    exact Line.parallel_symm (Relations.exercise_3_5
      (Incidence.lineThrough first second firstSecondDistinct)
      (Incidence.lineThrough second third secondThirdDistinct)
      (Incidence.lineThrough first third firstThirdDistinct)
      rightAtSecond (Line.perpendicular_symm rightAtThird))
  · rintro ⟨rightAtThird, rightAtFirst⟩
    apply firstSecondNonparallel
    exact Line.parallel_symm (Relations.exercise_3_5
      (Incidence.lineThrough second third secondThirdDistinct)
      (Incidence.lineThrough first third firstThirdDistinct)
      (Incidence.lineThrough first second firstSecondDistinct)
      (Line.perpendicular_symm rightAtThird)
      (Line.perpendicular_symm rightAtFirst))
end Purelib.Geometry.Triangles.Right.Uniqueness

end
