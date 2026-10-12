module

import Purelib.Algebra.Field.ExplicitField
public import Purelib.Algebra.Field.Finite.Five
import Purelib.Geometry.Plane.Line.Incidence
import Purelib.Geometry.Plane.Line.Quadrance
public import Purelib.Geometry.Plane.Line.Spread
import Purelib.Geometry.Plane.Point.Basic
import Purelib.Geometry.Plane.Point.Quadrance
import Purelib.Geometry.Plane.Line.Basic
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

open Purelib.Algebra.Field.Finite

open Purelib.Geometry

open Purelib.Geometry.Plane.Line

open Purelib.Geometry.Plane.Point

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

namespace Purelib.Geometry.Triangles.FiniteField.Five.Null.Singly.Basic

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

section

set_option genInjectivity false in
/-- A null triangle with exactly the first opposite side null. The other two sides are retained as explicit nonzero
quadrances, so the spread at the first vertex is the sole vertex spread defined by the book. -/
structure SinglyNullAtFirst where
  /-- The first vertex, opposite the unique null side. -/ first : Geometry.Plane.Point Five.Element
  /-- The second vertex of the displayed triangle. -/ second : Geometry.Plane.Point Five.Element
  /-- The third vertex of the displayed triangle. -/ third : Geometry.Plane.Point Five.Element
  /-- The three vertices are not collinear. -/ notCollinear : ¬ Incidence.Collinear first second third
  /-- The side opposite the first vertex has zero quadrance. -/ firstQuadranceZero : Quadrance.quadrance second third =
    0
  /-- The side opposite the second vertex has nonzero quadrance. -/ secondQuadranceNonzero : Quadrance.quadrance first
    third ≠ 0
  /-- The side opposite the third vertex has nonzero quadrance. -/ thirdQuadranceNonzero : Quadrance.quadrance first
    second ≠ 0

constructive_injectivity SinglyNullAtFirst

namespace SinglyNullAtFirst

/-- The first and second vertices are distinct because their quadrance is nonzero. -/
theorem firstSecondDistinct
  (triangle : SinglyNullAtFirst) :
    triangle.first ≠ triangle.second := by
  intro equalPoints
  apply triangle.thirdQuadranceNonzero
  calc
    Quadrance.quadrance triangle.first triangle.second =
        Quadrance.quadrance triangle.second triangle.second := by rw [equalPoints]
    _ = 0 := Quadrance.quadrance_self triangle.second

/-- The first and third vertices are distinct because their quadrance is nonzero. -/
theorem firstThirdDistinct
  (triangle : SinglyNullAtFirst) :
    triangle.first ≠ triangle.third := by
  intro equalPoints
  apply triangle.secondQuadranceNonzero
  calc
    Quadrance.quadrance triangle.first triangle.third =
        Quadrance.quadrance triangle.third triangle.third := by rw [equalPoints]
    _ = 0 := Quadrance.quadrance_self triangle.third

/-- The line from the first to the second vertex is non-null. -/
theorem firstSecondNonNull
  (triangle : SinglyNullAtFirst) :
    ¬ (Incidence.lineThrough triangle.first triangle.second
      triangle.firstSecondDistinct).IsNull := by
  intro nullSide
  exact triangle.thirdQuadranceNonzero
    ((Quadrance.null_line_iff_quadrance_zero triangle.first triangle.second
      triangle.firstSecondDistinct).1 nullSide)

/-- The line from the first to the third vertex is non-null. -/
theorem firstThirdNonNull
  (triangle : SinglyNullAtFirst) :
    ¬ (Incidence.lineThrough triangle.first triangle.third
      triangle.firstThirdDistinct).IsNull := by
  intro nullSide
  exact triangle.secondQuadranceNonzero
    ((Quadrance.null_line_iff_quadrance_zero triangle.first triangle.third
      triangle.firstThirdDistinct).1 nullSide)

/-- The reversed line from the second to the first vertex is non-null. -/
theorem secondFirstNonNull
  (triangle : SinglyNullAtFirst) :
    ¬ (Incidence.lineThrough triangle.second triangle.first
      triangle.firstSecondDistinct.symm).IsNull := by
  intro nullSide
  apply triangle.thirdQuadranceNonzero
  calc
    Quadrance.quadrance triangle.first triangle.second =
        Quadrance.quadrance triangle.second triangle.first :=
      Quadrance.quadrance_symm triangle.first triangle.second
    _ = 0 :=
      (Quadrance.null_line_iff_quadrance_zero triangle.second triangle.first
        triangle.firstSecondDistinct.symm).1 nullSide

/-- The reversed line from the third to the first vertex is non-null. -/
theorem thirdFirstNonNull
  (triangle : SinglyNullAtFirst) :
    ¬ (Incidence.lineThrough triangle.third triangle.first
      triangle.firstThirdDistinct.symm).IsNull := by
  intro nullSide
  apply triangle.secondQuadranceNonzero
  calc
    Quadrance.quadrance triangle.first triangle.third =
        Quadrance.quadrance triangle.third triangle.first :=
      Quadrance.quadrance_symm triangle.first triangle.third
    _ = 0 :=
      (Quadrance.null_line_iff_quadrance_zero triangle.third triangle.first
        triangle.firstThirdDistinct.symm).1 nullSide

/-- The only spread defined at a vertex of this singly-null triangle. -/
def oppositeSpread (triangle :
  SinglyNullAtFirst) : Five.Element :=
  Spread.spread
    (Incidence.lineThrough triangle.second triangle.first
      triangle.firstSecondDistinct.symm)
    (Incidence.lineThrough triangle.third triangle.first
      triangle.firstThirdDistinct.symm)
    triangle.secondFirstNonNull triangle.thirdFirstNonNull
end SinglyNullAtFirst
end

end Purelib.Geometry.Triangles.FiniteField.Five.Null.Singly.Basic

end
