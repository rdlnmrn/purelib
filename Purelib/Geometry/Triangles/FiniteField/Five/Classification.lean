module
public import Purelib.Geometry.Triangles.Similarity.Basic
import Purelib.Geometry.Triangles.NonNull.Spread
import Purelib.Geometry.Triangles.NonNull.Basic
public import Purelib.Algebra.Field.Finite.Five
import Purelib.Algebra.Field.ExplicitField
import Purelib.Geometry.Plane.Line.Incidence
import Purelib.Geometry.Plane.Point.Basic
import Purelib.Geometry.Triangles.Quadrea.Basic
import Purelib.Geometry.Trigonometry.QuadTriple.Basic
import Purelib.LinearAlgebra.Coordinates3.Vector.Permutation
import Purelib.LinearAlgebra.Coordinates3.Vector

open Purelib

open Purelib.Algebra.Field.Finite

open Purelib.Geometry

open Purelib.Geometry.Plane.Line

open Purelib.Geometry.Triangles

open Purelib.Geometry.Trigonometry

open Purelib.LinearAlgebra.Coordinates3.Vector

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

namespace Purelib.Geometry.Triangles.FiniteField.Five.Classification

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

section

/-- The quadrea of a noncollinear triangle over the field with five elements is one or four. -/
public theorem quadrea_values
    (first second third : Plane.Point Five.Element)
    (notCollinear : ¬ Incidence.Collinear first second third) :
    Quadrea.Basic.quadrea first second third = 1 ∨ Quadrea.Basic.quadrea first second third = 4 := by
  have determinantNonzero : Incidence.pointDeterminant first second third ≠ 0 := by
    intro determinantZero
    exact notCollinear
      ((Incidence.collinear_iff_pointDeterminant_eq_zero first second third).2
        determinantZero)
  rcases Five.square_eq_one_or_four_of_nonzero
      (Incidence.pointDeterminant first second third) determinantNonzero with
    squareOne | squareFour
  · apply Or.inr
    rw [Quadrea.Basic.quadrea_coordinate_formula, squareOne]
    decide
  · apply Or.inl
    rw [Quadrea.Basic.quadrea_coordinate_formula, squareFour]
    decide

/-- Three nonzero scalars over the field with five elements with Archimedes value one or four have two equal entries. -/
private theorem scalar_isosceles
    (q₁ q₂ q₃ : Five.Element)
    (firstNonzero : q₁ ≠ 0) (secondNonzero : q₂ ≠ 0)
    (thirdNonzero : q₃ ≠ 0)
    (areaValue : QuadTriple.Basic.archimedesFunction q₁ q₂ q₃ = 1 ∨
      QuadTriple.Basic.archimedesFunction q₁ q₂ q₃ = 4) :
    q₁ = q₂ ∨ q₁ = q₃ ∨ q₂ = q₃ := by
  decide +revert

/-- The three cleared spread laws over the field with five elements force a permutation of the spread triple three,
three, one.

All three quadrances are nonzero and the common area is one or four. -/
private theorem scalar_spread_pattern
    (q₁ q₂ q₃ s₁ s₂ s₃ : Five.Element)
    (firstNonzero : q₁ ≠ 0) (secondNonzero : q₂ ≠ 0)
    (thirdNonzero : q₃ ≠ 0)
    (areaValue : QuadTriple.Basic.archimedesFunction q₁ q₂ q₃ = 1 ∨
      QuadTriple.Basic.archimedesFunction q₁ q₂ q₃ = 4)
    (firstProduct :
      QuadTriple.Basic.archimedesFunction q₁ q₂ q₃ = 4 * q₂ * q₃ * s₁)
    (secondProduct :
      QuadTriple.Basic.archimedesFunction q₁ q₂ q₃ = 4 * q₁ * q₃ * s₂)
    (thirdProduct :
      QuadTriple.Basic.archimedesFunction q₁ q₂ q₃ = 4 * q₁ * q₂ * s₃) :
    Permutation.RepeatedEntryPattern (3 : Five.Element) 1 ⟨s₁, s₂, s₃⟩ := by
  unfold Permutation.RepeatedEntryPattern
  decide +revert

/-- The Archimedes expression of the side quadrances of a non-null triangle over the field with five elements is one or
four. -/
private theorem triangle_area_values (triangle :
  NonNull.Basic.NonNullTriangle Five.Element) :
    QuadTriple.Basic.archimedesFunction triangle.quadrances.t
        triangle.quadrances.r triangle.quadrances.s = 1 ∨
      QuadTriple.Basic.archimedesFunction triangle.quadrances.t
        triangle.quadrances.r triangle.quadrances.s = 4 := by
  exact Geometry.Triangles.FiniteField.Five.Classification.quadrea_values triangle.first triangle.second triangle.third
    triangle.notCollinear

/-- The spreads of a non-null triangle over the field with five elements are a permutation of three, three, one. -/
theorem spread_pattern (triangle :
  NonNull.Basic.NonNullTriangle Five.Element) :
    Permutation.RepeatedEntryPattern (3 : Five.Element) 1 triangle.spreads := by
  have products := triangle.quadrea_spread_products
  exact Geometry.Triangles.FiniteField.Five.Classification.scalar_spread_pattern triangle.quadrances.t
    triangle.quadrances.r triangle.quadrances.s
    triangle.spreads.t triangle.spreads.r triangle.spreads.s
    triangle.firstQuadranceNonzero triangle.secondQuadranceNonzero
    triangle.thirdQuadranceNonzero (Geometry.Triangles.FiniteField.Five.Classification.triangle_area_values triangle)
    products.1 products.2.1 products.2.2

/-- Exercise 10.11: every non-null triangle over `F₅` is isosceles. -/
theorem exercise_10_11_isosceles (triangle :
  NonNull.Basic.NonNullTriangle Five.Element) :
    triangle.quadrances.t = triangle.quadrances.r ∨
      triangle.quadrances.t = triangle.quadrances.s ∨
      triangle.quadrances.r = triangle.quadrances.s :=
  Geometry.Triangles.FiniteField.Five.Classification.scalar_isosceles triangle.quadrances.t triangle.quadrances.r
    triangle.quadrances.s triangle.firstQuadranceNonzero
    triangle.secondQuadranceNonzero triangle.thirdQuadranceNonzero
    (Geometry.Triangles.FiniteField.Five.Classification.triangle_area_values triangle)

/-- Exercise 10.11: any two non-null triangles over `F₅` have the same unordered spread triple `{3,3,1}`. -/
theorem exercise_10_11_similar
    (left right : NonNull.Basic.NonNullTriangle Five.Element) : left.Similar right :=
  Permutation.sameEntries_of_repeatedEntryPattern (Geometry.Triangles.FiniteField.Five.Classification.spread_pattern
    left)
    (Geometry.Triangles.FiniteField.Five.Classification.spread_pattern right)
end

end Purelib.Geometry.Triangles.FiniteField.Five.Classification

end
