module
public import Purelib.Algebra.Field.Finite.Three
public import Purelib.Geometry.Triangles.Similarity.Basic
import Purelib.Geometry.Triangles.NonNull.Spread
import Purelib.Geometry.Triangles.NonNull.Basic
import Purelib.Algebra.Field.ExplicitField
import Purelib.Geometry.Plane.Line.Incidence
public import Purelib.Geometry.Plane.Line.Quadrance
import Purelib.Geometry.Plane.Point.Basic
import Purelib.Geometry.Plane.Point.Quadrance
import Purelib.Geometry.Triangles.Quadrea.Basic
public import Purelib.Geometry.Triangles.Right.Isosceles.Basic
import Purelib.Geometry.Triangles.Right.Quadrance
import Purelib.Geometry.Trigonometry.QuadTriple.Basic
import Purelib.LinearAlgebra.Coordinates3.Vector.Permutation
import Purelib.Geometry.Plane.Line.Basic
import Purelib.Tactic.Ring

open Purelib.Geometry.Plane (Line)

open Purelib

open Purelib.Algebra.Field.Finite

open Purelib.Geometry

open Purelib.Geometry.Plane.Line

open Purelib.Geometry.Plane.Point

open Purelib.Geometry.Triangles

open Purelib.Geometry.Triangles.Right

open Purelib.Geometry.Triangles.Right.Isosceles.Basic

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

namespace Purelib.Geometry.Triangles.FiniteField.Three.Classification

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

section

/-- Distinct points over the field with three elements have nonzero quadrance. -/
theorem quadrance_ne_zero_of_distinct
    (first second : Geometry.Plane.Point Three.Element) (distinct : first ≠ second) :
    Quadrance.quadrance first second ≠ 0 := by
  rcases first with ⟨firstX, firstY⟩
  rcases second with ⟨secondX, secondY⟩
  unfold Quadrance.quadrance
  decide +revert

/-- Every source triangle over `F₃` is automatically non-null. -/
def nonNullTriangle (first second third :
  Geometry.Plane.Point Three.Element)
    (notCollinear : ¬ Incidence.Collinear first second third) :
    NonNull.Basic.NonNullTriangle Three.Element :=
  let firstSecondDistinct : first ≠ second := by
    intro equalPoints
    apply notCollinear
    apply (Incidence.collinear_iff_pointDeterminant_eq_zero first second third).2
    rw [equalPoints]
    unfold Line.Incidence.pointDeterminant
    ring1
  let firstThirdDistinct : first ≠ third := by
    intro equalPoints
    apply notCollinear
    apply (Incidence.collinear_iff_pointDeterminant_eq_zero first second third).2
    rw [equalPoints]
    unfold Line.Incidence.pointDeterminant
    ring1
  let secondThirdDistinct : second ≠ third := by
    intro equalPoints
    apply notCollinear
    apply (Incidence.collinear_iff_pointDeterminant_eq_zero first second third).2
    rw [equalPoints]
    unfold Line.Incidence.pointDeterminant
    ring1
  {
  first := first
  second := second
  third := third
  notCollinear := notCollinear
  firstSecondDistinct := firstSecondDistinct
  firstThirdDistinct := firstThirdDistinct
  secondThirdDistinct := secondThirdDistinct
  firstSecondNonNull := by
    intro nullSide
    exact quadrance_ne_zero_of_distinct first second
      firstSecondDistinct
      ((Quadrance.null_line_iff_quadrance_zero first second
        firstSecondDistinct).1 nullSide)
  firstThirdNonNull := by
    intro nullSide
    exact quadrance_ne_zero_of_distinct first third
      firstThirdDistinct
      ((Quadrance.null_line_iff_quadrance_zero first third
        firstThirdDistinct).1 nullSide)
  secondThirdNonNull := by
    intro nullSide
    exact quadrance_ne_zero_of_distinct second third
      secondThirdDistinct
      ((Quadrance.null_line_iff_quadrance_zero second third
        secondThirdDistinct).1 nullSide)
  }

/-- Three nonzero scalars with nonzero Archimedes expression over the field with three elements satisfy an isosceles
right-triangle pattern.

One pair is equal and its sum is the remaining entry. -/
private theorem quadrance_pattern
    (q₁ q₂ q₃ : Three.Element)
    (firstNonzero : q₁ ≠ 0) (secondNonzero : q₂ ≠ 0)
    (thirdNonzero : q₃ ≠ 0)
    (areaNonzero : QuadTriple.Basic.archimedesFunction q₁ q₂ q₃ ≠ 0) :
    (q₂ = q₃ ∧ q₂ + q₃ = q₁) ∨
      (q₁ = q₃ ∧ q₁ + q₃ = q₂) ∨
      (q₁ = q₂ ∧ q₁ + q₂ = q₃) := by
  decide +revert

/-- The three cleared spread laws over the field with three elements force a permutation of the spread triple two, two,
one.

The three quadrances and their Archimedes expression are nonzero. -/
private theorem scalar_spread_pattern
    (q₁ q₂ q₃ s₁ s₂ s₃ : Three.Element)
    (firstNonzero : q₁ ≠ 0) (secondNonzero : q₂ ≠ 0)
    (thirdNonzero : q₃ ≠ 0)
    (areaNonzero : QuadTriple.Basic.archimedesFunction q₁ q₂ q₃ ≠ 0)
    (firstProduct :
      QuadTriple.Basic.archimedesFunction q₁ q₂ q₃ = 4 * q₂ * q₃ * s₁)
    (secondProduct :
      QuadTriple.Basic.archimedesFunction q₁ q₂ q₃ = 4 * q₁ * q₃ * s₂)
    (thirdProduct :
      QuadTriple.Basic.archimedesFunction q₁ q₂ q₃ = 4 * q₁ * q₂ * s₃) :
    Permutation.RepeatedEntryPattern (2 : Three.Element) 1 ⟨s₁, s₂, s₃⟩ := by
  unfold Permutation.RepeatedEntryPattern
  decide +revert

/-- The spreads of a non-null triangle over the field with three elements are a permutation of two, two, one. -/
theorem spread_pattern (triangle :
  NonNull.Basic.NonNullTriangle Three.Element) :
    Permutation.RepeatedEntryPattern (2 : Three.Element) 1 triangle.spreads := by
  have areaNonzero :
      Quadrea.Basic.quadrea triangle.first triangle.second triangle.third ≠ 0 :=
    (Quadrea.Basic.quadrea_ne_zero_iff_not_collinear triangle.first triangle.second
      triangle.third (by decide : (2 : Three.Element) ≠ 0)).2
      triangle.notCollinear
  have products := triangle.quadrea_spread_products
  exact scalar_spread_pattern triangle.quadrances.t
    triangle.quadrances.r triangle.quadrances.s
    triangle.spreads.t triangle.spreads.r triangle.spreads.s
    triangle.firstQuadranceNonzero triangle.secondQuadranceNonzero
    triangle.thirdQuadranceNonzero areaNonzero products.1 products.2.1
    products.2.2

/-- Exercise 10.10: any two triangles over `F₃` have the same unordered spread triple `{2,2,1}`. -/
theorem exercise_10_10_similar
    (left right : NonNull.Basic.NonNullTriangle Three.Element) : left.Similar right :=
  Permutation.sameEntries_of_repeatedEntryPattern (spread_pattern
    left)
    (spread_pattern right)

/-- Exercise 10.10: every triangle over `F₃` has one displayed vertex which is simultaneously right and isosceles. -/
theorem exercise_10_10_right_isosceles
    (triangle : NonNull.Basic.NonNullTriangle Three.Element) : (NonNullTriangle.IsRightIsosceles triangle) := by
  have areaNonzero :
      Quadrea.Basic.quadrea triangle.first triangle.second triangle.third ≠ 0 :=
    (Quadrea.Basic.quadrea_ne_zero_iff_not_collinear triangle.first triangle.second
      triangle.third (by decide : (2 : Three.Element) ≠ 0)).2
      triangle.notCollinear
  have pattern := quadrance_pattern triangle.quadrances.t
    triangle.quadrances.r triangle.quadrances.s
    triangle.firstQuadranceNonzero triangle.secondQuadranceNonzero
    triangle.thirdQuadranceNonzero areaNonzero
  rcases pattern with atFirst | atSecond | atThird
  · apply Or.inl
    refine ⟨atFirst.1, ?_⟩
    apply (Quadrance.pythagoras_iff_perpendicular triangle.second triangle.third
      triangle.first triangle.firstSecondDistinct.symm
      triangle.firstThirdDistinct.symm
      (by decide : (2 : Three.Element) ≠ 0)).1
    calc
      Quadrance.quadrance triangle.third triangle.first +
          Quadrance.quadrance triangle.second triangle.first =
        Quadrance.quadrance triangle.first triangle.third +
          Quadrance.quadrance triangle.first triangle.second := by
            rw [Quadrance.quadrance_symm triangle.third triangle.first,
              Quadrance.quadrance_symm triangle.second triangle.first]
      _ = triangle.quadrances.r + triangle.quadrances.s := rfl
      _ = triangle.quadrances.t := atFirst.2
  · apply Or.inr
    apply Or.inl
    refine ⟨atSecond.1, ?_⟩
    apply (Quadrance.pythagoras_iff_perpendicular triangle.first triangle.third
      triangle.second triangle.firstSecondDistinct
      triangle.secondThirdDistinct.symm
      (by decide : (2 : Three.Element) ≠ 0)).1
    calc
      Quadrance.quadrance triangle.third triangle.second +
          Quadrance.quadrance triangle.first triangle.second =
        Quadrance.quadrance triangle.second triangle.third +
          Quadrance.quadrance triangle.first triangle.second := by
            rw [Quadrance.quadrance_symm triangle.third triangle.second]
      _ = triangle.quadrances.t + triangle.quadrances.s := rfl
      _ = triangle.quadrances.r := atSecond.2
  · apply Or.inr
    apply Or.inr
    refine ⟨atThird.1, ?_⟩
    exact (Quadrance.pythagoras_iff_perpendicular triangle.first triangle.second
      triangle.third triangle.firstThirdDistinct
      triangle.secondThirdDistinct (by decide : (2 : Three.Element) ≠ 0)).1
      atThird.2
end

end Purelib.Geometry.Triangles.FiniteField.Three.Classification

end
