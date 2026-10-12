module
import Purelib.Algebra.Field.ExplicitField
import Purelib.Geometry.Plane.Line.Incidence
import Purelib.Geometry.Plane.Point.Basic
import Purelib.Geometry.Plane.Point.Quadrance
import Purelib.Geometry.Triangles.FiniteField.Five.Classification
public import Purelib.Geometry.Triangles.FiniteField.Five.Null.Singly.Basic
import Purelib.Geometry.Triangles.Quadrea.Basic
import Purelib.Geometry.Triangles.Trigonometry.Spread
import Purelib.Geometry.Trigonometry.QuadTriple.Basic
import Purelib.Algebra.Field.Finite.Five
import Purelib.Tactic.Ring

open Purelib.Geometry.Triangles.FiniteField.Five.Null.Singly.Basic (SinglyNullAtFirst)

open Purelib

open Purelib.Algebra.Field.Finite

open Purelib.Geometry

open Purelib.Geometry.Plane.Line

open Purelib.Geometry.Plane.Point

open Purelib.Geometry.Triangles

open Purelib.Geometry.Triangles.FiniteField.Five

open Purelib.Geometry.Triangles.FiniteField.Five.Null

open Purelib.Geometry.Trigonometry

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

namespace Purelib.Geometry.Triangles.FiniteField.Five.Null.Singly

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

section

namespace Basic.SinglyNullAtFirst

/-- The opposite spread of a singly null scalar triangle over the field with five elements is one or three.

The other two quadrances are nonzero, their Archimedes expression is one or four and the cleared spread law holds. -/
private theorem
  scalar_opposite_spread
    (q₂ q₃ s : Five.Element)
    (secondNonzero : q₂ ≠ 0) (thirdNonzero : q₃ ≠ 0)
    (areaValue : QuadTriple.Basic.archimedesFunction 0 q₂ q₃ = 1 ∨
      QuadTriple.Basic.archimedesFunction 0 q₂ q₃ = 4)
    (areaProduct : QuadTriple.Basic.archimedesFunction 0 q₂ q₃ = 4 * q₂ * q₃ * s) :
    s = 1 ∨ s = 3 := by
  decide +revert

/-- Corrected null part of Exercise 10.11: for a triangle with exactly one null side, the sole defined vertex spread
gives exactly the two possible types `1` and `3`. -/
theorem
  oppositeSpread_eq_one_or_three
  (triangle : SinglyNullAtFirst) :
    triangle.oppositeSpread = 1 ∨ triangle.oppositeSpread = 3 := by
  have geometricAreaValues := Classification.quadrea_values triangle.first triangle.second
    triangle.third triangle.notCollinear
  have scalarAreaEqualsGeometric :
      QuadTriple.Basic.archimedesFunction 0
          (Quadrance.quadrance triangle.third triangle.first)
          (Quadrance.quadrance triangle.second triangle.first) =
        Quadrea.Basic.quadrea triangle.first triangle.second triangle.third := by
    unfold Quadrea.Basic.quadrea
    rw [triangle.firstQuadranceZero,
      Quadrance.quadrance_symm triangle.third triangle.first,
      Quadrance.quadrance_symm triangle.second triangle.first]
  have areaValues :
      QuadTriple.Basic.archimedesFunction 0
          (Quadrance.quadrance triangle.third triangle.first)
          (Quadrance.quadrance triangle.second triangle.first) = 1 ∨
        QuadTriple.Basic.archimedesFunction 0
          (Quadrance.quadrance triangle.third triangle.first)
          (Quadrance.quadrance triangle.second triangle.first) = 4 := by
    rcases geometricAreaValues with areaOne | areaFour
    · exact Or.inl (scalarAreaEqualsGeometric.trans areaOne)
    · exact Or.inr (scalarAreaEqualsGeometric.trans areaFour)
  have reversedProduct := Trigonometry.Spread.quadrea_spread triangle.second triangle.third
    triangle.first triangle.firstSecondDistinct.symm
    triangle.firstThirdDistinct.symm
    triangle.secondFirstNonNull triangle.thirdFirstNonNull
  have areaProduct :
      QuadTriple.Basic.archimedesFunction 0
          (Quadrance.quadrance triangle.third triangle.first)
          (Quadrance.quadrance triangle.second triangle.first) =
        4 * Quadrance.quadrance triangle.third triangle.first *
          Quadrance.quadrance triangle.second triangle.first *
            triangle.oppositeSpread := by
    calc
      QuadTriple.Basic.archimedesFunction 0
          (Quadrance.quadrance triangle.third triangle.first)
          (Quadrance.quadrance triangle.second triangle.first) =
        Quadrea.Basic.quadrea triangle.first triangle.second triangle.third :=
          scalarAreaEqualsGeometric
      _ = Quadrea.Basic.quadrea triangle.second triangle.third triangle.first :=
        (Quadrea.Basic.quadrea_cyclic triangle.first triangle.second triangle.third).symm
      _ = 4 * Quadrance.quadrance triangle.third triangle.first *
          Quadrance.quadrance triangle.second triangle.first *
            triangle.oppositeSpread := reversedProduct
  have secondReversedNonzero :
      Quadrance.quadrance triangle.third triangle.first ≠ 0 := by
    rw [Quadrance.quadrance_symm triangle.third triangle.first]
    exact triangle.secondQuadranceNonzero
  have thirdReversedNonzero :
      Quadrance.quadrance triangle.second triangle.first ≠ 0 := by
    rw [Quadrance.quadrance_symm triangle.second triangle.first]
    exact triangle.thirdQuadranceNonzero
  exact scalar_opposite_spread
    (Quadrance.quadrance triangle.third triangle.first)
    (Quadrance.quadrance triangle.second triangle.first) triangle.oppositeSpread
    secondReversedNonzero thirdReversedNonzero areaValues areaProduct

end Basic.SinglyNullAtFirst

/-- Swapping the first two vertices preserves noncollinearity. -/
private theorem
  Classification.not_collinear_swap_first_second
    {first second third : Geometry.Plane.Point Five.Element}
    (notCollinear : ¬ Incidence.Collinear first second third) :
    ¬ Incidence.Collinear second first third := by
  intro swappedCollinear
  apply notCollinear
  apply (Incidence.collinear_iff_pointDeterminant_eq_zero first second third).2
  have swappedZero :=
    Incidence.pointDeterminant_eq_zero_of_collinear swappedCollinear
  calc
    Incidence.pointDeterminant first second third =
        -Incidence.pointDeterminant second first third := by
      unfold Incidence.pointDeterminant
      ring1
    _ = 0 := by rw [swappedZero]; exact neg_zero

/-- Cyclically moving the third vertex to the first position preserves noncollinearity. -/
private theorem Classification.not_collinear_cyclic_right
    {first second third : Geometry.Plane.Point Five.Element}
    (notCollinear : ¬ Incidence.Collinear first second third) :
    ¬ Incidence.Collinear third first second := by
  intro cyclicCollinear
  apply notCollinear
  apply (Incidence.collinear_iff_pointDeterminant_eq_zero first second third).2
  have cyclicZero :=
    Incidence.pointDeterminant_eq_zero_of_collinear cyclicCollinear
  calc
    Incidence.pointDeterminant first second third =
        Incidence.pointDeterminant third first second := by
      unfold Incidence.pointDeterminant
      ring1
    _ = 0 := cyclicZero

/-- Every `F₅` triangle with exactly one null side can be relabelled by one of three displayed permutations so that the
null side is first. Its sole defined vertex spread is then one of the two values `1` and `3`. -/
theorem Classification.exercise_10_11_singlyNull
    (first second third : Geometry.Plane.Point Five.Element)
    (notCollinear : ¬ Incidence.Collinear first second third)
    (exactlyOneNull :
      (Quadrance.quadrance second third = 0 ∧
        Quadrance.quadrance first third ≠ 0 ∧ Quadrance.quadrance first second ≠ 0) ∨
      (Quadrance.quadrance first third = 0 ∧
        Quadrance.quadrance second third ≠ 0 ∧ Quadrance.quadrance first second ≠ 0) ∨
      (Quadrance.quadrance first second = 0 ∧
        Quadrance.quadrance second third ≠ 0 ∧ Quadrance.quadrance first third ≠ 0)) :
    ∃ normalized : SinglyNullAtFirst,
      ((normalized.first = first ∧ normalized.second = second ∧
          normalized.third = third) ∨
        (normalized.first = second ∧ normalized.second = first ∧
          normalized.third = third) ∨
        (normalized.first = third ∧ normalized.second = first ∧
          normalized.third = second)) ∧
      (normalized.oppositeSpread = 1 ∨ normalized.oppositeSpread = 3) := by
  rcases exactlyOneNull with firstNull | secondOrThirdNull
  · let normalized : SinglyNullAtFirst :=
      { first := first
        second := second
        third := third
        notCollinear := notCollinear
        firstQuadranceZero := firstNull.1
        secondQuadranceNonzero := firstNull.2.1
        thirdQuadranceNonzero := firstNull.2.2 }
    exact ⟨normalized, Or.inl ⟨rfl, rfl, rfl⟩,
      normalized.oppositeSpread_eq_one_or_three⟩
  · rcases secondOrThirdNull with secondNull | thirdNull
    · have thirdReversedNonzero : Quadrance.quadrance second first ≠ 0 := by
        rw [Quadrance.quadrance_symm second first]
        exact secondNull.2.2
      let normalized : SinglyNullAtFirst :=
        { first := second
          second := first
          third := third
          notCollinear := Geometry.Triangles.FiniteField.Five.Null.Singly.Classification.not_collinear_swap_first_second
            notCollinear
          firstQuadranceZero := secondNull.1
          secondQuadranceNonzero := secondNull.2.1
          thirdQuadranceNonzero := thirdReversedNonzero }
      exact ⟨normalized, Or.inr (Or.inl ⟨rfl, rfl, rfl⟩),
        normalized.oppositeSpread_eq_one_or_three⟩
    · have secondReversedNonzero : Quadrance.quadrance third second ≠ 0 := by
        rw [Quadrance.quadrance_symm third second]
        exact thirdNull.2.1
      have thirdReversedNonzero : Quadrance.quadrance third first ≠ 0 := by
        rw [Quadrance.quadrance_symm third first]
        exact thirdNull.2.2
      let normalized : SinglyNullAtFirst :=
        { first := third
          second := first
          third := second
          notCollinear := Geometry.Triangles.FiniteField.Five.Null.Singly.Classification.not_collinear_cyclic_right
            notCollinear
          firstQuadranceZero := thirdNull.1
          secondQuadranceNonzero := secondReversedNonzero
          thirdQuadranceNonzero := thirdReversedNonzero }
      exact ⟨normalized, Or.inr (Or.inr ⟨rfl, rfl, rfl⟩),
        normalized.oppositeSpread_eq_one_or_three⟩

end

end Purelib.Geometry.Triangles.FiniteField.Five.Null.Singly

end
