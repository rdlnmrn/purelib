module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.Proportions.TwoStruts.Exercises
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Geometry.Plane.Line.Basic
public import Purelib.Geometry.Plane.Line.Incidence
import Purelib.Geometry.Plane.Point.Basic
public import Purelib.Geometry.Plane.Point.Quadrance
public import Purelib.Geometry.Trigonometry.QuadTriple.Basic
import Purelib.Data.Rat.Fraction.Compatibility

import formalisations.DivineProportions.Chapters.Proportions.ChapterElevenExercises
import Purelib.Tactic.Ring

section
@[expose] public section

/-!
# Divine Proportions, Chapter 11 examples

The source's factored Two-struts example and its two failed converses are
recorded over constructive rational coordinates.  The counterexamples use
integer points, so every incidence, quadrance, and determinant is a finite
kernel computation.
-/

namespace formalisations.DivineProportions.Chapters.Examples.ChapterEleven

namespace ChapterElevenExamples
namespace ExampleElevenOne

section
open Purelib.Data.Rat
/-- The rational strut parameter one quarter. -/
def p : Fraction.Rational := 1 / 4
/-- The rational strut parameter nine sixty-fourths. -/
def r : Fraction.Rational := 9 / 64

end

open Purelib.Algebra.Field in
open Purelib.Data.Rat in
open Purelib.Data.Rat.Fraction.Cast in
open Purelib.Geometry.Trigonometry.QuadTriple in
open formalisations.DivineProportions.Chapters.Proportions in
/-- Example 11.1 at the source's literal rational parameters. -/
theorem example_11_1 (m n : Fraction.Rational)
    (strutTriples :
      Purelib.Geometry.Trigonometry.QuadTriple r (r * p) (m * p) ∧
        Purelib.Geometry.Trigonometry.QuadTriple p (r * p) (n * r)) :
    (64 * m - 9) * (64 * m - 81) = 0 ∧
      (36 * n - 25) * (36 * n - 121) = 0 := by
  apply ChapterElevenExercises.example_11_1 p r m n
  · calc
      4 * p = p * 4 := by ring1
      _ = 1 := ExplicitField.div_mul_cancel 1
        (Order.rationalNatCastNonzero (by decide))
  · calc
      64 * r = r * 64 := by ring1
      _ = 9 := ExplicitField.div_mul_cancel 9
        (Order.rationalNatCastNonzero (by decide))
  · exact strutTriples

end ExampleElevenOne

namespace ExerciseElevenFour

section
open Purelib.Data.Rat
/-- The exact rational parameter p, equal to one. -/
def p : Fraction.Rational := 1
/-- The exact rational parameter r, equal to one. -/
def r : Fraction.Rational := 1
/-- The exact rational parameter m, equal to four. -/
def m : Fraction.Rational := 4
/-- The exact rational parameter n, equal to four. -/
def n : Fraction.Rational := 4
/-- The exact rational parameter s₁, equal to three quarters. -/
def s₁ : Fraction.Rational := 3 / 4
/-- The exact rational parameter s₂, equal to three quarters. -/
def s₂ : Fraction.Rational := 3 / 4
/-- The exact rational parameter s₃, equal to three quarters. -/
def s₃ : Fraction.Rational := 3 / 4

end

/-- The third equilateral spread, three quarters, is nonzero. -/
private theorem thirdSpreadNonzero : s₃ ≠ 0 := by decide

open Purelib.Geometry.Trigonometry.QuadTriple in
/-- Both displayed quadrance triples obey the quad-triple equation. -/
private theorem strutTriples :
    Purelib.Geometry.Trigonometry.QuadTriple r (r * p) (m * p) ∧
      Purelib.Geometry.Trigonometry.QuadTriple p (r * p) (n * r) := by
  constructor <;> unfold Purelib.Geometry.Trigonometry.QuadTriple Basic.archimedesFunction <;> decide

open Purelib.Algebra in
/-- The corrected equations hold for the equilateral-spread specialization
`p=r=1`, `m=n=4`. -/
theorem corrected_equations :
    (m * s₂ + s₁ + s₃) ^ 2 =
        2 * ((m * s₂) ^ 2 + s₁ ^ 2 + s₃ ^ 2) ∧
      (n * s₁ + s₂ + s₃) ^ 2 =
        2 * ((n * s₁) ^ 2 + s₂ ^ 2 + s₃ ^ 2) := by
  apply Proportions.TwoStruts.Exercises.exercise_11_4_corrected p r m n s₁ s₂ s₃ thirdSpreadNonzero
  · decide
  · decide
  · exact strutTriples

/-- The two equations printed in Exercise 11.4 omit the `m²` and `n²`
terms.  This exact specialization refutes both omissions. -/
theorem printed_equations_counterexample :
    ¬ ((m * s₂ + s₁ + s₃) ^ 2 = 2 * (s₁ ^ 2 + s₃ ^ 2) ∧
      (n * s₁ + s₂ + s₃) ^ 2 = 2 * (s₂ ^ 2 + s₃ ^ 2)) := by
  decide

end ExerciseElevenFour

namespace ExerciseElevenEight

section
open Purelib.Data.Rat
open Purelib.Geometry.Plane.Point
/-- The first rational triangle vertex, with coordinates (0, 0). -/
def first : Purelib.Geometry.Plane.Point Fraction.Rational := ⟨0, 0⟩
/-- The second rational triangle vertex, with coordinates (2, 0). -/
def second : Purelib.Geometry.Plane.Point Fraction.Rational := ⟨2, 0⟩
/-- The third rational triangle vertex, with coordinates (0, 2). -/
def third : Purelib.Geometry.Plane.Point Fraction.Rational := ⟨0, 2⟩

/-- The midpoint of `A₂A₃`. -/
def B₁ : Purelib.Geometry.Plane.Point Fraction.Rational := ⟨1, 1⟩
/-- The midpoint of `A₃A₁`. -/
def B₂ : Purelib.Geometry.Plane.Point Fraction.Rational := ⟨0, 1⟩
/-- The midpoint of `A₁A₂`. -/
def B₃ : Purelib.Geometry.Plane.Point Fraction.Rational := ⟨1, 0⟩

end

section
open Purelib.Geometry.Plane.Line
open Purelib.Geometry.Plane.Line.Basic
/-- The point B₁ is collinear with the second and third vertices. -/
private theorem firstSide : Incidence.Collinear second third B₁ := by
  let distinct : second ≠ third := by decide
  exact ⟨Incidence.lineThrough second third distinct,
    Incidence.lineThrough_contains_first second third distinct,
    Incidence.lineThrough_contains_second second third distinct, by
      unfold Purelib.Geometry.Plane.Line.Contains Incidence.lineThrough second third B₁
      ring1⟩

/-- The point B₂ is collinear with the third and first vertices. -/
private theorem secondSide : Incidence.Collinear third first B₂ := by
  let distinct : third ≠ first := by decide
  exact ⟨Incidence.lineThrough third first distinct,
    Incidence.lineThrough_contains_first third first distinct,
    Incidence.lineThrough_contains_second third first distinct, by
      unfold Purelib.Geometry.Plane.Line.Contains Incidence.lineThrough third first B₂
      ring1⟩

/-- The point B₃ is collinear with the first and second vertices. -/
private theorem thirdSide : Incidence.Collinear first second B₃ := by
  let distinct : first ≠ second := by decide
  exact ⟨Incidence.lineThrough first second distinct,
    Incidence.lineThrough_contains_first first second distinct,
    Incidence.lineThrough_contains_second first second distinct, by
      unfold Purelib.Geometry.Plane.Line.Contains Incidence.lineThrough first second B₃
      ring1⟩

end

open Purelib.Geometry.Plane.Point in
/-- The six quadrances are `(2,2)`, `(1,1)`, and `(1,1)`. -/
theorem quadrance_values :
    Quadrance.quadrance second B₁ = 2 ∧ Quadrance.quadrance B₁ third = 2 ∧
      Quadrance.quadrance third B₂ = 1 ∧ Quadrance.quadrance B₂ first = 1 ∧
      Quadrance.quadrance first B₃ = 1 ∧ Quadrance.quadrance B₃ second = 1 := by
  decide

open Purelib.Geometry.Plane.Line in
open Purelib.Geometry.Plane.Point in
/-- Exercise 11.8.  The three side midpoints satisfy the Menelaus product
but form a nondegenerate medial triangle rather than a line. -/
theorem exercise_11_8 :
    Incidence.Collinear second third B₁ ∧
      Incidence.Collinear third first B₂ ∧
      Incidence.Collinear first second B₃ ∧
      Quadrance.quadrance second B₁ * Quadrance.quadrance third B₂ * Quadrance.quadrance first B₃ =
        Quadrance.quadrance B₁ third * Quadrance.quadrance B₂ first * Quadrance.quadrance B₃ second ∧
      ¬ Incidence.Collinear B₁ B₂ B₃ := by
  refine ⟨firstSide, secondSide, thirdSide, by decide, ?_⟩
  intro collinear
  have determinantZero := Incidence.pointDeterminant_eq_zero_of_collinear collinear
  exact (by decide : Incidence.pointDeterminant B₁ B₂ B₃ ≠ 0) determinantZero

end ExerciseElevenEight

namespace ExerciseElevenTen

section
open Purelib.Data.Rat
open Purelib.Geometry.Plane.Point
/-- The first rational triangle vertex, with coordinates (0, 0). -/
def first : Purelib.Geometry.Plane.Point Fraction.Rational := ⟨0, 0⟩
/-- The second rational triangle vertex, with coordinates (6, 0). -/
def second : Purelib.Geometry.Plane.Point Fraction.Rational := ⟨6, 0⟩
/-- The third rational triangle vertex, with coordinates (0, 6). -/
def third : Purelib.Geometry.Plane.Point Fraction.Rational := ⟨0, 6⟩

/-- The one-third point of `A₂A₃`. -/
def B₁ : Purelib.Geometry.Plane.Point Fraction.Rational := ⟨4, 2⟩
/-- The midpoint of `A₃A₁`. -/
def B₂ : Purelib.Geometry.Plane.Point Fraction.Rational := ⟨0, 3⟩
/-- An external point of `A₁A₂`, beyond `A₂`. -/
def B₃ : Purelib.Geometry.Plane.Point Fraction.Rational := ⟨12, 0⟩

end

section
open Purelib.Geometry.Plane.Line
open Purelib.Geometry.Plane.Line.Basic
/-- The point B₁ is collinear with the second and third vertices. -/
private theorem firstSide : Incidence.Collinear second third B₁ := by
  let distinct : second ≠ third := by decide
  exact ⟨Incidence.lineThrough second third distinct,
    Incidence.lineThrough_contains_first second third distinct,
    Incidence.lineThrough_contains_second second third distinct, by
      unfold Purelib.Geometry.Plane.Line.Contains Incidence.lineThrough second third B₁
      ring1⟩

/-- The point B₂ is collinear with the third and first vertices. -/
private theorem secondSide : Incidence.Collinear third first B₂ := by
  let distinct : third ≠ first := by decide
  exact ⟨Incidence.lineThrough third first distinct,
    Incidence.lineThrough_contains_first third first distinct,
    Incidence.lineThrough_contains_second third first distinct, by
      unfold Purelib.Geometry.Plane.Line.Contains Incidence.lineThrough third first B₂
      ring1⟩

/-- The point B₃ is collinear with the first and second vertices. -/
private theorem thirdSide : Incidence.Collinear first second B₃ := by
  let distinct : first ≠ second := by decide
  exact ⟨Incidence.lineThrough first second distinct,
    Incidence.lineThrough_contains_first first second distinct,
    Incidence.lineThrough_contains_second first second distinct, by
      unfold Purelib.Geometry.Plane.Line.Contains Incidence.lineThrough first second B₃
      ring1⟩

end

/-- The first vertex is distinct from the side point B₁. -/
private theorem firstB₁Distinct : first ≠ B₁ := by decide
/-- The second vertex is distinct from the side point B₂. -/
private theorem secondB₂Distinct : second ≠ B₂ := by decide
/-- The third vertex is distinct from the side point B₃. -/
private theorem thirdB₃Distinct : third ≠ B₃ := by decide

section
open Purelib.Data.Rat
open Purelib.Geometry.Plane.Line
/-- The line through the first vertex and side point B₁, using their exact distinctness witness. -/
def firstCevian : Purelib.Geometry.Plane.Line Fraction.Rational :=
  let distinct : first ≠ B₁ := by decide
  Incidence.lineThrough first B₁ distinct
/-- The line through the second vertex and side point B₂, using their exact distinctness witness. -/
def secondCevian : Purelib.Geometry.Plane.Line Fraction.Rational :=
  let distinct : second ≠ B₂ := by decide
  Incidence.lineThrough second B₂ distinct
/-- The line through the third vertex and side point B₃, using their exact distinctness witness. -/
def thirdCevian : Purelib.Geometry.Plane.Line Fraction.Rational :=
  let distinct : third ≠ B₃ := by decide
  Incidence.lineThrough third B₃ distinct

end

open Purelib.Geometry.Plane.Point in
/-- The six quadrances are `(8,32)`, `(9,9)`, and `(144,36)`. -/
theorem quadrance_values :
    Quadrance.quadrance second B₁ = 8 ∧ Quadrance.quadrance B₁ third = 32 ∧
      Quadrance.quadrance third B₂ = 9 ∧ Quadrance.quadrance B₂ first = 9 ∧
      Quadrance.quadrance first B₃ = 144 ∧ Quadrance.quadrance B₃ second = 36 := by
  constructor
  · unfold Quadrance.quadrance second B₁
    ring1
  constructor
  · unfold Quadrance.quadrance B₁ third
    ring1
  constructor
  · unfold Quadrance.quadrance third B₂
    ring1
  constructor
  · unfold Quadrance.quadrance B₂ first
    ring1
  constructor
  · unfold Quadrance.quadrance first B₃
    ring1
  · unfold Quadrance.quadrance B₃ second
    ring1

open Purelib.Data.Rat
open Purelib.Geometry.Plane.Line
open Purelib.Geometry.Plane.Point
/-- The three displayed cevians have no common point. -/
theorem cevians_not_concurrent :
    ¬ ∃ point : Purelib.Geometry.Plane.Point Fraction.Rational,
      firstCevian.Contains point ∧ secondCevian.Contains point ∧
        thirdCevian.Contains point := by
  rintro ⟨point, firstContains, secondContains, thirdContains⟩
  have determinantZero := Incidence.lineDeterminant_eq_zero_of_concurrent
    firstCevian secondCevian thirdCevian point firstContains secondContains
      thirdContains
  exact (by
      decide : Incidence.lineDeterminant firstCevian secondCevian thirdCevian ≠ 0)
      determinantZero

/-- Exercise 11.10.  Squared side ratios lose the sign detected by affine
Ceva: the quadrance products agree, but the three cevians are not
concurrent. -/
theorem exercise_11_10 :
    Incidence.Collinear second third B₁ ∧
      Incidence.Collinear third first B₂ ∧
      Incidence.Collinear first second B₃ ∧
      Quadrance.quadrance second B₁ * Quadrance.quadrance third B₂ * Quadrance.quadrance first B₃ =
        Quadrance.quadrance B₁ third * Quadrance.quadrance B₂ first * Quadrance.quadrance B₃ second ∧
      ¬ ∃ point : Purelib.Geometry.Plane.Point Fraction.Rational,
        firstCevian.Contains point ∧ secondCevian.Contains point ∧
          thirdCevian.Contains point := by
  refine ⟨firstSide, secondSide, thirdSide, ?_, cevians_not_concurrent⟩
  rw [quadrance_values.1, quadrance_values.2.1,
    quadrance_values.2.2.1, quadrance_values.2.2.2.1,
    quadrance_values.2.2.2.2.1, quadrance_values.2.2.2.2.2]
  ring1

end ExerciseElevenTen

namespace ExerciseElevenEleven

open Purelib.Data.Rat in
/-- When the common spread product is null, all three cleared Menelaus
relations may hold while the quadrance products differ.  This is the precise
cancellation failure described by Exercise 11.11. -/
theorem null_factor_counterexample :
    ∃ r₁ r₂ r₃ R₁ R₂ R₃ P₁ P₂ P₃ : Fraction.Rational,
      r₁ * P₁ = R₂ * r₂ ∧
      r₂ * P₂ = R₃ * r₃ ∧
      r₃ * P₃ = R₁ * r₁ ∧
      (R₁ * R₂ * R₃ - P₁ * P₂ * P₃) * (r₁ * r₂ * r₃) = 0 ∧
      R₁ * R₂ * R₃ ≠ P₁ * P₂ * P₃ := by
  refine ⟨0, 0, 0, 1, 1, 1, 0, 1, 1, ?_⟩
  decide

end ExerciseElevenEleven

end ChapterElevenExamples

end formalisations.DivineProportions.Chapters.Examples.ChapterEleven

end
