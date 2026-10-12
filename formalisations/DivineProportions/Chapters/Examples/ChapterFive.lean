module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Algebra.Field.Finite.Five
import Purelib.Geometry.Plane.Line.Basic
public import Purelib.Geometry.Plane.Line.Incidence
import Purelib.Geometry.Plane.Point.Basic
public import Purelib.Geometry.Plane.Point.Quadrance
import Purelib.Geometry.Trigonometry.QuadTriple.Basic
public import Purelib.Geometry.Trigonometry.QuadTriple.SquaredSum
import Purelib.NumberTheory.SquareClass.Rational.Nonsquare

public import Purelib.Algebra.Field.Finite.Eleven

open Purelib.Geometry

section
@[expose] public section

/-!
# Divine Proportions, Exercise 5.9

The braces in the source are treated as an unordered triple: any one entry
may be `(a+b)²`, with the other two equal to `a²` and `b²`.  The explicit
quad triple `{3,3,12}` is not of that form over the constructive rationals,
because its two repeated entries would require a rational square root of
three.  The nonsquare certificate comes from the computable reduced fraction,
not from real-number completeness or an infinite descent object.
-/

namespace formalisations.DivineProportions.Chapters.Examples.ChapterFive

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]
namespace ExerciseFiveNine

open Purelib.Data.Rat in
open Purelib.Geometry.Trigonometry.QuadTriple in
open Purelib.NumberTheory in
/-- The rational quad triple `(3,3,12)` is not a squared-sum triple.

This explicit example separates the quad-triple relation from a squared-sum representation, using that three has no
rational square root (Exercise 5.9). -/
theorem exercise_5_9 :
    Trigonometry.QuadTriple (3 : Fraction.Rational) 3 12 ∧
      ¬ SquaredSum.IsSquaredSumTriple (3 : Fraction.Rational) 3 12 := by
  apply SquaredSum.exercise_5_9_of_three_not_square
  exact SquareClass.Rational.Nonsquare.square_ne_three

end ExerciseFiveNine

end formalisations.DivineProportions.Chapters.Examples.ChapterFive

end

section
/-!
# Divine Proportions, Chapter 5 quad-triple exercises

The exercises below are direct finite polynomial consequences of
Archimedes' function.  Exercise 5.11 exposes the same distinct-centre premise
missing from the source's earlier quadratic-compatibility claim; no root is
selected in the degenerate case.
-/

@[expose] public section

namespace formalisations.DivineProportions.Chapters.Examples.ChapterFive

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]
namespace ExerciseFiveTwelveExample

section
open Purelib.Algebra.Field.Finite
open Purelib.Geometry.Plane.Point
/-- The point (1, 0) over the field of five elements. -/
def first : Plane.Point
  Five.Element := ⟨1, 0⟩
/-- The point (0, 2) over the field of five elements. -/
def second : Plane.Point
  Five.Element := ⟨0, 2⟩
/-- The origin over the field of five elements. -/
def third : Plane.Point
  Five.Element := ⟨0, 0⟩

end

open Purelib.Geometry.Plane.Line in
open Purelib.Geometry.Plane.Line.Basic in
open Purelib.Geometry.Plane.Point in
open formalisations.DivineProportions.Chapters.Examples.ChapterFive in
/-- Exercise 5.12's requested example: this noncollinear `F₅` triangle is
right at `third`, while the opposite side has quadrance zero. -/
theorem
  opposite_quadrance_can_vanish
  :
    Quadrance.quadrance first second = 0 ∧
      (Incidence.lineThrough first third (by decide)).Perpendicular
        (Incidence.lineThrough second third (by decide)) ∧
      ¬ Incidence.Collinear first second
        third := by
  constructor
  · decide
  constructor
  · unfold Plane.Line.Perpendicular Incidence.lineThrough first
      second
      third
    decide
  · intro collinear
    have determinantZero :=
      (Incidence.collinear_iff_pointDeterminant_eq_zero first second
        third).1
        collinear
    have determinantNonzero :
        Incidence.pointDeterminant first second
          third ≠ 0 := by
      unfold Incidence.pointDeterminant first second
        third
      decide
    exact determinantNonzero determinantZero

end ExerciseFiveTwelveExample
end formalisations.DivineProportions.Chapters.Examples.ChapterFive

end

end

section
@[expose] public section

/-!
# Divine Proportions, Chapter 5: quadrance

Quadrance is a polynomial, so its basic geometry works uniformly over the
constructive rationals and finite fields.  The few exclusions below are
stated explicitly: midpoint and Triple-quad arguments require `2 ≠ 0`.
-/

namespace formalisations.DivineProportions.Chapters.Examples.ChapterFive

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

open Purelib.Algebra.Field.Finite
open Purelib.Geometry.Plane.Point
/-- Example 5.1 in a finite field: `[0,0]` and `[1,2]` are distinct in `F₅`
but have zero quadrance because `2² = -1`. -/
theorem example_5_1_fieldFive :
    Quadrance.quadrance
      (⟨0, 0⟩ : Plane.Point Five.Element)
      (⟨1, 2⟩ : Plane.Point Five.Element) = 0 := by
  decide

/-- The origin and (1, 2) are distinct over the field of five elements. -/
theorem example_5_1_fieldFive_distinct :
    (⟨0, 0⟩ : Plane.Point Five.Element) ≠ ⟨1, 2⟩ := by
  decide
end formalisations.DivineProportions.Chapters.Examples.ChapterFive

end

end

section
/-!
# Divine Proportions, Example 5.2

Every point, line, incidence, perpendicularity, and quadrance printed in the
source is checked by kernel computation in the project's executable
eleven-element field.
-/

@[expose] public section

namespace formalisations.DivineProportions.Chapters.Examples.ChapterFive

namespace ChapterFiveExamples

open Purelib.Algebra.Field.Finite in
/-- The executable carrier of the field of eleven elements. -/
abbrev Element := Eleven.Element

section
open Purelib.Geometry.Plane.Point
/-- The first displayed vertex (3, 7) modulo eleven. -/
def firstPoint : Purelib.Geometry.Plane.Point Element := ⟨3, 7⟩
/-- The second displayed vertex (10, 3) modulo eleven. -/
def secondPoint : Purelib.Geometry.Plane.Point Element := ⟨10, 3⟩
/-- The third displayed vertex (6, 1) modulo eleven. -/
def thirdPoint : Purelib.Geometry.Plane.Point Element := ⟨6, 1⟩

end

section
open Purelib.Geometry.Plane.Line
/-- The printed side `A₁A₂=⟨3:8:1⟩`. -/
def firstSecondLine : Purelib.Geometry.Plane.Line Element where
  a := 3
  b := 8
  c := 1
  direction_nonzero := by decide

/-- The printed side `A₂A₃=⟨8:6:1⟩`. -/
def secondThirdLine : Purelib.Geometry.Plane.Line Element where
  a := 8
  b := 6
  c := 1
  direction_nonzero := by decide

/-- The printed side `A₁A₃=⟨10:5:1⟩`. -/
def firstThirdLine : Purelib.Geometry.Plane.Line Element where
  a := 10
  b := 5
  c := 1
  direction_nonzero := by decide

end

open Purelib.Geometry.Plane.Line.Basic in
open Purelib.Geometry.Plane.Point in
/-- Example 5.2: the complete closed certificate for Figure 5.3 and its
following quadrance calculation. -/
theorem example_5_2 :
    firstSecondLine.Contains firstPoint ∧
      firstSecondLine.Contains secondPoint ∧
      secondThirdLine.Contains secondPoint ∧
      secondThirdLine.Contains thirdPoint ∧
      firstThirdLine.Contains firstPoint ∧
      firstThirdLine.Contains thirdPoint ∧
      firstThirdLine.Perpendicular secondThirdLine ∧
      Quadrance.quadrance secondPoint thirdPoint = 9 ∧
      Quadrance.quadrance firstPoint thirdPoint = 1 ∧
      Quadrance.quadrance firstPoint secondPoint = 10 ∧
      Quadrance.quadrance secondPoint thirdPoint +
          Quadrance.quadrance firstPoint thirdPoint =
        Quadrance.quadrance firstPoint secondPoint := by
  unfold Purelib.Geometry.Plane.Line.Contains Purelib.Geometry.Plane.Line.Perpendicular Quadrance.quadrance
      firstSecondLine
    secondThirdLine firstThirdLine firstPoint secondPoint thirdPoint
  decide

end ChapterFiveExamples

end formalisations.DivineProportions.Chapters.Examples.ChapterFive

end

end
