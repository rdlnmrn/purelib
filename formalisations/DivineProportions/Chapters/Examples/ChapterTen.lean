module
import Purelib.Algebra.Group.Basic
import Purelib.Geometry.Triangles.Quadrance.Basic
import Purelib.LinearAlgebra.Coordinates3.Vector.Permutation
import Purelib.Geometry.Triangles.Congruence.Basic
import Purelib.Algebra.Field.Ratio
import Purelib.Geometry.Triangles.NonNull.Basic
import Purelib.Algebra.Field.Cancellation
import Purelib.Data.Rat.Fraction.Cast
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.Field.Finite.Five
import Purelib.Algebra.Field.Finite.Three
import Purelib.Data.Rat.Fraction.Field.Finite
import Purelib.Geometry.Plane.Line.Basic
import Purelib.Geometry.Plane.Line.Incidence
import Purelib.Geometry.Plane.Line.Spread
import Purelib.Geometry.Plane.Point.Basic
import Purelib.Geometry.Plane.Point.Quadrance
public import Purelib.Geometry.Triangles.Altitude.Foot
public import Purelib.Geometry.Triangles.FiniteField.Five.Null.Singly.Basic
public import Purelib.Geometry.Triangles.FiniteField.Three.Classification
import Purelib.Geometry.Triangles.Right.Altitude
import Purelib.Geometry.Triangles.Right.Isosceles.Basic
import Purelib.Data.Rat.Fraction.Compatibility
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Geometry.Triangles.NonNull.Spread
import Purelib.Geometry.Triangles.Similarity.Basic
import Purelib.LinearAlgebra.Coordinates3.Vector
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Fraction.Order.Cast

open Purelib.Algebra
open Purelib.Algebra.Field

open Purelib.Data.Rat

open Purelib.Geometry.Plane

open Purelib.Geometry.Triangles

open Purelib.LinearAlgebra.Coordinates3 renaming Vector -> Vector3

section
@[expose] public section

/-!
# Divine Proportions, Chapter 10 rational examples

The two examples below retain the source's literal rational coordinates.  All
side matches and spread matches are explicit finite permutation witnesses.
-/

namespace formalisations.DivineProportions.Chapters.Examples.ChapterTen

namespace ChapterTenExamples
namespace ExerciseTenSix

/-- The rational vertex (3, 0) of the displayed right triangle. -/
def first : Purelib.Geometry.Plane.Point Fraction.Rational := ⟨3, 0⟩
/-- The rational vertex (0, 4) of the displayed right triangle. -/
def second : Purelib.Geometry.Plane.Point Fraction.Rational := ⟨0, 4⟩
/-- The origin, at which the displayed rational triangle is right. -/
def third : Purelib.Geometry.Plane.Point Fraction.Rational := ⟨0, 0⟩

/-- The first two vertices of the displayed right triangle are distinct. -/
private theorem firstSecondDistinct : first ≠ second := by decide
/-- The first and third vertices of the displayed right triangle are distinct. -/
public theorem firstThirdDistinct : first ≠ third := by decide

/-- The second and third vertices of the displayed right triangle are distinct. -/
public theorem secondThirdDistinct : second ≠ third := by decide

/-- The displayed rational right triangle is noncollinear. -/
private theorem notCollinear : ¬ Line.Incidence.Collinear first second third := by
  intro collinear
  have determinantZero :=
    Line.Incidence.pointDeterminant_eq_zero_of_collinear collinear
  have determinantNonzero : Line.Incidence.pointDeterminant first second third ≠ 0 := by
    unfold Line.Incidence.pointDeterminant first second third
    decide
  exact determinantNonzero determinantZero

/-- The side joining the first two vertices has nonzero norm. -/
private theorem firstSecondNonNull :
    ¬ (Line.Incidence.lineThrough first second firstSecondDistinct).IsNull := by
  unfold Purelib.Geometry.Plane.Line.IsNull Line.Incidence.lineThrough first second
  decide

/-- The side joining the first and third vertices has nonzero norm. -/
private theorem firstThirdNonNull :
    ¬ (Line.Incidence.lineThrough first third ExerciseTenSix.firstThirdDistinct).IsNull := by
  unfold Purelib.Geometry.Plane.Line.IsNull Line.Incidence.lineThrough first third
  decide

/-- The side joining the second and third vertices has nonzero norm. -/
private theorem secondThirdNonNull :
    ¬ (Line.Incidence.lineThrough second third ExerciseTenSix.secondThirdDistinct).IsNull := by
  unfold Purelib.Geometry.Plane.Line.IsNull Line.Incidence.lineThrough second third
  decide

/-- The rational triangle with vertices (3, 0), (0, 4) and (0, 0).

Its retained certificates establish noncollinearity, distinct vertices and non-null sides. -/
def triangle : NonNull.Basic.NonNullTriangle Fraction.Rational :=
  let firstSecondDistinct : first ≠ second := by decide
  let
    firstThirdDistinct
    : first ≠ third := by decide
  let secondThirdDistinct : second ≠ third := by decide
  let notCollinear : ¬ Line.Incidence.Collinear first second third := by
    intro collinear
    have determinantZero :=
      Line.Incidence.pointDeterminant_eq_zero_of_collinear collinear
    have determinantNonzero : Line.Incidence.pointDeterminant first second third ≠ 0 := by
      unfold Line.Incidence.pointDeterminant first second third
      decide
    exact determinantNonzero determinantZero
  let firstSecondNonNull :
      ¬ (Line.Incidence.lineThrough first second firstSecondDistinct).IsNull := by
    unfold Purelib.Geometry.Plane.Line.IsNull Line.Incidence.lineThrough first second
    decide
  let firstThirdNonNull :
      ¬ (Line.Incidence.lineThrough first third
        firstThirdDistinct).IsNull
        := by
    unfold Purelib.Geometry.Plane.Line.IsNull Line.Incidence.lineThrough first third
    decide
  let secondThirdNonNull :
      ¬ (Line.Incidence.lineThrough second third secondThirdDistinct).IsNull := by
    unfold Purelib.Geometry.Plane.Line.IsNull Line.Incidence.lineThrough second third
    decide
  {
    first := first
    second := second
    third := third
    notCollinear := notCollinear
    firstSecondDistinct := firstSecondDistinct
    firstThirdDistinct :=
      firstThirdDistinct
    secondThirdDistinct := secondThirdDistinct
    firstSecondNonNull := firstSecondNonNull
    firstThirdNonNull := firstThirdNonNull
    secondThirdNonNull := secondThirdNonNull
  }

/-- The two sides through the origin are perpendicular. -/
public theorem rightAtThird :
    (Line.Incidence.lineThrough first third ExerciseTenSix.firstThirdDistinct).Perpendicular
      (Line.Incidence.lineThrough second third ExerciseTenSix.secondThirdDistinct) := by
  unfold Purelib.Geometry.Plane.Line.Perpendicular Line.Incidence.lineThrough first second third
  ring1

/-- The opposite-side quadrances of the displayed right triangle are 16, 9 and 25. -/
theorem quadrance_values : triangle.quadrances = ⟨16, 9, 25⟩ := by
  apply Vector3.ext <;>
    unfold NonNull.Basic.NonNullTriangle.quadrances Quadrance.Basic.triangleQuadrances Point.Quadrance.quadrance
      triangle first second third <;>
    ring1

/-- The altitude foot has quadrances 81/25, 256/25 and 144/25 from the three vertices.

These values use the retained right-angle witness and distinguish the two endpoint formulas. -/
theorem corrected_values :
    Point.Quadrance.quadrance first (Altitude.Foot.NonNullTriangle.thirdAltitudeFoot triangle) = (81 :
      Fraction.Rational) / 25 ∧
      Point.Quadrance.quadrance second (Altitude.Foot.NonNullTriangle.thirdAltitudeFoot triangle) = (256 :
        Fraction.Rational) / 25 ∧
      Point.Quadrance.quadrance third (Altitude.Foot.NonNullTriangle.thirdAltitudeFoot triangle) = (144 :
        Fraction.Rational) / 25 := open formalisations.DivineProportions.Chapters.Examples.ChapterSix in by
  have corrected := Right.Altitude.quadrance_formulas triangle
    (Purelib.Data.Rat.Fraction.Order.Cast.rational_natCast_nonzero (by decide : 2 ≠ 0)) ExerciseTenSix.rightAtThird
  rw [quadrance_values] at corrected
  refine ⟨?_, ?_, ?_⟩
  · calc
      Point.Quadrance.quadrance first (Altitude.Foot.NonNullTriangle.thirdAltitudeFoot triangle) =
          (9 : Fraction.Rational) ^ 2 / 25 := corrected.1
      _ = 81 / 25 := by rw [show (9 : Fraction.Rational) ^ 2 = 81 by ring1]
  · calc
      Point.Quadrance.quadrance second (Altitude.Foot.NonNullTriangle.thirdAltitudeFoot triangle) =
          (16 : Fraction.Rational) ^ 2 / 25 := corrected.2.1
      _ = 256 / 25 := by rw [show (16 : Fraction.Rational) ^ 2 = 256 by ring1]
  · calc
      Point.Quadrance.quadrance third (Altitude.Foot.NonNullTriangle.thirdAltitudeFoot triangle) =
          (16 : Fraction.Rational) * 9 / 25 := corrected.2.2
      _ = 144 / 25 := by rw [show (16 : Fraction.Rational) * 9 = 144 by ring1]

/-- The first printed equation in Exercise 10.6 uses `Q₁²/Q₃`, but
this explicit right triangle gives `81/25`, whereas that printed expression
is `256/25`. -/
theorem exercise_10_6_printed_counterexample :
    Point.Quadrance.quadrance first (Altitude.Foot.NonNullTriangle.thirdAltitudeFoot triangle) ≠
      triangle.quadrances.t ^ 2 / triangle.quadrances.s := by
  intro printed
  have impossible : (81 : Fraction.Rational) / 25 = 256 / 25 := by
    calc
      (81 : Fraction.Rational) / 25 =
          Point.Quadrance.quadrance first (Altitude.Foot.NonNullTriangle.thirdAltitudeFoot triangle) :=
        corrected_values.1.symm
      _ = triangle.quadrances.t ^ 2 /
          triangle.quadrances.s := printed
      _ = (256 : Fraction.Rational) / 25 := by
        rw [quadrance_values]
        rw [show (16 : Fraction.Rational) ^ 2 = 256 by ring1]
  exact Fraction.Field.Finite.rational_div_ne_div_same_denominator
    (by decide : 81 ≠ 256) (by decide : 25 ≠ 0) impossible

end ExerciseTenSix

namespace ExerciseTenSeven

/-- The first vertex (2, 3) of the first congruence example. -/
def firstA : Purelib.Geometry.Plane.Point Fraction.Rational := ⟨2, 3⟩
/-- The second vertex (3, 1) of the first congruence example. -/
def secondA : Purelib.Geometry.Plane.Point Fraction.Rational := ⟨3, 1⟩
/-- The third vertex (10, 2) of the first congruence example. -/
def thirdA : Purelib.Geometry.Plane.Point Fraction.Rational := ⟨10, 2⟩

/-- The first vertex (0, 1) of the second congruence example. -/
def firstB : Purelib.Geometry.Plane.Point Fraction.Rational := ⟨0, 1⟩
/-- The second vertex (−2, 2) of the second congruence example. -/
def secondB : Purelib.Geometry.Plane.Point Fraction.Rational := ⟨-2, 2⟩
/-- The third vertex (5, 6) of the second congruence example. -/
def thirdB : Purelib.Geometry.Plane.Point Fraction.Rational := ⟨5, 6⟩

/-- Exercise 10.7.  The side triples are respectively `{50,65,5}` and
`{65,50,5}`, so the first two opposite sides are exchanged. -/
theorem exercise_10_7 :
    Congruence.Basic.CongruentTriangles firstA secondA thirdA firstB secondB thirdB := by
  apply Vector3.Permutation.SameEntries.bac
  · unfold Quadrance.Basic.triangleQuadrances Point.Quadrance.quadrance firstA secondA thirdA firstB secondB thirdB
    ring1
  · unfold Quadrance.Basic.triangleQuadrances Point.Quadrance.quadrance firstA secondA thirdA firstB secondB thirdB
    ring1
  · unfold Quadrance.Basic.triangleQuadrances Point.Quadrance.quadrance firstA secondA thirdA firstB secondB thirdB
    ring1

end ExerciseTenSeven

namespace ExerciseTenEight

/-- The first vertex (−4, 3) of the first similarity example. -/
def firstA : Purelib.Geometry.Plane.Point Fraction.Rational := ⟨-4, 3⟩
/-- The second vertex (6, 5) of the first similarity example. -/
def secondA : Purelib.Geometry.Plane.Point Fraction.Rational := ⟨6, 5⟩
/-- The third vertex (−1, 1) of the first similarity example. -/
def thirdA : Purelib.Geometry.Plane.Point Fraction.Rational := ⟨-1, 1⟩

/-- The first vertex (4, −7) of the second similarity example. -/
def firstB : Purelib.Geometry.Plane.Point Fraction.Rational := ⟨4, -7⟩
/-- The second vertex (−2, −11) of the second similarity example. -/
def secondB : Purelib.Geometry.Plane.Point Fraction.Rational := ⟨-2, -11⟩
/-- The third vertex (2, 9) of the second similarity example. -/
def thirdB : Purelib.Geometry.Plane.Point Fraction.Rational := ⟨2, 9⟩

/-- The first two vertices of triangle A are distinct. -/
private theorem firstSecondDistinctA : firstA ≠ secondA := by decide
/-- The first and third vertices of triangle A are distinct. -/
private theorem firstThirdDistinctA : firstA ≠ thirdA := by decide
/-- The second and third vertices of triangle A are distinct. -/
private theorem secondThirdDistinctA : secondA ≠ thirdA := by decide
/-- The first two vertices of triangle B are distinct. -/
private theorem firstSecondDistinctB : firstB ≠ secondB := by decide
/-- The first and third vertices of triangle B are distinct. -/
private theorem firstThirdDistinctB : firstB ≠ thirdB := by decide
/-- The second and third vertices of triangle B are distinct. -/
private theorem secondThirdDistinctB : secondB ≠ thirdB := by decide

/-- The displayed vertices of triangle A are noncollinear. -/
private theorem notCollinearA : ¬ Line.Incidence.Collinear firstA secondA thirdA := by
  intro collinear
  have determinantZero :=
    Line.Incidence.pointDeterminant_eq_zero_of_collinear collinear
  have determinantNonzero : Line.Incidence.pointDeterminant firstA secondA thirdA ≠ 0 := by
    unfold Line.Incidence.pointDeterminant firstA secondA thirdA
    decide
  exact determinantNonzero determinantZero

/-- The displayed vertices of triangle B are noncollinear. -/
private theorem notCollinearB : ¬ Line.Incidence.Collinear firstB secondB thirdB := by
  intro collinear
  have determinantZero :=
    Line.Incidence.pointDeterminant_eq_zero_of_collinear collinear
  have determinantNonzero : Line.Incidence.pointDeterminant firstB secondB thirdB ≠ 0 := by
    unfold Line.Incidence.pointDeterminant firstB secondB thirdB
    decide
  exact determinantNonzero determinantZero

/-- The first-to-second side of triangle A has nonzero norm. -/
private theorem firstSecondNonNullA :
    ¬ (Line.Incidence.lineThrough firstA secondA ExerciseTenEight.firstSecondDistinctA).IsNull := by
  unfold Purelib.Geometry.Plane.Line.IsNull Line.Incidence.lineThrough firstA secondA
  decide

/-- The first-to-third side of triangle A has nonzero norm. -/
private theorem firstThirdNonNullA :
    ¬ (Line.Incidence.lineThrough firstA thirdA ExerciseTenEight.firstThirdDistinctA).IsNull := by
  unfold Purelib.Geometry.Plane.Line.IsNull Line.Incidence.lineThrough firstA thirdA
  decide

/-- The second-to-third side of triangle A has nonzero norm. -/
private theorem secondThirdNonNullA :
    ¬ (Line.Incidence.lineThrough secondA thirdA ExerciseTenEight.secondThirdDistinctA).IsNull := by
  unfold Purelib.Geometry.Plane.Line.IsNull Line.Incidence.lineThrough secondA thirdA
  decide

/-- The first-to-second side of triangle B has nonzero norm. -/
private theorem firstSecondNonNullB :
    ¬ (Line.Incidence.lineThrough firstB secondB ExerciseTenEight.firstSecondDistinctB).IsNull := by
  unfold Purelib.Geometry.Plane.Line.IsNull Line.Incidence.lineThrough firstB secondB
  decide

/-- The first-to-third side of triangle B has nonzero norm. -/
private theorem firstThirdNonNullB :
    ¬ (Line.Incidence.lineThrough firstB thirdB ExerciseTenEight.firstThirdDistinctB).IsNull := by
  unfold Purelib.Geometry.Plane.Line.IsNull Line.Incidence.lineThrough firstB thirdB
  decide

/-- The second-to-third side of triangle B has nonzero norm. -/
private theorem secondThirdNonNullB :
    ¬ (Line.Incidence.lineThrough secondB thirdB ExerciseTenEight.secondThirdDistinctB).IsNull := by
  unfold Purelib.Geometry.Plane.Line.IsNull Line.Incidence.lineThrough secondB thirdB
  decide

/-- The first certified rational triangle in the similarity example.

Retain the displayed three vertices and the proofs of noncollinearity, distinctness and non-null sides. -/
def triangleA : NonNull.Basic.NonNullTriangle Fraction.Rational :=
  let
    firstSecondDistinctA
    : firstA ≠ secondA := by decide
  let
    firstThirdDistinctA
    : firstA ≠ thirdA := by decide
  let
    secondThirdDistinctA
    : secondA ≠ thirdA := by decide
  let formalisations.DivineProportions.Chapters.Examples.ChapterTen.ChapterTenExamples.ExerciseTenEight.notCollinearA :
    ¬ Line.Incidence.Collinear firstA secondA thirdA := by
    intro collinear
    have determinantZero :=
      Line.Incidence.pointDeterminant_eq_zero_of_collinear collinear
    have determinantNonzero : Line.Incidence.pointDeterminant firstA secondA thirdA ≠ 0 := by
      unfold Line.Incidence.pointDeterminant firstA secondA thirdA
      decide
    exact determinantNonzero determinantZero
  let
    firstSecondNonNullA
    :
      ¬ (Line.Incidence.lineThrough firstA secondA
        firstSecondDistinctA).IsNull
        := by
    unfold Purelib.Geometry.Plane.Line.IsNull Line.Incidence.lineThrough firstA secondA
    decide
  let
    firstThirdNonNullA
    :
      ¬ (Line.Incidence.lineThrough firstA thirdA
        firstThirdDistinctA).IsNull
        := by
    unfold Purelib.Geometry.Plane.Line.IsNull Line.Incidence.lineThrough firstA thirdA
    decide
  let
    secondThirdNonNullA
    :
      ¬ (Line.Incidence.lineThrough secondA thirdA
        secondThirdDistinctA).IsNull
        := by
    unfold Purelib.Geometry.Plane.Line.IsNull Line.Incidence.lineThrough secondA thirdA
    decide
  {
    first := firstA
    second := secondA
    third := thirdA
    notCollinear :=
      formalisations.DivineProportions.Chapters.Examples.ChapterTen.ChapterTenExamples.ExerciseTenEight.notCollinearA
    firstSecondDistinct :=
      firstSecondDistinctA
    firstThirdDistinct :=
      firstThirdDistinctA
    secondThirdDistinct :=
      secondThirdDistinctA
    firstSecondNonNull :=
      firstSecondNonNullA
    firstThirdNonNull :=
      firstThirdNonNullA
    secondThirdNonNull :=
      secondThirdNonNullA
  }

/-- The second certified rational triangle in the similarity example.

Retain the displayed three vertices and the proofs of noncollinearity, distinctness and non-null sides. -/
def triangleB : NonNull.Basic.NonNullTriangle Fraction.Rational :=
  let
    firstSecondDistinctB
    : firstB ≠ secondB := by decide
  let
    firstThirdDistinctB
    : firstB ≠ thirdB := by decide
  let
    secondThirdDistinctB
    : secondB ≠ thirdB := by decide
  let formalisations.DivineProportions.Chapters.Examples.ChapterTen.ChapterTenExamples.ExerciseTenEight.notCollinearB :
    ¬ Line.Incidence.Collinear firstB secondB thirdB := by
    intro collinear
    have determinantZero :=
      Line.Incidence.pointDeterminant_eq_zero_of_collinear collinear
    have determinantNonzero : Line.Incidence.pointDeterminant firstB secondB thirdB ≠ 0 := by
      unfold Line.Incidence.pointDeterminant firstB secondB thirdB
      decide
    exact determinantNonzero determinantZero
  let
    firstSecondNonNullB
    :
      ¬ (Line.Incidence.lineThrough firstB secondB
        firstSecondDistinctB).IsNull
        := by
    unfold Purelib.Geometry.Plane.Line.IsNull Line.Incidence.lineThrough firstB secondB
    decide
  let
    firstThirdNonNullB
    :
      ¬ (Line.Incidence.lineThrough firstB thirdB
        firstThirdDistinctB).IsNull
        := by
    unfold Purelib.Geometry.Plane.Line.IsNull Line.Incidence.lineThrough firstB thirdB
    decide
  let
    secondThirdNonNullB
    :
      ¬ (Line.Incidence.lineThrough secondB thirdB
        secondThirdDistinctB).IsNull
        := by
    unfold Purelib.Geometry.Plane.Line.IsNull Line.Incidence.lineThrough secondB thirdB
    decide
  {
    first := firstB
    second := secondB
    third := thirdB
    notCollinear :=
      formalisations.DivineProportions.Chapters.Examples.ChapterTen.ChapterTenExamples.ExerciseTenEight.notCollinearB
    firstSecondDistinct :=
      firstSecondDistinctB
    firstThirdDistinct :=
      firstThirdDistinctB
    secondThirdDistinct :=
      secondThirdDistinctB
    firstSecondNonNull :=
      firstSecondNonNullB
    firstThirdNonNull :=
      firstThirdNonNullB
    secondThirdNonNull :=
      secondThirdNonNullB
  }

/-- The first triangle has opposite-side quadrances `65,13,104`; the second
has `416,260,52`. -/
theorem quadrance_values :
    triangleA.quadrances = ⟨65, 13, 104⟩ ∧
      triangleB.quadrances = ⟨416, 260, 52⟩ := by
  constructor
  · apply Vector3.ext <;>
      unfold NonNull.Basic.NonNullTriangle.quadrances Quadrance.Basic.triangleQuadrances Point.Quadrance.quadrance
        ExerciseTenEight.triangleA firstA secondA thirdA <;>
      ring1
  · apply Vector3.ext <;>
      unfold NonNull.Basic.NonNullTriangle.quadrances Quadrance.Basic.triangleQuadrances Point.Quadrance.quadrance
        ExerciseTenEight.triangleB firstB secondB thirdB <;>
      ring1

/-- The first spread triple is `(1/2,1/10,4/5)`. -/
theorem triangleA_spread_values :
    triangleA.spreads.t = (1 : Fraction.Rational) / 2 ∧
      triangleA.spreads.r = (1 : Fraction.Rational) / 10 ∧
      triangleA.spreads.s = (4 : Fraction.Rational) / 5 := open
        formalisations.DivineProportions.Chapters.Examples.ChapterSix in by
  constructor
  · unfold NonNull.Basic.NonNullTriangle.spreads Line.Spread.spread
    apply Ratio.ratio_eq_of_cross_product
      (ExplicitField.mul_ne_zero ExerciseTenEight.firstSecondNonNullA ExerciseTenEight.firstThirdNonNullA)
      (Purelib.Data.Rat.Fraction.Order.Cast.rational_natCast_nonzero (by decide : 2 ≠ 0))
    unfold ExerciseTenEight.triangleA Line.Incidence.lineThrough firstA secondA thirdA
    ring1
  constructor
  · unfold NonNull.Basic.NonNullTriangle.spreads Line.Spread.spread
    apply Ratio.ratio_eq_of_cross_product
      (ExplicitField.mul_ne_zero
        triangleA.firstSecondReversedNonNull ExerciseTenEight.secondThirdNonNullA)
      (Purelib.Data.Rat.Fraction.Order.Cast.rational_natCast_nonzero (by decide : 10 ≠ 0))
    unfold ExerciseTenEight.triangleA Line.Incidence.lineThrough firstA secondA thirdA
    ring1
  · unfold NonNull.Basic.NonNullTriangle.spreads Line.Spread.spread
    apply Ratio.ratio_eq_of_cross_product
      (ExplicitField.mul_ne_zero
        triangleA.firstThirdReversedNonNull
        triangleA.secondThirdReversedNonNull)
      (Purelib.Data.Rat.Fraction.Order.Cast.rational_natCast_nonzero (by decide : 5 ≠ 0))
    unfold ExerciseTenEight.triangleA Line.Incidence.lineThrough firstA secondA thirdA
    ring1

/-- The second spread triple is `(4/5,1/2,1/10)`. -/
theorem triangleB_spread_values :
    triangleB.spreads.t = (4 : Fraction.Rational) / 5 ∧
      triangleB.spreads.r = (1 : Fraction.Rational) / 2 ∧
      triangleB.spreads.s = (1 : Fraction.Rational) / 10 := open
        formalisations.DivineProportions.Chapters.Examples.ChapterSix in by
  constructor
  · unfold NonNull.Basic.NonNullTriangle.spreads Line.Spread.spread
    apply Ratio.ratio_eq_of_cross_product
      (ExplicitField.mul_ne_zero ExerciseTenEight.firstSecondNonNullB ExerciseTenEight.firstThirdNonNullB)
      (Purelib.Data.Rat.Fraction.Order.Cast.rational_natCast_nonzero (by decide : 5 ≠ 0))
    unfold ExerciseTenEight.triangleB Line.Incidence.lineThrough firstB secondB thirdB
    ring1
  constructor
  · unfold NonNull.Basic.NonNullTriangle.spreads Line.Spread.spread
    apply Ratio.ratio_eq_of_cross_product
      (ExplicitField.mul_ne_zero
        triangleB.firstSecondReversedNonNull ExerciseTenEight.secondThirdNonNullB)
      (Purelib.Data.Rat.Fraction.Order.Cast.rational_natCast_nonzero (by decide : 2 ≠ 0))
    unfold ExerciseTenEight.triangleB Line.Incidence.lineThrough firstB secondB thirdB
    ring1
  · unfold NonNull.Basic.NonNullTriangle.spreads Line.Spread.spread
    apply Ratio.ratio_eq_of_cross_product
      (ExplicitField.mul_ne_zero
        triangleB.firstThirdReversedNonNull
        triangleB.secondThirdReversedNonNull)
      (Purelib.Data.Rat.Fraction.Order.Cast.rational_natCast_nonzero (by decide : 10 ≠ 0))
    unfold ExerciseTenEight.triangleB Line.Incidence.lineThrough firstB secondB thirdB
    ring1

/-- The displayed triangles are similar by a cyclic permutation of their spreads. -/
theorem triangles_similar : triangleA.Similar ExerciseTenEight.triangleB := by
  apply Vector3.Permutation.SameEntries.bca
  · exact triangleA_spread_values.1.trans triangleB_spread_values.2.1.symm
  · exact triangleA_spread_values.2.1.trans
      triangleB_spread_values.2.2.symm
  · exact triangleA_spread_values.2.2.trans triangleB_spread_values.1.symm

/-- The displayed triangles are not congruent because their quadrance triples have no matching permutation. -/
theorem triangles_not_congruent : ¬ triangleA.Congruent ExerciseTenEight.triangleB := by
  intro congruent
  have sameValues :
      Vector3.Permutation.SameEntries triangleA.quadrances triangleB.quadrances :=
    congruent
  rw [quadrance_values.1, quadrance_values.2] at sameValues
  rcases sameValues with
    ⟨first, _second, _third⟩ | ⟨first, _second, _third⟩ |
    ⟨first, _second, _third⟩ | ⟨first, _second, _third⟩ |
    ⟨first, _second, _third⟩ | ⟨first, _second, _third⟩
  · exact Fraction.Field.Finite.rational_natCast_ne (by decide : 65 ≠ 416) first
  · exact Fraction.Field.Finite.rational_natCast_ne (by decide : 65 ≠ 416) first
  · exact Fraction.Field.Finite.rational_natCast_ne (by decide : 65 ≠ 260) first
  · exact Fraction.Field.Finite.rational_natCast_ne (by decide : 65 ≠ 260) first
  · exact Fraction.Field.Finite.rational_natCast_ne (by decide : 65 ≠ 52) first
  · exact Fraction.Field.Finite.rational_natCast_ne (by decide : 65 ≠ 52) first

/-- The two displayed triangles are similar but not congruent.

The conjunction retains both the similarity witness and the obstruction to congruence for the explicit pair (Exercise
10.8). -/
theorem exercise_10_8 : triangleA.Similar ExerciseTenEight.triangleB ∧
    ¬ triangleA.Congruent ExerciseTenEight.triangleB :=
  ⟨ExerciseTenEight.triangles_similar, ExerciseTenEight.triangles_not_congruent⟩

end ExerciseTenEight

namespace ExampleTenOne

/-- The source's Cross-law equation after clearing its literal denominator is
exactly the displayed factorization. -/
theorem cross_law_factorization
    {K : Type*} [ExplicitField K] (q₂ : K) :
    13 * (q₂ - 12) ^ 2 = 98 * q₂ ↔
      (13 * q₂ - 72) * (q₂ - 26) = 0 := by
  constructor
  · intro cleared
    calc
      (13 * q₂ - 72) * (q₂ - 26) =
          13 * (q₂ - 12) ^ 2 - 98 * q₂ := by ring1
      _ = 0 := by rw [cleared]; ring1
  · intro factored
    have differenceZero :
        13 * (q₂ - 12) ^ 2 - 98 * q₂ = 0 := by
      calc
        13 * (q₂ - 12) ^ 2 - 98 * q₂ =
            (13 * q₂ - 72) * (q₂ - 26) := by ring1
        _ = 0 := factored
    exact Group.eq_of_sub_eq_zero differenceZero

/-- Example 10.1's two and only two candidates for `Q₂`, obtained by the
book's finite factorization. -/
theorem quadrance_alternatives
    {K : Type*} [ExplicitField K] [DecidableEq K]
    (q₂ : K) (thirteenNonzero : (13 : K) ≠ 0)
    (crossLaw : (q₂ - 12) ^ 2 = (98 / 13) * q₂) :
    q₂ = 72 / 13 ∨ q₂ = 26 := by
  have cleared : 13 * (q₂ - 12) ^ 2 = 98 * q₂ := by
    calc
      13 * (q₂ - 12) ^ 2 = (q₂ - 12) ^ 2 * 13 := by ring1
      _ = ((98 / 13) * q₂) * 13 := by rw [crossLaw]
      _ = ((98 / 13) * 13) * q₂ := by ring1
      _ = 98 * q₂ := by
        rw [ExplicitField.div_mul_cancel 98 thirteenNonzero]
  have factored := (ExampleTenOne.cross_law_factorization q₂).1 cleared
  by_cases secondFactorZero : q₂ - 26 = 0
  · exact Or.inr (Group.eq_of_sub_eq_zero secondFactorZero)
  · have firstFactorZero : 13 * q₂ - 72 = 0 := by
      by_cases firstZero : 13 * q₂ - 72 = 0
      · exact firstZero
      · exact False.elim
          ((ExplicitField.mul_ne_zero firstZero secondFactorZero)
            factored)
    left
    apply ExplicitField.eq_of_mul_eq_mul_left thirteenNonzero
    calc
      13 * q₂ = 72 := Group.eq_of_sub_eq_zero firstFactorZero
      _ = (72 / 13) * 13 :=
        (ExplicitField.div_mul_cancel 72 thirteenNonzero).symm
      _ = 13 * (72 / 13) := by ring1

/-- The rational cross-law equation has only the candidates 72/13 and 26. -/
theorem rational_quadrance_alternatives (q₂ : Fraction.Rational)
    (crossLaw : (q₂ - 12) ^ 2 = (98 / 13) * q₂) :
    q₂ = 72 / 13 ∨ q₂ = 26 :=
  open formalisations.DivineProportions.Chapters.Examples.ChapterSix in ExampleTenOne.quadrance_alternatives q₂
    (Purelib.Data.Rat.Fraction.Order.Cast.rational_natCast_nonzero (by decide : 13 ≠ 0)) crossLaw

/-- Recover the cross-law equation from its denominator-cleared form when thirteen is nonzero. -/
private theorem cross_law_of_cleared
    {K : Type*} [ExplicitField K]
    (q₂ : K) (thirteenNonzero : (13 : K) ≠ 0)
    (cleared : 13 * (q₂ - 12) ^ 2 = 98 * q₂) :
    (q₂ - 12) ^ 2 = (98 / 13) * q₂ := by
  apply ExplicitField.eq_of_mul_eq_mul_left thirteenNonzero
  calc
    13 * (q₂ - 12) ^ 2 = 98 * q₂ := cleared
    _ = ((98 / 13) * 13) * q₂ := by
      rw [ExplicitField.div_mul_cancel 98 thirteenNonzero]
    _ = 13 * ((98 / 13) * q₂) := by ring1

/-- Both displayed candidates satisfy the Cross-law equation used to obtain
them. -/
theorem quadrance_candidates_satisfy :
    (((72 : Fraction.Rational) / 13 - 12) ^ 2 =
        (98 / 13) * ((72 : Fraction.Rational) / 13)) ∧
      ((26 : Fraction.Rational) - 12) ^ 2 = (98 / 13) * 26 := open
        formalisations.DivineProportions.Chapters.Examples.ChapterSix in by
  have thirteenNonzero : (13 : Fraction.Rational) ≠ 0 :=
    Purelib.Data.Rat.Fraction.Order.Cast.rational_natCast_nonzero (by decide)
  constructor
  · apply ExampleTenOne.cross_law_of_cleared ((72 : Fraction.Rational) / 13) thirteenNonzero
    apply (ExampleTenOne.cross_law_factorization ((72 : Fraction.Rational) / 13)).2
    have firstFactorZero :
        13 * ((72 : Fraction.Rational) / 13) - 72 = 0 := by
      calc
        13 * ((72 : Fraction.Rational) / 13) - 72 =
            ((72 : Fraction.Rational) / 13) * 13 - 72 := by ring1
        _ = 72 - 72 := by
          rw [ExplicitField.div_mul_cancel 72 thirteenNonzero]
        _ = 0 := by ring1
    rw [firstFactorZero]
    ring1
  · apply ExampleTenOne.cross_law_of_cleared (26 : Fraction.Rational) thirteenNonzero
    apply (ExampleTenOne.cross_law_factorization (26 : Fraction.Rational)).2
    ring1

/-- The first candidate satisfies the first cross-product equality in the spread law. -/
private theorem case_one_first_cross :
    ((81 : Fraction.Rational) / 442) * ((72 : Fraction.Rational) / 13) =
      ((2916 : Fraction.Rational) / 14365) * 5 := by
  calc
    ((81 : Fraction.Rational) / 442) * ((72 : Fraction.Rational) / 13) =
        ((2916 : Fraction.Rational) / 14365) * ((5 : Fraction.Rational) / 1) :=
      Fraction.Field.Finite.rational_fraction_product_eq 81 442 72 13 2916 14365 5 1
        (by decide) (by decide) (by decide) (by decide) (by ring1)
    _ = ((2916 : Fraction.Rational) / 14365) * 5 := by
      rw [Fraction.Field.Finite.rational_div_one]

/-- The first candidate satisfies the second cross-product equality in the spread law. -/
private theorem case_one_second_cross :
    ((2916 : Fraction.Rational) / 14365) * 17 =
      ((81 : Fraction.Rational) / 130) * ((72 : Fraction.Rational) / 13) := by
  calc
    ((2916 : Fraction.Rational) / 14365) * 17 =
        ((2916 : Fraction.Rational) / 14365) * ((17 : Fraction.Rational) / 1) := by
      rw [Fraction.Field.Finite.rational_div_one]
    _ = ((81 : Fraction.Rational) / 130) * ((72 : Fraction.Rational) / 13) :=
      Fraction.Field.Finite.rational_fraction_product_eq 2916 14365 17 1 81 130 72 13
        (by decide) (by decide) (by decide) (by decide) (by ring1)

/-- The complete Spread-law quotient chain for the first candidate. -/
theorem first_spread_solution :
    ((81 : Fraction.Rational) / 442) / 5 =
        ((2916 : Fraction.Rational) / 14365) / ((72 : Fraction.Rational) / 13) ∧
      ((2916 : Fraction.Rational) / 14365) / ((72 : Fraction.Rational) / 13) =
        ((81 : Fraction.Rational) / 130) / 17 := open formalisations.DivineProportions.Chapters.Examples.ChapterSix in
          by
  have seventyTwoNonzero : (72 : Fraction.Rational) ≠ 0 :=
    Purelib.Data.Rat.Fraction.Order.Cast.rational_natCast_nonzero (by decide)
  have thirteenNonzero : (13 : Fraction.Rational) ≠ 0 :=
    Purelib.Data.Rat.Fraction.Order.Cast.rational_natCast_nonzero (by decide)
  have q₂Nonzero : (72 : Fraction.Rational) / 13 ≠ 0 :=
    ExplicitField.div_ne_zero seventyTwoNonzero thirteenNonzero
  exact ⟨
    Ratio.ratio_eq_of_cross_product
      (Purelib.Data.Rat.Fraction.Order.Cast.rational_natCast_nonzero (by decide : 5 ≠ 0)) q₂Nonzero
      ExampleTenOne.case_one_first_cross,
    Ratio.ratio_eq_of_cross_product q₂Nonzero
      (Purelib.Data.Rat.Fraction.Order.Cast.rational_natCast_nonzero (by decide : 17 ≠ 0))
      ExampleTenOne.case_one_second_cross⟩

/-- The second candidate satisfies the first cross-product equality in the spread law. -/
private theorem case_two_first_cross :
    ((81 : Fraction.Rational) / 442) * 26 =
      ((81 : Fraction.Rational) / 85) * 5 := by
  calc
    ((81 : Fraction.Rational) / 442) * 26 =
        ((81 : Fraction.Rational) / 442) * ((26 : Fraction.Rational) / 1) := by
      rw [Fraction.Field.Finite.rational_div_one]
    _ = ((81 : Fraction.Rational) / 85) * ((5 : Fraction.Rational) / 1) :=
      Fraction.Field.Finite.rational_fraction_product_eq 81 442 26 1 81 85 5 1
        (by decide) (by decide) (by decide) (by decide) (by ring1)
    _ = ((81 : Fraction.Rational) / 85) * 5 := by rw [Fraction.Field.Finite.rational_div_one]

/-- The second candidate satisfies the second cross-product equality in the spread law. -/
private theorem case_two_second_cross :
    ((81 : Fraction.Rational) / 85) * 17 =
      ((81 : Fraction.Rational) / 130) * 26 := by
  calc
    ((81 : Fraction.Rational) / 85) * 17 =
        ((81 : Fraction.Rational) / 85) * ((17 : Fraction.Rational) / 1) := by
      rw [Fraction.Field.Finite.rational_div_one]
    _ = ((81 : Fraction.Rational) / 130) * ((26 : Fraction.Rational) / 1) :=
      Fraction.Field.Finite.rational_fraction_product_eq 81 85 17 1 81 130 26 1
        (by decide) (by decide) (by decide) (by decide) (by ring1)
    _ = ((81 : Fraction.Rational) / 130) * 26 := by rw [Fraction.Field.Finite.rational_div_one]

/-- The complete Spread-law quotient chain for the second candidate. -/
theorem second_spread_solution :
    ((81 : Fraction.Rational) / 442) / 5 =
        ((81 : Fraction.Rational) / 85) / 26 ∧
      ((81 : Fraction.Rational) / 85) / 26 =
        ((81 : Fraction.Rational) / 130) / 17 := open formalisations.DivineProportions.Chapters.Examples.ChapterSix in
          by
  exact ⟨
    Ratio.ratio_eq_of_cross_product
      (Purelib.Data.Rat.Fraction.Order.Cast.rational_natCast_nonzero (by decide : 5 ≠ 0))
      (Purelib.Data.Rat.Fraction.Order.Cast.rational_natCast_nonzero (by decide : 26 ≠ 0))
      ExampleTenOne.case_two_first_cross,
    Ratio.ratio_eq_of_cross_product
      (Purelib.Data.Rat.Fraction.Order.Cast.rational_natCast_nonzero (by decide : 26 ≠ 0))
      (Purelib.Data.Rat.Fraction.Order.Cast.rational_natCast_nonzero (by decide : 17 ≠ 0))
      ExampleTenOne.case_two_second_cross⟩

/-- Example 10.1, collecting both Cross-law candidates and both displayed
Spread-law solutions. -/
theorem example_10_1 :
    ((((72 : Fraction.Rational) / 13 - 12) ^ 2 =
        (98 / 13) * ((72 : Fraction.Rational) / 13)) ∧
      ((26 : Fraction.Rational) - 12) ^ 2 = (98 / 13) * 26) ∧
      (((81 : Fraction.Rational) / 442) / 5 =
          ((2916 : Fraction.Rational) / 14365) / ((72 : Fraction.Rational) / 13) ∧
        ((2916 : Fraction.Rational) / 14365) / ((72 : Fraction.Rational) / 13) =
          ((81 : Fraction.Rational) / 130) / 17) ∧
      (((81 : Fraction.Rational) / 442) / 5 = ((81 : Fraction.Rational) / 85) / 26 ∧
        ((81 : Fraction.Rational) / 85) / 26 = ((81 : Fraction.Rational) / 130) / 17) :=
  ⟨ExampleTenOne.quadrance_candidates_satisfy, ExampleTenOne.first_spread_solution,
    ExampleTenOne.second_spread_solution⟩

end ExampleTenOne

namespace ExerciseTenTen

/-- The origin in the coordinate plane over the field with three elements. -/
def first : Purelib.Geometry.Plane.Point Finite.Three.Element := ⟨0, 0⟩
/-- The vertex (1, 0) over the field with three elements. -/
def second : Purelib.Geometry.Plane.Point Finite.Three.Element := ⟨1, 0⟩
/-- The vertex (0, 1) over the field with three elements. -/
def third : Purelib.Geometry.Plane.Point Finite.Three.Element := ⟨0, 1⟩

/-- The three displayed vertices over the field with three elements are noncollinear. -/
private theorem notCollinear : ¬ Line.Incidence.Collinear first second third := by
  intro collinear
  have determinantZero := Line.Incidence.pointDeterminant_eq_zero_of_collinear collinear
  exact (by decide : Line.Incidence.pointDeterminant first second third ≠ 0)
    determinantZero

/-- The certified triangle with vertices (0, 0), (1, 0) and (0, 1) over the field with three elements. -/
def triangle : NonNull.Basic.NonNullTriangle Finite.Three.Element :=
  let notCollinear : ¬ Line.Incidence.Collinear first second third := by
    intro collinear
    have determinantZero := Line.Incidence.pointDeterminant_eq_zero_of_collinear collinear
    exact (by decide : Line.Incidence.pointDeterminant first second third ≠ 0)
      determinantZero
  FiniteField.Three.Classification.nonNullTriangle first second third notCollinear

/-- A literal representative of Exercise 10.10: its quadrances are
`(2,1,1)`, its spreads are `(1,2,2)`, and the first vertex is right
isosceles. -/
theorem representative :
    triangle.quadrances = ⟨2, 1, 1⟩ ∧
      triangle.spreads = ⟨1, 2, 2⟩ ∧
      (Right.Isosceles.Basic.NonNullTriangle.RightIsoscelesAtFirst triangle) := by
  constructor
  · apply Vector3.ext <;> decide
  constructor
  · apply Vector3.ext <;> decide
  · unfold Right.Isosceles.Basic.NonNullTriangle.RightIsoscelesAtFirst
    constructor
    · decide
    · unfold Purelib.Geometry.Plane.Line.Perpendicular
      decide

end ExerciseTenTen

namespace ExerciseTenEleven

namespace SpreadThree

/-- The vertex (0, 1) of the singly-null triangle with opposite spread three. -/
def first : Purelib.Geometry.Plane.Point Finite.Five.Element := ⟨0, 1⟩
/-- The vertex (1, 2) of the singly-null triangle with opposite spread three. -/
def second : Purelib.Geometry.Plane.Point Finite.Five.Element := ⟨1, 2⟩
/-- The origin of the singly-null triangle with opposite spread three. -/
def third : Purelib.Geometry.Plane.Point Finite.Five.Element := ⟨0, 0⟩

/-- The vertices of the spread-three triangle over the field with five elements are noncollinear. -/
private theorem notCollinear : ¬ Line.Incidence.Collinear first second third := by
  intro collinear
  have determinantZero := Line.Incidence.pointDeterminant_eq_zero_of_collinear collinear
  exact (by decide : Line.Incidence.pointDeterminant first second third ≠ 0)
    determinantZero

/-- The displayed singly-null triangle over the field with five elements.

Its side opposite the first vertex has quadrance zero, while the other two quadrances are nonzero. -/
def triangle : FiniteField.Five.Null.Singly.Basic.SinglyNullAtFirst :=
  let notCollinear : ¬ Line.Incidence.Collinear first second third := by
    intro collinear
    have determinantZero := Line.Incidence.pointDeterminant_eq_zero_of_collinear collinear
    exact (by decide : Line.Incidence.pointDeterminant first second third ≠ 0)
      determinantZero
  {
    first := first
    second := second
    third := third
    notCollinear := notCollinear
    firstQuadranceZero := by decide
    secondQuadranceNonzero := by decide
    thirdQuadranceNonzero := by decide
  }

/-- The displayed singly-null triangle has quadrances 0, 1, 2 and opposite spread 3. -/
theorem quadrances_and_spread :
    Point.Quadrance.quadrance second third = 0 ∧
      Point.Quadrance.quadrance first third = 1 ∧
      Point.Quadrance.quadrance first second = 2 ∧
      triangle.oppositeSpread = 3 := by
  decide

end SpreadThree

namespace SpreadOne

/-- The vertex (0, 1) of the singly-null triangle with opposite spread one. -/
def first : Purelib.Geometry.Plane.Point Finite.Five.Element := ⟨0, 1⟩
/-- The vertex (2, 1) of the singly-null triangle with opposite spread one. -/
def second : Purelib.Geometry.Plane.Point Finite.Five.Element := ⟨2, 1⟩
/-- The origin of the singly-null triangle with opposite spread one. -/
def third : Purelib.Geometry.Plane.Point Finite.Five.Element := ⟨0, 0⟩

/-- The vertices of the spread-one triangle over the field with five elements are noncollinear. -/
private theorem notCollinear : ¬ Line.Incidence.Collinear first second third := by
  intro collinear
  have determinantZero := Line.Incidence.pointDeterminant_eq_zero_of_collinear collinear
  exact (by decide : Line.Incidence.pointDeterminant first second third ≠ 0)
    determinantZero

/-- The second displayed singly-null triangle over the field with five elements.

Its side opposite the first vertex has quadrance zero, while the other two quadrances are nonzero. -/
def triangle : FiniteField.Five.Null.Singly.Basic.SinglyNullAtFirst :=
  let notCollinear : ¬ Line.Incidence.Collinear first second third := by
    intro collinear
    have determinantZero := Line.Incidence.pointDeterminant_eq_zero_of_collinear collinear
    exact (by decide : Line.Incidence.pointDeterminant first second third ≠ 0)
      determinantZero
  {
    first := first
    second := second
    third := third
    notCollinear := notCollinear
    firstQuadranceZero := by decide
    secondQuadranceNonzero := by decide
    thirdQuadranceNonzero := by decide
  }

/-- The second displayed singly-null triangle has quadrances 0, 1, 4 and opposite spread 1. -/
theorem quadrances_and_spread :
    Point.Quadrance.quadrance second third = 0 ∧
      Point.Quadrance.quadrance first third = 1 ∧
      Point.Quadrance.quadrance first second = 4 ∧
      triangle.oppositeSpread = 1 := by
  decide

end SpreadOne

namespace TwoNullSides

/-- The vertex (0, 1) of the two-null-side triangle over the field with five elements. -/
def first : Purelib.Geometry.Plane.Point Finite.Five.Element := ⟨0, 1⟩
/-- The vertex (1, 3) of the two-null-side triangle over the field with five elements. -/
def second : Purelib.Geometry.Plane.Point Finite.Five.Element := ⟨1, 3⟩
/-- The origin of the two-null-side triangle over the field with five elements. -/
def third : Purelib.Geometry.Plane.Point Finite.Five.Element := ⟨0, 0⟩

/-- The first two vertices of the two-null-side triangle are distinct. -/
private theorem firstSecondDistinct : first ≠ second := by decide
/-- The first and third vertices of the two-null-side triangle are distinct. -/
private theorem firstThirdDistinct : first ≠ third := by decide
/-- The second and third vertices of the two-null-side triangle are distinct. -/
private theorem secondThirdDistinct : second ≠ third := by decide

/-- The two-null-side triangle over the field with five elements is noncollinear. -/
private theorem notCollinear : ¬ Line.Incidence.Collinear first second third := by
  intro collinear
  have determinantZero := Line.Incidence.pointDeterminant_eq_zero_of_collinear collinear
  exact (by decide : Line.Incidence.pointDeterminant first second third ≠ 0)
    determinantZero

/-- A noncollinear `F₅` triangle with two null sides.  Every vertex contains
at least one of those sides, so no vertex meets the two non-null premises
required by the book's definition of spread. -/
theorem separate_degenerate_regime :
    let firstSecondDistinct : first ≠ second := by decide
    let
      firstThirdWitness
      : first ≠ third := by decide
    let
      secondThirdWitness
      : second ≠ third := by decide
    ¬ Line.Incidence.Collinear first second third ∧
      (Line.Incidence.lineThrough first second firstSecondDistinct).IsNull ∧
      ¬ (Line.Incidence.lineThrough first third
        firstThirdWitness).IsNull
        ∧
      (Line.Incidence.lineThrough second third
        secondThirdWitness).IsNull
        := by
  dsimp only
  refine ⟨notCollinear, ?_, ?_, ?_⟩
  · unfold Purelib.Geometry.Plane.Line.IsNull
    decide
  · unfold Purelib.Geometry.Plane.Line.IsNull
    decide
  · unfold Purelib.Geometry.Plane.Line.IsNull
    decide

end TwoNullSides

/-- Both singly-null similarity values occur, while the two-null-side case is
a separate regime outside spread-based similarity. -/
theorem exercise_10_11_null_examples :
    SpreadThree.triangle.oppositeSpread = 3 ∧
      SpreadOne.triangle.oppositeSpread = 1 ∧
      ¬ Line.Incidence.Collinear TwoNullSides.first TwoNullSides.second TwoNullSides.third :=
  ⟨SpreadThree.quadrances_and_spread.2.2.2,
    SpreadOne.quadrances_and_spread.2.2.2,
    TwoNullSides.separate_degenerate_regime.1⟩

end ExerciseTenEleven

end ChapterTenExamples

end formalisations.DivineProportions.Chapters.Examples.ChapterTen

end
