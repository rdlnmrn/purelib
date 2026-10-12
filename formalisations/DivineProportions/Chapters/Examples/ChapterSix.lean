module
import Purelib.Algebra.Field.Ratio
import Purelib.Data.Rat.Fraction.Cast
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.Field.Squares
import Purelib.Geometry.Plane.Line.Basic
import Purelib.Geometry.Plane.Line.Incidence
import Purelib.Geometry.Plane.Line.Spread
public import Purelib.Geometry.Plane.Line.VertexBisector.Construction
import Purelib.Geometry.Plane.Line.VertexBisector.Existence
import Purelib.Geometry.Plane.Point.Basic
public import Purelib.Geometry.Triangles.Quadrance.Realization
import Purelib.Geometry.Triangles.Quadrea.Basic
import Purelib.Geometry.Trigonometry.QuadTriple.Basic
import Purelib.NumberTheory.SquareClass.Rational.Nonsquare
public import Purelib.Algebra.Field.Finite.Eleven
import Purelib.Data.Rat.Fraction.Compatibility
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Fraction.Order.Cast

open Purelib.Algebra.Field

open Purelib.Data.Rat

open Purelib.Geometry.Plane

open Purelib.Geometry.Triangles

open Purelib

section
@[expose] public section

/-!
# Divine Proportions, Exercises 6.1--6.2

Exercise 6.1 is proved by cancelling only the displayed non-null and
nonperpendicular denominators.  Exercise 6.2 is a closed constructive-rational
counterexample: two distinct nonperpendicular directions have complementary
spreads with a third line.
-/

section

open Purelib.Geometry

variable {K : Type*} [ExplicitField K]
namespace formalisations.DivineProportions.Chapters.Examples.ChapterSix.ExerciseSixTwo

/-- The fixed comparison line with coefficient direction `(0,1)`. -/
def comparison : Geometry.Plane.Line
  Fraction.Rational where
  a := 0
  b := 1
  c := 0
  direction_nonzero := Or.inr (by decide)

/-- First rational direction in the Exercise 6.2 counterexample. -/
def first : Geometry.Plane.Line
  Fraction.Rational where
  a := 4
  b := 3
  c := 0
  direction_nonzero := Or.inl (by decide)

/-- Second rational direction in the Exercise 6.2 counterexample. -/
def second : Geometry.Plane.Line
  Fraction.Rational where
  a := 3
  b := 4
  c := 0
  direction_nonzero := Or.inl (by decide)

end formalisations.DivineProportions.Chapters.Examples.ChapterSix.ExerciseSixTwo

section
namespace formalisations.DivineProportions.Chapters.Examples.ChapterSix.ExerciseSixTwo

/-- The horizontal comparison line has nonzero norm. -/
private theorem
  comparisonNonNull
  : ¬ comparison.IsNull := by
  unfold comparison
      Geometry.Plane.Line.IsNull
  decide
/-- The first line with coefficients (4, 3, 0) has nonzero norm. -/
private theorem
  firstNonNull
  : ¬ first.IsNull := by
  unfold first Geometry.Plane.Line.IsNull
  decide
/-- The second line with coefficients (3, 4, 0) has nonzero norm. -/
private theorem
  secondNonNull
  : ¬ second.IsNull := by
  unfold second Geometry.Plane.Line.IsNull
  decide
end formalisations.DivineProportions.Chapters.Examples.ChapterSix.ExerciseSixTwo
end

namespace formalisations.DivineProportions.Chapters.Examples.ChapterSix.ExerciseSixTwo

/-- Exercise 6.2: complementary spreads with a third line do not force the
first two lines to be perpendicular.  Here the spreads are `16/25` and
`9/25`, while the coefficient dot product is `24`. -/
theorem exercise_6_2 :
    let comparisonNonNull : ¬
      comparison.IsNull := by
      unfold comparison
        Geometry.Plane.Line.IsNull
      decide
    let firstNonNull : ¬ first.IsNull := by
      unfold first
          Geometry.Plane.Line.IsNull
      decide
    let secondNonNull : ¬ second.IsNull :=
      by
      unfold second
          Geometry.Plane.Line.IsNull
      decide
    Line.Spread.spread first
      comparison firstNonNull
      comparisonNonNull = 16 / 25 ∧
      Line.Spread.spread second
        comparison secondNonNull
        comparisonNonNull = 9 / 25 ∧
      Line.Spread.spread first
        comparison firstNonNull
        comparisonNonNull +
          Line.Spread.spread second
            comparison secondNonNull
            comparisonNonNull = 1 ∧
      ¬ first.Perpendicular
        formalisations.DivineProportions.Chapters.Examples.ChapterSix.ExerciseSixTwo.second := by
  dsimp only
  unfold Line.Spread.spread Line.Basic.lineNorm
    first
    second
    comparison
    Geometry.Plane.Line.Perpendicular
  decide

end formalisations.DivineProportions.Chapters.Examples.ChapterSix.ExerciseSixTwo

end

end

section
@[expose] public section

/-!
# Divine Proportions, Chapter 6 worked examples

The numerical examples use the project's executable constructive rational
field.  Every equality below reduces to finite integer arithmetic; no decimal
or completed-real interpretation is involved.
-/

namespace formalisations.DivineProportions.Chapters.Examples.ChapterSix

namespace ChapterSixExamples

/-- Two is nonzero in the rational field. -/
private theorem rational_two_nonzero : (2 : Fraction.Rational) ≠ 0 := by decide

/-- Ten is nonzero in the rational field. -/
private theorem rational_ten_nonzero : (10 : Fraction.Rational) ≠ 0 :=
  Purelib.Data.Rat.Fraction.Order.Cast.rational_natCast_nonzero (by
    decide)

/-- Fifty is nonzero in the rational field. -/
private theorem rational_fifty_nonzero : (50 : Fraction.Rational) ≠ 0 :=
  Purelib.Data.Rat.Fraction.Order.Cast.rational_natCast_nonzero (by
    decide)
namespace ExampleSixOne

/-- Example 6.1's exact quadrea and three displayed spread quotients.  The
book's decimal-field calculation is retained entirely in the constructive
rationals. -/
theorem example_6_1 :
    Geometry.Trigonometry.QuadTriple.Basic.archimedesFunction (16 : Fraction.Rational) 36 9 = 455 ∧
      (455 : Fraction.Rational) / (4 * 36 * 9) = 455 / 1296 ∧
      (455 : Fraction.Rational) / (4 * 16 * 9) = 455 / 576 ∧
      (455 : Fraction.Rational) / (4 * 16 * 36) = 455 / 2304 := by
  constructor
  · unfold Geometry.Trigonometry.QuadTriple.Basic.archimedesFunction
    ring1
  constructor
  · rw [show (4 : Fraction.Rational) * 36 * 9 = 1296 by ring1]
  constructor
  · rw [show (4 : Fraction.Rational) * 16 * 9 = 576 by ring1]
  · rw [show (4 : Fraction.Rational) * 16 * 36 = 2304 by ring1]

end ExampleSixOne

namespace ExampleSixTwo

/-- Example 6.2: no constructive-rational triangle has quadrances
`16,36,9`, because its forced quadrea `455` is not a rational square. -/
theorem example_6_2 :
    ¬ Quadrance.Realization.HasTriangleQuadrances (16 : Fraction.Rational) 36 9 := by
  rintro ⟨first, second, third, _notCollinear,
    firstQuadrance, secondQuadrance, thirdQuadrance⟩
  apply NumberTheory.SquareClass.Rational.Nonsquare.square_ne_455
    (2 * Line.Incidence.pointDeterminant first second third)
  calc
    (2 * Line.Incidence.pointDeterminant first second third) ^ 2 =
        4 * Line.Incidence.pointDeterminant first second third ^ 2 := by ring1
    _ = Quadrea.Basic.quadrea first second third :=
      (Quadrea.Basic.quadrea_coordinate_formula first second third).symm
    _ = Geometry.Trigonometry.QuadTriple.Basic.archimedesFunction (16 : Fraction.Rational) 36 9 := by
      unfold Quadrea.Basic.quadrea
      rw [firstQuadrance, secondQuadrance, thirdQuadrance]
    _ = 455 := by
      unfold Geometry.Trigonometry.QuadTriple.Basic.archimedesFunction
      ring1

end ExampleSixTwo

namespace ExampleSixThree

/-- A concrete first vertex realizing the existence assertion in Example
6.3. -/
def firstPoint : Geometry.Plane.Point Finite.Eleven.Element := ⟨0, 5⟩

/-- A concrete second vertex realizing the existence assertion in Example
6.3. -/
def secondPoint : Geometry.Plane.Point Finite.Eleven.Element := ⟨2, 1⟩

/-- The origin is the third vertex of the displayed realization. -/
def thirdPoint : Geometry.Plane.Point Finite.Eleven.Element := ⟨0, 0⟩

/-- The first and second displayed vertices over the field with eleven elements are distinct. -/
private theorem firstSecondDistinct : firstPoint ≠ secondPoint := by decide

/-- The first and third displayed vertices over the field with eleven elements are distinct. -/
private theorem firstThirdDistinct : firstPoint ≠ thirdPoint := by decide

/-- The second and third displayed vertices over the field with eleven elements are distinct. -/
private theorem secondThirdDistinct : secondPoint ≠ thirdPoint := by decide

/-- The line from the first vertex to the second has nonzero norm. -/
private theorem firstSecondNonNull :
    ¬ (Line.Incidence.lineThrough firstPoint secondPoint firstSecondDistinct).IsNull := by
  unfold Geometry.Plane.Line.IsNull Line.Incidence.lineThrough firstPoint secondPoint
  decide

/-- The line from the first vertex to the third has nonzero norm. -/
private theorem firstThirdNonNull :
    ¬ (Line.Incidence.lineThrough firstPoint thirdPoint firstThirdDistinct).IsNull := by
  unfold Geometry.Plane.Line.IsNull Line.Incidence.lineThrough firstPoint thirdPoint
  decide

/-- The line from the second vertex to the third has nonzero norm. -/
private theorem secondThirdNonNull :
    ¬ (Line.Incidence.lineThrough secondPoint thirdPoint secondThirdDistinct).IsNull := by
  unfold Geometry.Plane.Line.IsNull Line.Incidence.lineThrough secondPoint thirdPoint
  decide

/-- The reversed line from the second vertex to the first has nonzero norm. -/
private theorem firstSecondReversedNonNull :
    ¬ (Line.Incidence.lineThrough secondPoint firstPoint firstSecondDistinct.symm).IsNull := by
  unfold Geometry.Plane.Line.IsNull Line.Incidence.lineThrough firstPoint secondPoint
  decide

/-- The reversed line from the third vertex to the first has nonzero norm. -/
private theorem firstThirdReversedNonNull :
    ¬ (Line.Incidence.lineThrough thirdPoint firstPoint firstThirdDistinct.symm).IsNull := by
  unfold Geometry.Plane.Line.IsNull Line.Incidence.lineThrough firstPoint thirdPoint
  decide

/-- The reversed line from the third vertex to the second has nonzero norm. -/
private theorem secondThirdReversedNonNull :
    ¬ (Line.Incidence.lineThrough thirdPoint secondPoint secondThirdDistinct.symm).IsNull := by
  unfold Geometry.Plane.Line.IsNull Line.Incidence.lineThrough secondPoint thirdPoint
  decide

/-- A triangle over the field with eleven elements realizes quadrances 5, 3 and 9.

The witness retains the displayed vertices, their distinctness and all six oriented side non-nullness proofs. -/
theorem triangle_exists : Quadrance.Realization.HasTriangleQuadrances (5 : Finite.Eleven.Element) 3 9 := by
  refine ⟨firstPoint, secondPoint, thirdPoint, ?_, by decide,
    by decide, by decide⟩
  intro collinear
  have determinantZero :=
    (Line.Incidence.collinear_iff_pointDeterminant_eq_zero
      firstPoint secondPoint thirdPoint).1 collinear
  have determinantNonzero :
      Line.Incidence.pointDeterminant firstPoint secondPoint thirdPoint ≠ 0 := by
    unfold Line.Incidence.pointDeterminant firstPoint secondPoint thirdPoint
    decide
  exact determinantNonzero determinantZero

/-- Example 6.3's exact characteristic-eleven quadrea and three spread
values, together with an explicit triangle realizing its quadrances. -/
theorem example_6_3 :
    let firstSecondDistinct : firstPoint ≠ secondPoint := by decide
    let firstThirdDistinct : firstPoint ≠ thirdPoint := by decide
    let secondThirdDistinct : secondPoint ≠ thirdPoint := by decide
    let firstSecondNonNull :
        ¬ (Line.Incidence.lineThrough firstPoint secondPoint firstSecondDistinct).IsNull := by
      unfold Geometry.Plane.Line.IsNull Line.Incidence.lineThrough firstPoint secondPoint
      decide
    let firstThirdNonNull :
        ¬ (Line.Incidence.lineThrough firstPoint thirdPoint firstThirdDistinct).IsNull := by
      unfold Geometry.Plane.Line.IsNull Line.Incidence.lineThrough firstPoint thirdPoint
      decide
    let secondThirdNonNull :
        ¬ (Line.Incidence.lineThrough secondPoint thirdPoint secondThirdDistinct).IsNull := by
      unfold Geometry.Plane.Line.IsNull Line.Incidence.lineThrough secondPoint thirdPoint
      decide
    let firstSecondReversedNonNull :
        ¬ (Line.Incidence.lineThrough secondPoint firstPoint firstSecondDistinct.symm).IsNull := by
      unfold Geometry.Plane.Line.IsNull Line.Incidence.lineThrough firstPoint secondPoint
      decide
    let firstThirdReversedNonNull :
        ¬ (Line.Incidence.lineThrough thirdPoint firstPoint firstThirdDistinct.symm).IsNull := by
      unfold Geometry.Plane.Line.IsNull Line.Incidence.lineThrough firstPoint thirdPoint
      decide
    let secondThirdReversedNonNull :
        ¬ (Line.Incidence.lineThrough thirdPoint secondPoint secondThirdDistinct.symm).IsNull := by
      unfold Geometry.Plane.Line.IsNull Line.Incidence.lineThrough secondPoint thirdPoint
      decide
    Geometry.Trigonometry.QuadTriple.Basic.archimedesFunction (5 : Finite.Eleven.Element) 3 9 = 4 ∧
      Line.Spread.spread
          (Line.Incidence.lineThrough firstPoint secondPoint firstSecondDistinct)
          (Line.Incidence.lineThrough firstPoint thirdPoint firstThirdDistinct)
          firstSecondNonNull firstThirdNonNull = 9 ∧
      Line.Spread.spread
          (Line.Incidence.lineThrough secondPoint firstPoint firstSecondDistinct.symm)
          (Line.Incidence.lineThrough secondPoint thirdPoint secondThirdDistinct)
          firstSecondReversedNonNull secondThirdNonNull = 1 ∧
      Line.Spread.spread
          (Line.Incidence.lineThrough thirdPoint firstPoint firstThirdDistinct.symm)
          (Line.Incidence.lineThrough thirdPoint secondPoint secondThirdDistinct.symm)
          firstThirdReversedNonNull secondThirdReversedNonNull = 3 ∧
      Quadrance.Realization.HasTriangleQuadrances (5 : Finite.Eleven.Element) 3 9 := by
  dsimp only
  refine ⟨by decide, ?_, ?_, ?_, triangle_exists⟩
  · unfold Line.Spread.spread Line.Basic.lineNorm Line.Incidence.lineThrough firstPoint secondPoint thirdPoint
    decide
  · unfold Line.Spread.spread Line.Basic.lineNorm Line.Incidence.lineThrough firstPoint secondPoint thirdPoint
    decide
  · unfold Line.Spread.spread Line.Basic.lineNorm Line.Incidence.lineThrough firstPoint secondPoint thirdPoint
    decide

end ExampleSixThree

namespace ExampleSixFour

/-- Example 6.4 over any requested finite field fragment carrying an element
`i` with `i²=-1`.  This records all printed complex arithmetic without
introducing a completed complex carrier. -/
theorem example_6_4 {K : Type*} [ExplicitField K] [Nontrivial K]
    (i : K) (iSquare : i ^ 2 = -1) (twoNonzero : (2 : K) ≠ 0) :
    Geometry.Trigonometry.QuadTriple.Basic.archimedesFunction (1 : K) 2 i = 6 * i ∧
      Geometry.Trigonometry.QuadTriple.Basic.archimedesFunction (1 : K) 2 i / (4 * 2 * i) = 3 / 4 ∧
      Geometry.Trigonometry.QuadTriple.Basic.archimedesFunction (1 : K) 2 i / (4 * 1 * i) = 3 / 2 ∧
      Geometry.Trigonometry.QuadTriple.Basic.archimedesFunction (1 : K) 2 i / (4 * 1 * 2) = 3 * i / 4 := by
  have iNonzero : i ≠ 0 := by
    intro iZero
    have negativeOneZero : (-1 : K) = 0 := by
      calc
        (-1 : K) = i ^ 2 := iSquare.symm
        _ = 0 := by rw [iZero]; ring1
    have oneNonzero : (1 : K) ≠ 0 := one_ne_zero
    apply oneNonzero
    calc
      (1 : K) = -(-1) := by ring1
      _ = 0 := by rw [negativeOneZero]; ring1
  have fourNonzero : (4 : K) ≠ 0 := by
    have fourAsProduct : (4 : K) = 2 * 2 := by ring1
    rw [fourAsProduct]
    exact ExplicitField.mul_ne_zero twoNonzero twoNonzero
  have firstDenominatorNonzero : (4 : K) * 2 * i ≠ 0 :=
    ExplicitField.mul_ne_zero
      (ExplicitField.mul_ne_zero fourNonzero twoNonzero) iNonzero
  have secondDenominatorNonzero : (4 : K) * 1 * i ≠ 0 := by
    simpa only [mul_one] using
      ExplicitField.mul_ne_zero fourNonzero iNonzero
  have thirdDenominatorNonzero : (4 : K) * 1 * 2 ≠ 0 := by
    simpa only [mul_one] using
      ExplicitField.mul_ne_zero fourNonzero twoNonzero
  have areaFormula : Geometry.Trigonometry.QuadTriple.Basic.archimedesFunction (1 : K) 2 i = 6 * i := by
    calc
      Geometry.Trigonometry.QuadTriple.Basic.archimedesFunction (1 : K) 2 i = 6 * i - (1 + i ^ 2) := by
        unfold Geometry.Trigonometry.QuadTriple.Basic.archimedesFunction
        ring1
      _ = 6 * i := by rw [iSquare]; ring1
  refine ⟨areaFormula, ?_, ?_, ?_⟩
  · apply Ratio.ratio_eq_of_cross_product firstDenominatorNonzero fourNonzero
    rw [areaFormula]
    ring1
  · apply Ratio.ratio_eq_of_cross_product secondDenominatorNonzero twoNonzero
    rw [areaFormula]
    ring1
  · apply Ratio.ratio_eq_of_cross_product thirdDenominatorNonzero fourNonzero
    rw [areaFormula]
    ring1

end ExampleSixFour

namespace ExampleSixFive

/-- Example 6.5's first line `⟨2 : 1 : -1⟩`. -/
def first : Geometry.Plane.Line Fraction.Rational where
  a := 2
  b := 1
  c := -1
  direction_nonzero := Or.inl (by decide)

/-- Example 6.5's second line `⟨11 : 2 : -4⟩`. -/
def second : Geometry.Plane.Line Fraction.Rational where
  a := 11
  b := 2
  c := -4
  direction_nonzero := Or.inl (by decide)

/-- The first displayed book bisector `⟨1 : -3 : 1⟩`. -/
def firstBisector : Geometry.Plane.Line Fraction.Rational where
  a := 1
  b := -3
  c := 1
  direction_nonzero := Or.inl (by decide)

/-- The second displayed book bisector `⟨21 : 7 : -9⟩`. -/
def secondBisector : Geometry.Plane.Line Fraction.Rational where
  a := 21
  b := 7
  c := -9
  direction_nonzero := Or.inl (by decide)

/-- The first rational line in Example 6.5 has nonzero norm. -/
theorem first_nonNull : ¬ first.IsNull := by
  unfold Geometry.Plane.Line.IsNull first
  decide

/-- The second rational line in Example 6.5 has nonzero norm. -/
theorem second_nonNull : ¬ second.IsNull := by
  unfold Geometry.Plane.Line.IsNull second
  decide

/-- The two rational lines in Example 6.5 are not parallel. -/
theorem not_parallel : ¬ first.Parallel second := by
  unfold Geometry.Plane.Line.Parallel first second
  decide

/-- The product of the two line norms in Example 6.5 is the square of 25. -/
theorem norm_product_square :
    (25 : Fraction.Rational) ^ 2 = Line.Basic.lineNorm first * Line.Basic.lineNorm second := by decide

/-- The negative algebraic bisector candidate equals the first displayed bisector. -/
theorem negative_candidate_is_firstBisector :
    (Line.VertexBisector.Construction.negativeVertexBisector first second 25 first_nonNull not_parallel).Equivalent
      firstBisector := by
  unfold Geometry.Plane.Line.Equivalent Line.VertexBisector.Construction.negativeVertexBisector first second
      firstBisector
    Line.Basic.lineNorm
  exact ⟨by ring1, by ring1, by ring1⟩

/-- The positive algebraic bisector candidate equals the second displayed bisector. -/
theorem positive_candidate_is_secondBisector :
    (Line.VertexBisector.Construction.positiveVertexBisector first second 25 first_nonNull not_parallel).Equivalent
      secondBisector := by
  unfold Geometry.Plane.Line.Equivalent Line.VertexBisector.Construction.positiveVertexBisector first second
      secondBisector
    Line.Basic.lineNorm
  exact ⟨by ring1, by ring1, by ring1⟩

/-- The first displayed bisector in Example 6.5 has nonzero norm. -/
theorem firstBisector_nonNull : ¬ firstBisector.IsNull := by
  unfold Geometry.Plane.Line.IsNull firstBisector
  decide

/-- The second displayed bisector in Example 6.5 has nonzero norm. -/
theorem secondBisector_nonNull : ¬ secondBisector.IsNull := by
  unfold Geometry.Plane.Line.IsNull secondBisector
  decide

/-- Example 6.5's first pair of equal spreads. -/
theorem firstBisector_spreads :
    Line.Spread.spread first firstBisector first_nonNull firstBisector_nonNull =
        (49 : Fraction.Rational) / 50 ∧
      Line.Spread.spread second firstBisector second_nonNull firstBisector_nonNull =
        (49 : Fraction.Rational) / 50 := by
  constructor
  · unfold Line.Spread.spread
    apply Ratio.ratio_eq_of_cross_product
      (ExplicitField.mul_ne_zero first_nonNull firstBisector_nonNull)
      rational_fifty_nonzero
    unfold first firstBisector
    ring1
  · unfold Line.Spread.spread
    apply Ratio.ratio_eq_of_cross_product
      (ExplicitField.mul_ne_zero second_nonNull firstBisector_nonNull)
      rational_fifty_nonzero
    unfold second firstBisector
    ring1

/-- Example 6.5's second pair of equal spreads. -/
theorem secondBisector_spreads :
    Line.Spread.spread first secondBisector first_nonNull secondBisector_nonNull =
        (1 : Fraction.Rational) / 50 ∧
      Line.Spread.spread second secondBisector second_nonNull secondBisector_nonNull =
        (1 : Fraction.Rational) / 50 := by
  constructor
  · unfold Line.Spread.spread
    apply Ratio.ratio_eq_of_cross_product
      (ExplicitField.mul_ne_zero first_nonNull secondBisector_nonNull)
      rational_fifty_nonzero
    unfold first secondBisector
    ring1
  · unfold Line.Spread.spread
    apply Ratio.ratio_eq_of_cross_product
      (ExplicitField.mul_ne_zero second_nonNull secondBisector_nonNull)
      rational_fifty_nonzero
    unfold second secondBisector
    ring1

/-- The two displayed bisectors in Example 6.5 are perpendicular. -/
theorem bisectors_perpendicular : firstBisector.Perpendicular secondBisector := by
  unfold Geometry.Plane.Line.Perpendicular firstBisector secondBisector
  ring1

/-- The complete exact-arithmetic content of Example 6.5. -/
theorem example_6_5 :
    Squares.IsNonzeroSquare (Line.Spread.spread first second first_nonNull second_nonNull) ∧
      firstBisector.Perpendicular secondBisector ∧
      Line.Spread.spread first firstBisector first_nonNull firstBisector_nonNull =
          (49 : Fraction.Rational) / 50 ∧
      Line.Spread.spread second firstBisector second_nonNull firstBisector_nonNull =
          (49 : Fraction.Rational) / 50 ∧
      Line.Spread.spread first secondBisector first_nonNull secondBisector_nonNull =
          (1 : Fraction.Rational) / 50 ∧
      Line.Spread.spread second secondBisector second_nonNull secondBisector_nonNull =
          (1 : Fraction.Rational) / 50 := by
  refine ⟨?_, bisectors_perpendicular,
    firstBisector_spreads.1, firstBisector_spreads.2,
    secondBisector_spreads.1, secondBisector_spreads.2⟩
  exact (Line.VertexBisector.Existence.vertex_bisector_exists_iff_spread_isNonzeroSquare first second
    first_nonNull second_nonNull not_parallel rational_two_nonzero).1
      ⟨Line.VertexBisector.Construction.negativeVertexBisector first second 25 first_nonNull not_parallel,
        Line.VertexBisector.Construction.negativeVertexBisector_isVertexBisector first second 25 first_nonNull
          second_nonNull not_parallel rational_two_nonzero norm_product_square⟩

end ExampleSixFive

namespace ExampleSixSix

/-- Example 6.6's first line `⟨3 : 1 : 5⟩`. -/
def first : Geometry.Plane.Line Fraction.Rational where
  a := 3
  b := 1
  c := 5
  direction_nonzero := Or.inl (by decide)

/-- Example 6.6's second line `⟨-3 : 1 : 2⟩`. -/
def second : Geometry.Plane.Line Fraction.Rational where
  a := -3
  b := 1
  c := 2
  direction_nonzero := Or.inl (by decide)

/-- The first displayed book bisector `⟨2 : 0 : 1⟩`. -/
def firstBisector : Geometry.Plane.Line Fraction.Rational where
  a := 2
  b := 0
  c := 1
  direction_nonzero := Or.inl (by decide)

/-- The second displayed book bisector `⟨0 : 2 : 7⟩`. -/
def secondBisector : Geometry.Plane.Line Fraction.Rational where
  a := 0
  b := 2
  c := 7
  direction_nonzero := Or.inr (by decide)

/-- The first rational line in Example 6.6 has nonzero norm. -/
theorem first_nonNull : ¬ first.IsNull := by
  unfold Geometry.Plane.Line.IsNull first
  decide

/-- The second rational line in Example 6.6 has nonzero norm. -/
theorem second_nonNull : ¬ second.IsNull := by
  unfold Geometry.Plane.Line.IsNull second
  decide

/-- The two rational lines in Example 6.6 are not parallel. -/
theorem not_parallel : ¬ first.Parallel second := by
  unfold Geometry.Plane.Line.Parallel first second
  decide

/-- The product of the two line norms in Example 6.6 is the square of 10. -/
theorem norm_product_square :
    (10 : Fraction.Rational) ^ 2 = Line.Basic.lineNorm first * Line.Basic.lineNorm second := by decide

/-- The negative algebraic bisector candidate equals the first displayed bisector. -/
theorem negative_candidate_is_firstBisector :
    (Line.VertexBisector.Construction.negativeVertexBisector first second 10 first_nonNull not_parallel).Equivalent
      firstBisector := by
  unfold Geometry.Plane.Line.Equivalent Line.VertexBisector.Construction.negativeVertexBisector first second
      firstBisector
    Line.Basic.lineNorm
  exact ⟨by ring1, by ring1, by ring1⟩

/-- The positive algebraic bisector candidate equals the second displayed bisector. -/
theorem positive_candidate_is_secondBisector :
    (Line.VertexBisector.Construction.positiveVertexBisector first second 10 first_nonNull not_parallel).Equivalent
      secondBisector := by
  unfold Geometry.Plane.Line.Equivalent Line.VertexBisector.Construction.positiveVertexBisector first second
      secondBisector
    Line.Basic.lineNorm
  exact ⟨by ring1, by ring1, by ring1⟩

/-- The first displayed bisector in Example 6.6 has nonzero norm. -/
theorem firstBisector_nonNull : ¬ firstBisector.IsNull := by
  unfold Geometry.Plane.Line.IsNull firstBisector
  decide

/-- The second displayed bisector in Example 6.6 has nonzero norm. -/
theorem secondBisector_nonNull : ¬ secondBisector.IsNull := by
  unfold Geometry.Plane.Line.IsNull secondBisector
  decide

/-- Example 6.6's first pair of equal spreads. -/
theorem firstBisector_spreads :
    Line.Spread.spread first firstBisector first_nonNull firstBisector_nonNull =
        (1 : Fraction.Rational) / 10 ∧
      Line.Spread.spread second firstBisector second_nonNull firstBisector_nonNull =
        (1 : Fraction.Rational) / 10 := by
  constructor
  · unfold Line.Spread.spread
    apply Ratio.ratio_eq_of_cross_product
      (ExplicitField.mul_ne_zero first_nonNull firstBisector_nonNull)
      rational_ten_nonzero
    unfold first firstBisector
    ring1
  · unfold Line.Spread.spread
    apply Ratio.ratio_eq_of_cross_product
      (ExplicitField.mul_ne_zero second_nonNull firstBisector_nonNull)
      rational_ten_nonzero
    unfold second firstBisector
    ring1

/-- Example 6.6's second pair of equal spreads. -/
theorem secondBisector_spreads :
    Line.Spread.spread first secondBisector first_nonNull secondBisector_nonNull =
        (9 : Fraction.Rational) / 10 ∧
      Line.Spread.spread second secondBisector second_nonNull secondBisector_nonNull =
        (9 : Fraction.Rational) / 10 := by
  constructor
  · unfold Line.Spread.spread
    apply Ratio.ratio_eq_of_cross_product
      (ExplicitField.mul_ne_zero first_nonNull secondBisector_nonNull)
      rational_ten_nonzero
    unfold first secondBisector
    ring1
  · unfold Line.Spread.spread
    apply Ratio.ratio_eq_of_cross_product
      (ExplicitField.mul_ne_zero second_nonNull secondBisector_nonNull)
      rational_ten_nonzero
    unfold second secondBisector
    ring1

/-- The two displayed bisectors in Example 6.6 are perpendicular. -/
theorem bisectors_perpendicular : firstBisector.Perpendicular secondBisector := by
  unfold Geometry.Plane.Line.Perpendicular firstBisector secondBisector
  ring1

/-- The complete exact-arithmetic content of Example 6.6. -/
theorem example_6_6 :
    Squares.IsNonzeroSquare (Line.Spread.spread first second first_nonNull second_nonNull) ∧
      firstBisector.Perpendicular secondBisector ∧
      Line.Spread.spread first firstBisector first_nonNull firstBisector_nonNull =
          (1 : Fraction.Rational) / 10 ∧
      Line.Spread.spread second firstBisector second_nonNull firstBisector_nonNull =
          (1 : Fraction.Rational) / 10 ∧
      Line.Spread.spread first secondBisector first_nonNull secondBisector_nonNull =
          (9 : Fraction.Rational) / 10 ∧
      Line.Spread.spread second secondBisector second_nonNull secondBisector_nonNull =
          (9 : Fraction.Rational) / 10 := by
  refine ⟨?_, bisectors_perpendicular,
    firstBisector_spreads.1, firstBisector_spreads.2,
    secondBisector_spreads.1, secondBisector_spreads.2⟩
  exact (Line.VertexBisector.Existence.vertex_bisector_exists_iff_spread_isNonzeroSquare first second
    first_nonNull second_nonNull not_parallel rational_two_nonzero).1
      ⟨Line.VertexBisector.Construction.positiveVertexBisector first second 10 first_nonNull not_parallel,
        Line.VertexBisector.Construction.positiveVertexBisector_isVertexBisector first second 10 first_nonNull
          second_nonNull not_parallel rational_two_nonzero norm_product_square⟩

end ExampleSixSix

end ChapterSixExamples

end formalisations.DivineProportions.Chapters.Examples.ChapterSix

end
