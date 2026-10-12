module
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Geometry.Plane.Line.Altitude
import Purelib.Geometry.Plane.Line.Basic
import Purelib.Geometry.Plane.Line.Construction
import Purelib.Geometry.Plane.Line.Incidence
public import Purelib.Geometry.Plane.Point.Affine
import Purelib.Geometry.Plane.Point.Basic
import Purelib.Geometry.Plane.Point.Laws
public import Purelib.Algebra.Field.Finite.Eleven
import Mathlib.Algebra.Ring.Defs
import Purelib.Tactic.Ring

open Purelib.Algebra.Field

open Purelib.Geometry
open Purelib.Geometry.Plane

section
@[expose] public section

/-!
# Divine Proportions, §§3.7–3.8: affine combinations

All parameters and witnesses are field elements.  Membership and uniqueness
are proved by finite coordinate algebra, with the nonzero coordinate selected
by decidable equality rather than by choice.
-/

namespace formalisations.DivineProportions.Chapters.Examples.ChapterThree

variable {K : Type*} [ExplicitField K]

/-- Example 3.8: the source's one-third/two-thirds combination has the printed
coordinate formula. -/
theorem example_3_8 (first second :
  Plane.Point K) :
    Point.Affine.affineCombination ((1 : K) / 3) first (2 / 3) second =
      ⟨first.x / 3 + 2 * second.x / 3,
        first.y / 3 + 2 * second.y / 3⟩ := by
  apply Plane.Point.ext <;>
    simp only [Point.Affine.affineCombination, ExplicitField.div_eq_mul_inv] <;>
    ring1
end formalisations.DivineProportions.Chapters.Examples.ChapterThree

end

end

section
@[expose] public section

/-!
# Divine Proportions, §3.4: the foot of an altitude

The construction is the exact rational formula printed in Theorem 8.  Its only
denominator is the direction quadrance `a² + b²`, so the source's non-null-line
hypothesis is exposed as the precise executable cancellation certificate.
-/

namespace formalisations.DivineProportions.Chapters.Examples.ChapterThree

variable {K : Type*} [ExplicitField K]
namespace ExampleThreeFive

/-- The point (7, 6) over the field with eleven elements. -/
def sourcePoint :
  Plane.Point Finite.Eleven.Element := ⟨7, 6⟩

/-- The source line with coefficients (10, 5, 1) over the field with eleven elements. -/
def sourceLine : Plane.Line
  Finite.Eleven.Element where
  a := 10
  b := 5
  c := 1
  direction_nonzero := Or.inl (by decide)

/-- The displayed altitude with coefficients (9, 4, 1) over the field with eleven elements. -/
def displayedAltitude :
  Plane.Line Finite.Eleven.Element where
  a := 9
  b := 4
  c := 1
  direction_nonzero := Or.inl (by decide)

/-- The source line in Example 3.5 has nonzero norm. -/
theorem sourceLine_nonNull : ¬
  sourceLine.IsNull := by
  unfold Plane.Line.IsNull
    sourceLine
  decide

/-- Example 3.5: the book's displayed altitude is a proportional
representative of the constructed altitude. -/
theorem altitude_equivalent :
    (Line.Construction.altitudeThrough
      sourcePoint
      sourceLine).Equivalent
      displayedAltitude := by
  unfold Plane.Line.Equivalent Line.Construction.altitudeThrough
    sourcePoint
    sourceLine
    displayedAltitude
  decide

/-- Example 3.5: the exact foot is `[2,9]` in `F₁₁`. -/
theorem foot_eq :
    Line.Altitude.altitudeFoot
      sourcePoint
      sourceLine
      sourceLine_nonNull = (⟨2, 9⟩ :
      Plane.Point Finite.Eleven.Element) := by
  decide

end ExampleThreeFive

end formalisations.DivineProportions.Chapters.Examples.ChapterThree

end

end

section
@[expose] public section

/-!
# Divine Proportions, Chapter 3: points, lines, and incidence

Lines are finite coefficient records, not sets of points and not quotients.
`Line.Equivalent` records the three cross-product equations expressing equality
of the ordered proportions.  This follows the source's finite algebra while
keeping every construction executable over both finite fields and the
constructive rationals.
-/

namespace formalisations.DivineProportions.Chapters.Examples.ChapterThree

variable {K : Type*}

section Incidence

variable [ExplicitField K]

/-- Example 3.1, first displayed rational/decimal point. -/
def example_3_1_first (K : Type*) [OfNat K 2]
  [OfNat K 3] : Plane.Point K := ⟨2, 3⟩

/-- Example 3.1, second displayed rational/decimal point. -/
def example_3_1_second (K : Type*) [OfNat K 2]
  [OfNat K 5] : Plane.Point K := ⟨5, 2⟩

/-- Example 3.3: the displayed line equation contains both displayed points. -/
theorem example_3_3 (K : Type*) [CommRing K] :
    (1 : K) * 2 + 3 * 3 - 11 = 0 ∧
      (1 : K) * 5 + 3 * 2 - 11 = 0 := by
  constructor <;> ring1

/-- Example 3.4, isolated as a characteristic-eleven calculation so it can be
instantiated by any executable finite field of that characteristic. -/
theorem example_3_4 (K : Type*) [CommRing K]
  (characteristicEleven : (11 : K) = 0) :
    (10 : K) * 3 + 5 * 7 + 1 = 0 ∧
      (10 : K) * 6 + 5 * 1 + 1 = 0 := by
  constructor
  · calc
      (10 : K) * 3 + 5 * 7 + 1 = 6 * 11 := by ring1
      _ = 0 := by rw [characteristicEleven]; ring1
  · calc
      (10 : K) * 6 + 5 * 1 + 1 = 6 * 11 := by ring1
      _ = 0 := by rw [characteristicEleven]; ring1

/-- Example 3.4 evaluated in the concrete eleven-element field. -/
theorem example_3_4_fieldEleven :
    (10 : Finite.Eleven.Element) * 3 + 5 * 7 + 1 = 0 ∧
      (10 : Finite.Eleven.Element) * 6 + 5 * 1 + 1 = 0 :=
  example_3_4 Finite.Eleven.Element
    Finite.Eleven.eleven_eq_zero

/-- Exercise 3.1: a zero line determinant need not mean affine concurrency.
These are three distinct parallel coefficient triples; already the first two
cannot contain one common point. -/
theorem exercise_3_1_counterexample [Nontrivial
  K] (point : Plane.Point K) :
    ¬ ((1 : K) * point.x + 0 * point.y + 0 = 0 ∧
      (1 : K) * point.x + 0 * point.y - 1 = 0) := by
  rintro ⟨firstEquation, secondEquation⟩
  have zeroEqualsOne : (0 : K) = 1 := by
    calc
      0 = ((1 : K) * point.x + 0 * point.y + 0) -
          ((1 : K) * point.x + 0 * point.y - 1) := by
        rw [firstEquation, secondEquation]
        ring1
      _ = 1 := by ring1
  exact zero_ne_one zeroEqualsOne
end Incidence

end formalisations.DivineProportions.Chapters.Examples.ChapterThree

end

end

section
@[expose] public section

/-!
# Divine Proportions, Chapter 3 finite examples

This module records the literal coordinate data in Examples 3.2, 3.6, and
3.7, together with an explicit quadrilateral for Exercise 3.14.  The
characteristic-thirteen calculations are generic polynomial certificates;
they do not enumerate a finite-field carrier or install another global field
model.
-/

namespace formalisations.DivineProportions.Chapters.Examples.ChapterThree

namespace ChapterThreeExamples

namespace ExampleThreeTwo

/-- The first point displayed in Figure 3.2. -/
def first : Point Finite.Eleven.Element := ⟨3, 7⟩

/-- The second point displayed in Figure 3.2. -/
def second : Point Finite.Eleven.Element := ⟨6, 1⟩

/-- Example 3.2: the two displayed `F₁₁` coordinate pairs are distinct. -/
theorem example_3_2 : first ≠ second := by decide

end ExampleThreeTwo

namespace ExampleThreeSix

variable {K : Type*} [ExplicitField K]

/-- Four is nonzero whenever two is nonzero in the explicit field. -/
private theorem four_nonzero (twoNonzero : (2 : K) ≠ 0) :
    (4 : K) ≠ 0 := by
  intro fourZero
  apply (ExplicitField.mul_ne_zero twoNonzero twoNonzero)
  calc
    (2 : K) * 2 = 4 := by ring1
    _ = 0 := fourZero

/-- The point `[5,2]` printed in Example 3.6. -/
def point : Point K := ⟨5, 2⟩

/-- The printed null line `⟨3:2:1⟩`. -/
def sourceLine (twoNonzero : (2 : K) ≠ 0) : Line K where
  a := 3
  b := 2
  c := 1
  direction_nonzero := Or.inr twoNonzero

/-- The printed altitude `⟨6:4:1⟩`. -/
def printedAltitude (twoNonzero : (2 : K) ≠ 0) : Line K where
  a := 6
  b := 4
  c := 1
  direction_nonzero := by
    exact Or.inr (four_nonzero twoNonzero)

/-- Example 3.6: in characteristic thirteen the printed altitude contains
`[5,2]`, is both perpendicular and parallel to the source line, both lines
are null, and the printed representative is equivalent to the executable
`altitudeThrough` construction. -/
theorem example_3_6
    (twoNonzero : (2 : K) ≠ 0) (thirteenZero : (13 : K) = 0) :
    (printedAltitude twoNonzero).Contains point ∧
      (printedAltitude twoNonzero).Perpendicular
        (sourceLine twoNonzero) ∧
      (printedAltitude twoNonzero).Parallel (sourceLine twoNonzero) ∧
      (sourceLine twoNonzero).IsNull ∧
      (printedAltitude twoNonzero).IsNull ∧
      (printedAltitude twoNonzero).Equivalent
        (Line.Construction.altitudeThrough point (sourceLine twoNonzero)) := by
  constructor
  · unfold printedAltitude point Line.Contains
    calc
      (6 : K) * 5 + 4 * 2 + 1 = 3 * 13 := by ring1
      _ = 0 := by rw [thirteenZero]; ring1
  constructor
  · unfold printedAltitude sourceLine Line.Perpendicular
    calc
      (6 : K) * 3 + 4 * 2 = 2 * 13 := by ring1
      _ = 0 := by rw [thirteenZero]; ring1
  constructor
  · unfold printedAltitude sourceLine Line.Parallel
    ring1
  constructor
  · unfold sourceLine Line.IsNull
    calc
      (3 : K) ^ 2 + 2 ^ 2 = 13 := by ring1
      _ = 0 := thirteenZero
  constructor
  · unfold printedAltitude Line.IsNull
    calc
      (6 : K) ^ 2 + 4 ^ 2 = 4 * 13 := by ring1
      _ = 0 := by rw [thirteenZero]; ring1
  · unfold Line.Equivalent printedAltitude Line.Construction.altitudeThrough sourceLine point
    exact ⟨
      by
        calc
          (6 : K) * 3 = (-2) * 4 + 2 * 13 := by ring1
          _ = (-2) * 4 := by rw [thirteenZero]; ring1,
      by
        calc
          (6 : K) * (2 * 5 - 3 * 2) = (-2) * 1 + 2 * 13 := by
            ring1
          _ = (-2) * 1 := by rw [thirteenZero]; ring1,
      by
        calc
          (4 : K) * (2 * 5 - 3 * 2) = 3 * 1 + 13 := by ring1
          _ = 3 * 1 := by rw [thirteenZero]; ring1⟩

end ExampleThreeSix

namespace ExampleThreeSeven

variable {K : Type*} [ExplicitField K]

/-- The first characteristic-thirteen point (2, 8). -/
def firstPoint : Point K := ⟨2, 8⟩
/-- The second characteristic-thirteen point (9, 9). -/
def secondPoint : Point K := ⟨9, 9⟩
/-- The third characteristic-thirteen point (10, 0). -/
def thirdPoint : Point K := ⟨10, 0⟩

/-- The printed line `A₂A₃=⟨9:1:1⟩`. -/
def firstLine [Nontrivial K] : Line K where
  a := 9
  b := 1
  c := 1
  direction_nonzero := Or.inr one_ne_zero

/-- The printed line `A₁A₃=⟨9:9:1⟩`. -/
def secondLine [Nontrivial K] (thirteenZero : (13 : K) = 0) : Line K where
  a := 9
  b := 9
  c := 1
  direction_nonzero := Or.inl (by
    intro nineZero
    apply (one_ne_zero : (1 : K) ≠ 0)
    calc
      (1 : K) = 3 * 9 - 2 * 13 := by ring1
      _ = 0 := by rw [nineZero, thirteenZero]; ring1)

/-- The printed line `A₁A₂=⟨7:3:1⟩`. -/
def thirdLine [Nontrivial K] (thirteenZero : (13 : K) = 0) : Line K where
  a := 7
  b := 3
  c := 1
  direction_nonzero := Or.inl (by
    intro sevenZero
    apply (one_ne_zero : (1 : K) ≠ 0)
    calc
      (1 : K) = 2 * 7 - 13 := by ring1
      _ = 0 := by rw [sevenZero, thirteenZero]; ring1)

/-- Example 3.7: the three printed characteristic-thirteen points are
noncollinear and each printed line contains exactly its displayed endpoint
pair. -/
theorem example_3_7 [Nontrivial K] [DecidableEq K]
    (thirteenZero : (13 : K) = 0) :
    ¬ Line.Incidence.Collinear (firstPoint (K := K)) secondPoint thirdPoint ∧
      (firstLine (K := K)).Contains secondPoint ∧
      (firstLine (K := K)).Contains thirdPoint ∧
      (secondLine thirteenZero).Contains firstPoint ∧
      (secondLine thirteenZero).Contains thirdPoint ∧
      (thirdLine thirteenZero).Contains firstPoint ∧
      (thirdLine thirteenZero).Contains secondPoint := by
  have determinantOne :
      Line.Incidence.pointDeterminant firstPoint secondPoint thirdPoint = (1 : K) := by
    unfold Line.Incidence.pointDeterminant firstPoint secondPoint thirdPoint
    calc
      (2 : K) * 9 - 2 * 0 + 9 * 0 - 10 * 9 + 10 * 8 - 9 * 8 =
          1 - 5 * 13 := by ring1
      _ = 1 := by rw [thirteenZero]; ring1
  constructor
  · intro collinear
    have determinantZero :=
      (Line.Incidence.collinear_iff_pointDeterminant_eq_zero
        firstPoint secondPoint thirdPoint).1 collinear
    rw [determinantOne] at determinantZero
    exact (one_ne_zero : (1 : K) ≠ 0) determinantZero
  constructor
  · unfold firstLine secondPoint Line.Contains
    calc
      (9 : K) * 9 + 1 * 9 + 1 = 7 * 13 := by ring1
      _ = 0 := by rw [thirteenZero]; ring1
  constructor
  · unfold firstLine thirdPoint Line.Contains
    calc
      (9 : K) * 10 + 1 * 0 + 1 = 7 * 13 := by ring1
      _ = 0 := by rw [thirteenZero]; ring1
  constructor
  · unfold secondLine firstPoint Line.Contains
    calc
      (9 : K) * 2 + 9 * 8 + 1 = 7 * 13 := by ring1
      _ = 0 := by rw [thirteenZero]; ring1
  constructor
  · unfold secondLine thirdPoint Line.Contains
    calc
      (9 : K) * 10 + 9 * 0 + 1 = 7 * 13 := by ring1
      _ = 0 := by rw [thirteenZero]; ring1
  constructor
  · unfold thirdLine firstPoint Line.Contains
    calc
      (7 : K) * 2 + 3 * 8 + 1 = 3 * 13 := by ring1
      _ = 0 := by rw [thirteenZero]; ring1
  · unfold thirdLine secondPoint Line.Contains
    calc
      (7 : K) * 9 + 3 * 9 + 1 = 7 * 13 := by ring1
      _ = 0 := by rw [thirteenZero]; ring1

end ExampleThreeSeven

namespace ExerciseThreeFourteen

variable {K : Type*} [ExplicitField K]

/-- The origin, first vertex of the parallel-diagonal quadrilateral. -/
def first : Point K := ⟨0, 0⟩
/-- The vertex (0, 1) of the parallel-diagonal quadrilateral. -/
def second : Point K := ⟨0, 1⟩
/-- The vertex (1, 0) of the parallel-diagonal quadrilateral. -/
def third : Point K := ⟨1, 0⟩
/-- The vertex (2, 1) of the parallel-diagonal quadrilateral. -/
def fourth : Point K := ⟨2, 1⟩

/-- Exercise 3.14: in every nontrivial field of characteristic different
from two, the four displayed points form a quadrilateral and its diagonal
lines are parallel. -/
theorem exercise_3_14 [Nontrivial K] [DecidableEq K]
    (twoNonzero : (2 : K) ≠ 0) :
    (first (K := K)) ≠ (second (K := K)) ∧
      (first (K := K)) ≠ (third (K := K)) ∧
      (first (K := K)) ≠ (fourth (K := K)) ∧
      (second (K := K)) ≠ (third (K := K)) ∧
      (second (K := K)) ≠ (fourth (K := K)) ∧
      (third (K := K)) ≠ (fourth (K := K)) ∧
      ¬ Line.Incidence.Collinear (first (K := K)) (second (K := K)) (third (K := K)) ∧
      ¬ Line.Incidence.Collinear (first (K := K)) (second (K := K)) (fourth (K := K)) ∧
      ¬ Line.Incidence.Collinear (first (K := K)) (third (K := K)) (fourth (K := K)) ∧
      ¬ Line.Incidence.Collinear (second (K := K)) (third (K := K)) (fourth (K := K)) ∧
      (Line.Incidence.lineThrough (first (K := K)) (third (K := K)) (by
          exact Point.Laws.points_ne_of_x_ne (zero_ne_one : (0 : K) ≠ 1))).Parallel
        (Line.Incidence.lineThrough (second (K := K)) (fourth (K := K)) (by
          exact Point.Laws.points_ne_of_x_ne (by
            intro zeroEqualsTwo
            exact twoNonzero zeroEqualsTwo.symm))) := by
  have firstSecondDistinct : first ≠ second :=
    Point.Laws.points_ne_of_y_ne (zero_ne_one : (0 : K) ≠ 1)
  have firstThirdDistinct : first ≠ third :=
    Point.Laws.points_ne_of_x_ne (zero_ne_one : (0 : K) ≠ 1)
  have firstFourthDistinct : first ≠ fourth :=
    Point.Laws.points_ne_of_x_ne (by
      intro zeroEqualsTwo
      exact twoNonzero zeroEqualsTwo.symm)
  have secondThirdDistinct : second ≠ third :=
    Point.Laws.points_ne_of_x_ne (zero_ne_one : (0 : K) ≠ 1)
  have secondFourthDistinct : second ≠ fourth :=
    Point.Laws.points_ne_of_x_ne (by
      intro zeroEqualsTwo
      exact twoNonzero zeroEqualsTwo.symm)
  have thirdFourthDistinct : third ≠ fourth :=
    Point.Laws.points_ne_of_x_ne (by
      intro oneEqualsTwo
      change (1 : K) = 2 at oneEqualsTwo
      apply (one_ne_zero : (1 : K) ≠ 0)
      calc
        (1 : K) = 2 - 1 := by ring1
        _ = 0 := by rw [← oneEqualsTwo]; ring1)
  have firstDeterminant :
      Line.Incidence.pointDeterminant first second third = (-1 : K) := by
    unfold Line.Incidence.pointDeterminant first second third
    ring1
  have secondDeterminant :
      Line.Incidence.pointDeterminant first second fourth = (-2 : K) := by
    unfold Line.Incidence.pointDeterminant first second fourth
    ring1
  have thirdDeterminant :
      Line.Incidence.pointDeterminant first third fourth = (1 : K) := by
    unfold Line.Incidence.pointDeterminant first third fourth
    ring1
  have fourthDeterminant :
      Line.Incidence.pointDeterminant second third fourth = (2 : K) := by
    unfold Line.Incidence.pointDeterminant second third fourth
    ring1
  have firstNoncollinear :
      ¬ Line.Incidence.Collinear (first (K := K)) second third := by
    intro collinear
    have zero := (Line.Incidence.collinear_iff_pointDeterminant_eq_zero
      first second third).1 collinear
    rw [firstDeterminant] at zero
    apply (one_ne_zero : (1 : K) ≠ 0)
    calc
      (1 : K) = -(-1) := by ring1
      _ = 0 := by rw [zero]; ring1
  have secondNoncollinear :
      ¬ Line.Incidence.Collinear (first (K := K)) second fourth := by
    intro collinear
    have zero := (Line.Incidence.collinear_iff_pointDeterminant_eq_zero
      first second fourth).1 collinear
    rw [secondDeterminant] at zero
    apply twoNonzero
    calc
      (2 : K) = -(-2) := by ring1
      _ = 0 := by rw [zero]; ring1
  have thirdNoncollinear :
      ¬ Line.Incidence.Collinear (first (K := K)) third fourth := by
    intro collinear
    have zero := (Line.Incidence.collinear_iff_pointDeterminant_eq_zero
      first third fourth).1 collinear
    rw [thirdDeterminant] at zero
    exact (one_ne_zero : (1 : K) ≠ 0) zero
  have fourthNoncollinear :
      ¬ Line.Incidence.Collinear (second (K := K)) third fourth := by
    intro collinear
    have zero := (Line.Incidence.collinear_iff_pointDeterminant_eq_zero
      second third fourth).1 collinear
    rw [fourthDeterminant] at zero
    exact twoNonzero zero
  refine ⟨firstSecondDistinct, firstThirdDistinct, firstFourthDistinct,
    secondThirdDistinct, secondFourthDistinct, thirdFourthDistinct,
    firstNoncollinear, secondNoncollinear, thirdNoncollinear,
    fourthNoncollinear, ?_⟩
  unfold Line.Parallel Line.Incidence.lineThrough first second third fourth
  ring1

end ExerciseThreeFourteen

end ChapterThreeExamples

end formalisations.DivineProportions.Chapters.Examples.ChapterThree

end

end
