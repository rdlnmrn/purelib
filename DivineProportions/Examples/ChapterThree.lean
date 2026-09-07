import DivineProportions.Algebra.FieldEleven
import DivineProportions.Plane.Affine
import DivineProportions.Plane.LineRelations

/-!
# Divine Proportions, Chapter 3 finite examples

This module records the literal coordinate data in Examples 3.2, 3.6, and
3.7, together with an explicit quadrilateral for Exercise 3.14.  The
characteristic-thirteen calculations are generic polynomial certificates;
they do not enumerate a finite-field carrier or install another global field
model.
-/

namespace DivineProportions

namespace ChapterThreeExamples

namespace ExampleThreeTwo

/-- The first point displayed in Figure 3.2. -/
def first : Point FieldEleven.Element := ⟨3, 7⟩

/-- The second point displayed in Figure 3.2. -/
def second : Point FieldEleven.Element := ⟨6, 1⟩

/-- Example 3.2: the two displayed `F₁₁` coordinate pairs are distinct. -/
theorem example_3_2 : first ≠ second := by decide

end ExampleThreeTwo

namespace ExampleThreeSix

variable {K : Type*} [RFAP.ExplicitField K]

private theorem four_nonzero (twoNonzero : (2 : K) ≠ 0) :
    (4 : K) ≠ 0 := by
  intro fourZero
  apply (RFAP.ExplicitField.mul_ne_zero twoNonzero twoNonzero)
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
  direction_nonzero := Or.inr (four_nonzero twoNonzero)

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
        (altitudeThrough point (sourceLine twoNonzero)) := by
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
  · unfold Line.Equivalent printedAltitude altitudeThrough sourceLine point
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

variable {K : Type*} [RFAP.ExplicitField K]

def firstPoint : Point K := ⟨2, 8⟩
def secondPoint : Point K := ⟨9, 9⟩
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
    ¬ Collinear (firstPoint (K := K)) secondPoint thirdPoint ∧
      (firstLine (K := K)).Contains secondPoint ∧
      (firstLine (K := K)).Contains thirdPoint ∧
      (secondLine thirteenZero).Contains firstPoint ∧
      (secondLine thirteenZero).Contains thirdPoint ∧
      (thirdLine thirteenZero).Contains firstPoint ∧
      (thirdLine thirteenZero).Contains secondPoint := by
  have determinantOne :
      pointDeterminant firstPoint secondPoint thirdPoint = (1 : K) := by
    unfold pointDeterminant firstPoint secondPoint thirdPoint
    calc
      (2 : K) * 9 - 2 * 0 + 9 * 0 - 10 * 9 + 10 * 8 - 9 * 8 =
          1 - 5 * 13 := by ring1
      _ = 1 := by rw [thirteenZero]; ring1
  constructor
  · intro collinear
    have determinantZero :=
      (collinear_iff_pointDeterminant_eq_zero
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

variable {K : Type*} [RFAP.ExplicitField K]

def first : Point K := ⟨0, 0⟩
def second : Point K := ⟨0, 1⟩
def third : Point K := ⟨1, 0⟩
def fourth : Point K := ⟨2, 1⟩

omit [RFAP.ExplicitField K] in
private theorem points_ne_of_x_ne
    {left right : Point K} (xDifferent : left.x ≠ right.x) : left ≠ right := by
  intro equal
  exact xDifferent (congrArg Point.x equal)

omit [RFAP.ExplicitField K] in
private theorem points_ne_of_y_ne
    {left right : Point K} (yDifferent : left.y ≠ right.y) : left ≠ right := by
  intro equal
  exact yDifferent (congrArg Point.y equal)

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
      ¬ Collinear (first (K := K)) (second (K := K)) (third (K := K)) ∧
      ¬ Collinear (first (K := K)) (second (K := K)) (fourth (K := K)) ∧
      ¬ Collinear (first (K := K)) (third (K := K)) (fourth (K := K)) ∧
      ¬ Collinear (second (K := K)) (third (K := K)) (fourth (K := K)) ∧
      (lineThrough (first (K := K)) (third (K := K)) (by
          exact points_ne_of_x_ne (zero_ne_one : (0 : K) ≠ 1))).Parallel
        (lineThrough (second (K := K)) (fourth (K := K)) (by
          exact points_ne_of_x_ne (by
            intro zeroEqualsTwo
            exact twoNonzero zeroEqualsTwo.symm))) := by
  have firstSecondDistinct : first ≠ second :=
    points_ne_of_y_ne (zero_ne_one : (0 : K) ≠ 1)
  have firstThirdDistinct : first ≠ third :=
    points_ne_of_x_ne (zero_ne_one : (0 : K) ≠ 1)
  have firstFourthDistinct : first ≠ fourth :=
    points_ne_of_x_ne (by
      intro zeroEqualsTwo
      exact twoNonzero zeroEqualsTwo.symm)
  have secondThirdDistinct : second ≠ third :=
    points_ne_of_x_ne (zero_ne_one : (0 : K) ≠ 1)
  have secondFourthDistinct : second ≠ fourth :=
    points_ne_of_x_ne (by
      intro zeroEqualsTwo
      exact twoNonzero zeroEqualsTwo.symm)
  have thirdFourthDistinct : third ≠ fourth :=
    points_ne_of_x_ne (by
      intro oneEqualsTwo
      change (1 : K) = 2 at oneEqualsTwo
      apply (one_ne_zero : (1 : K) ≠ 0)
      calc
        (1 : K) = 2 - 1 := by ring1
        _ = 0 := by rw [← oneEqualsTwo]; ring1)
  have firstDeterminant :
      pointDeterminant first second third = (-1 : K) := by
    unfold pointDeterminant first second third
    ring1
  have secondDeterminant :
      pointDeterminant first second fourth = (-2 : K) := by
    unfold pointDeterminant first second fourth
    ring1
  have thirdDeterminant :
      pointDeterminant first third fourth = (1 : K) := by
    unfold pointDeterminant first third fourth
    ring1
  have fourthDeterminant :
      pointDeterminant second third fourth = (2 : K) := by
    unfold pointDeterminant second third fourth
    ring1
  have firstNoncollinear :
      ¬ Collinear (first (K := K)) second third := by
    intro collinear
    have zero := (collinear_iff_pointDeterminant_eq_zero
      first second third).1 collinear
    rw [firstDeterminant] at zero
    apply (one_ne_zero : (1 : K) ≠ 0)
    calc
      (1 : K) = -(-1) := by ring1
      _ = 0 := by rw [zero]; ring1
  have secondNoncollinear :
      ¬ Collinear (first (K := K)) second fourth := by
    intro collinear
    have zero := (collinear_iff_pointDeterminant_eq_zero
      first second fourth).1 collinear
    rw [secondDeterminant] at zero
    apply twoNonzero
    calc
      (2 : K) = -(-2) := by ring1
      _ = 0 := by rw [zero]; ring1
  have thirdNoncollinear :
      ¬ Collinear (first (K := K)) third fourth := by
    intro collinear
    have zero := (collinear_iff_pointDeterminant_eq_zero
      first third fourth).1 collinear
    rw [thirdDeterminant] at zero
    exact (one_ne_zero : (1 : K) ≠ 0) zero
  have fourthNoncollinear :
      ¬ Collinear (second (K := K)) third fourth := by
    intro collinear
    have zero := (collinear_iff_pointDeterminant_eq_zero
      second third fourth).1 collinear
    rw [fourthDeterminant] at zero
    exact twoNonzero zero
  refine ⟨firstSecondDistinct, firstThirdDistinct, firstFourthDistinct,
    secondThirdDistinct, secondFourthDistinct, thirdFourthDistinct,
    firstNoncollinear, secondNoncollinear, thirdNoncollinear,
    fourthNoncollinear, ?_⟩
  unfold Line.Parallel lineThrough first second third fourth
  ring1

end ExerciseThreeFourteen

end ChapterThreeExamples

end DivineProportions
