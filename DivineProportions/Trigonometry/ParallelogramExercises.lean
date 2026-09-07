import DivineProportions.Trigonometry.Quadrance

/-!
# Divine Proportions, Chapter 5 parallelogram exercises

The source's rectangle and rhombus conditions are retained as four finite
adjacent-side dot products and one finite diagonal dot product.  Their
connection with perpendicular displayed lines is proved without quotienting
line representatives.  Exercises 5.4--5.6 then follow from the coordinate-sum
form of the Parallelogram center theorem.
-/

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K]

/-- Dot product of the directions of the displayed segments `AB` and `CD`. -/
def segmentDirectionDot
    (first second third fourth : Point K) : K :=
  (second.x - first.x) * (fourth.x - third.x) +
    (second.y - first.y) * (fourth.y - third.y)

/-- The source's definition of a rectangle: all four pairs of adjacent sides
are perpendicular.  The surrounding theorem supplies the nondegenerate
quadrilateral and parallelogram premises. -/
def IsRectangle
    (first second third fourth : Point K) : Prop :=
  segmentDirectionDot first second second third = 0 ∧
    segmentDirectionDot second third third fourth = 0 ∧
    segmentDirectionDot third fourth fourth first = 0 ∧
    segmentDirectionDot fourth first first second = 0

/-- The metric part of the source's definition of a rhombus: the two
diagonals of the displayed parallelogram are perpendicular. -/
def HasPerpendicularDiagonals
    (first second third fourth : Point K) : Prop :=
  segmentDirectionDot first third second fourth = 0

/-- The source's definition of a rhombus: a parallelogram whose two
diagonals are perpendicular. -/
def IsRhombus
    (first second third fourth : Point K) : Prop :=
  ParallelogramSideConditions first second third fourth ∧
    HasPerpendicularDiagonals first second third fourth

/-- Segment-direction orthogonality is exactly perpendicularity of the two
corresponding displayed lines. -/
theorem segmentDirectionDot_eq_zero_iff_perpendicular [DecidableEq K]
    (first second third fourth : Point K)
    (firstSecondDistinct : first ≠ second)
    (thirdFourthDistinct : third ≠ fourth) :
    segmentDirectionDot first second third fourth = 0 ↔
      (lineThrough first second firstSecondDistinct).Perpendicular
        (lineThrough third fourth thirdFourthDistinct) := by
  unfold segmentDirectionDot Line.Perpendicular lineThrough
  constructor <;> intro equality
  · calc
      (first.y - second.y) * (third.y - fourth.y) +
          (second.x - first.x) * (fourth.x - third.x) =
        (second.x - first.x) * (fourth.x - third.x) +
          (second.y - first.y) * (fourth.y - third.y) := by ring1
      _ = 0 := equality
  · calc
      (second.x - first.x) * (fourth.x - third.x) +
          (second.y - first.y) * (fourth.y - third.y) =
        (first.y - second.y) * (third.y - fourth.y) +
          (second.x - first.x) * (fourth.x - third.x) := by ring1
      _ = 0 := equality

private theorem four_ne_zero [DecidableEq K]
    (twoNonzero : (2 : K) ≠ 0) : (4 : K) ≠ 0 := by
  have fourAsProduct : (4 : K) = 2 * 2 := by ring1
  rw [fourAsProduct]
  exact RFAP.ExplicitField.mul_ne_zero twoNonzero twoNonzero

/-- Exercise 5.4: a parallelogram has equal diagonal quadrances precisely
when all four adjacent side pairs are perpendicular, hence precisely when it
is a rectangle. -/
theorem exercise_5_4 [DecidableEq K]
    (first second third fourth : Point K)
    (twoNonzero : (2 : K) ≠ 0)
    (determinantNonzero : pointDeterminant first second third ≠ 0)
    (parallelSides : ParallelogramSideConditions first second third fourth) :
    quadrance first third = quadrance second fourth ↔
      IsRectangle first second third fourth := by
  rcases parallelogram_coordinate_sums first second third fourth
      twoNonzero determinantNonzero parallelSides with ⟨xSums, ySums⟩
  have fourthX : fourth.x = first.x - second.x + third.x := by
    calc
      fourth.x = first.x + third.x - second.x := by
        rw [xSums]
        ring1
      _ = first.x - second.x + third.x := by ring1
  have fourthY : fourth.y = first.y - second.y + third.y := by
    calc
      fourth.y = first.y + third.y - second.y := by
        rw [ySums]
        ring1
      _ = first.y - second.y + third.y := by ring1
  let adjacentDot := segmentDirectionDot first second second third
  have diagonalDifference :
      quadrance first third - quadrance second fourth =
        4 * adjacentDot := by
    unfold adjacentDot segmentDirectionDot quadrance
    rw [fourthX, fourthY]
    ring1
  have rectangleIff :
      IsRectangle first second third fourth ↔ adjacentDot = 0 := by
    unfold IsRectangle adjacentDot segmentDirectionDot
    rw [fourthX, fourthY]
    constructor
    · intro rectangle
      exact rectangle.1
    · intro dotZero
      refine ⟨dotZero, ?_, ?_, ?_⟩
      · calc
          (third.x - second.x) *
                (first.x - second.x + third.x - third.x) +
              (third.y - second.y) *
                (first.y - second.y + third.y - third.y) =
            -((second.x - first.x) * (third.x - second.x) +
              (second.y - first.y) * (third.y - second.y)) := by ring1
          _ = 0 := by rw [dotZero]; ring1
      · calc
          (first.x - second.x + third.x - third.x) *
                (first.x - (first.x - second.x + third.x)) +
              (first.y - second.y + third.y - third.y) *
                (first.y - (first.y - second.y + third.y)) =
            (second.x - first.x) * (third.x - second.x) +
              (second.y - first.y) * (third.y - second.y) := by ring1
          _ = 0 := dotZero
      · calc
          (first.x - (first.x - second.x + third.x)) *
                (second.x - first.x) +
              (first.y - (first.y - second.y + third.y)) *
                (second.y - first.y) =
            -((second.x - first.x) * (third.x - second.x) +
              (second.y - first.y) * (third.y - second.y)) := by ring1
          _ = 0 := by rw [dotZero]; ring1
  rw [rectangleIff]
  constructor
  · intro diagonalsEqual
    have productZero : (4 : K) * adjacentDot = 0 := by
      rw [← diagonalDifference, diagonalsEqual]
      ring1
    by_cases dotZero : adjacentDot = 0
    · exact dotZero
    · exact False.elim
        ((RFAP.ExplicitField.mul_ne_zero
          (four_ne_zero twoNonzero) dotZero) productZero)
  · intro dotZero
    apply sub_eq_zero.mp
    rw [diagonalDifference, dotZero]
    ring1

/-- Exercise 5.5: the sum of the two diagonal quadrances of a parallelogram
is twice the sum of two adjacent side quadrances. -/
theorem exercise_5_5 [DecidableEq K]
    (first second third fourth : Point K)
    (twoNonzero : (2 : K) ≠ 0)
    (determinantNonzero : pointDeterminant first second third ≠ 0)
    (parallelSides : ParallelogramSideConditions first second third fourth) :
    quadrance first third + quadrance second fourth =
      2 * (quadrance first second + quadrance second third) := by
  rcases parallelogram_coordinate_sums first second third fourth
      twoNonzero determinantNonzero parallelSides with ⟨xSums, ySums⟩
  have fourthX : fourth.x = first.x - second.x + third.x := by
    calc
      fourth.x = first.x + third.x - second.x := by
        rw [xSums]
        ring1
      _ = first.x - second.x + third.x := by ring1
  have fourthY : fourth.y = first.y - second.y + third.y := by
    calc
      fourth.y = first.y + third.y - second.y := by
        rw [ySums]
        ring1
      _ = first.y - second.y + third.y := by ring1
  unfold quadrance
  rw [fourthX, fourthY]
  ring1

/-- Exercise 5.6: all four side quadrances of a parallelogram are equal
precisely when its diagonals are perpendicular, hence precisely when it is a
rhombus. -/
theorem exercise_5_6 [DecidableEq K]
    (first second third fourth : Point K)
    (twoNonzero : (2 : K) ≠ 0)
    (determinantNonzero : pointDeterminant first second third ≠ 0)
    (parallelSides : ParallelogramSideConditions first second third fourth) :
    (quadrance first second = quadrance second third ∧
      quadrance second third = quadrance third fourth ∧
      quadrance third fourth = quadrance fourth first) ↔
      IsRhombus first second third fourth := by
  rcases parallelogram_coordinate_sums first second third fourth
      twoNonzero determinantNonzero parallelSides with ⟨xSums, ySums⟩
  have fourthX : fourth.x = first.x - second.x + third.x := by
    calc
      fourth.x = first.x + third.x - second.x := by
        rw [xSums]
        ring1
      _ = first.x - second.x + third.x := by ring1
  have fourthY : fourth.y = first.y - second.y + third.y := by
    calc
      fourth.y = first.y + third.y - second.y := by
        rw [ySums]
        ring1
      _ = first.y - second.y + third.y := by ring1
  constructor
  · intro allSidesEqual
    refine ⟨parallelSides, ?_⟩
    unfold HasPerpendicularDiagonals segmentDirectionDot
    unfold quadrance at allSidesEqual
    rw [fourthX, fourthY] at allSidesEqual ⊢
    calc
      (third.x - first.x) *
            (first.x - second.x + third.x - second.x) +
          (third.y - first.y) *
            (first.y - second.y + third.y - second.y) =
        ((third.x - second.x) ^ 2 +
            (third.y - second.y) ^ 2) -
          ((second.x - first.x) ^ 2 +
            (second.y - first.y) ^ 2) := by ring1
      _ = 0 := by rw [← allSidesEqual.1]; ring1
  · intro rhombus
    have diagonalsPerpendicular := rhombus.2
    unfold HasPerpendicularDiagonals segmentDirectionDot at diagonalsPerpendicular
    unfold quadrance
    rw [fourthX, fourthY] at diagonalsPerpendicular ⊢
    have adjacentEqual :
        (second.x - first.x) ^ 2 + (second.y - first.y) ^ 2 =
          (third.x - second.x) ^ 2 + (third.y - second.y) ^ 2 := by
      calc
        (second.x - first.x) ^ 2 + (second.y - first.y) ^ 2 =
            (third.x - second.x) ^ 2 + (third.y - second.y) ^ 2 -
              ((third.x - first.x) *
                  (first.x - second.x + third.x - second.x) +
                (third.y - first.y) *
                  (first.y - second.y + third.y - second.y)) := by ring1
        _ = (third.x - second.x) ^ 2 +
            (third.y - second.y) ^ 2 := by
              rw [diagonalsPerpendicular]
              ring1
    refine ⟨adjacentEqual, ?_, ?_⟩
    · calc
        (third.x - second.x) ^ 2 + (third.y - second.y) ^ 2 =
            (second.x - first.x) ^ 2 +
              (second.y - first.y) ^ 2 := adjacentEqual.symm
        _ = (first.x - second.x + third.x - third.x) ^ 2 +
            (first.y - second.y + third.y - third.y) ^ 2 := by ring1
    · calc
        (first.x - second.x + third.x - third.x) ^ 2 +
              (first.y - second.y + third.y - third.y) ^ 2 =
            (second.x - first.x) ^ 2 +
              (second.y - first.y) ^ 2 := by ring1
        _ = (third.x - second.x) ^ 2 +
            (third.y - second.y) ^ 2 := adjacentEqual
        _ = (first.x - (first.x - second.x + third.x)) ^ 2 +
            (first.y - (first.y - second.y + third.y)) ^ 2 := by ring1

end DivineProportions
