import mathlib.Tactic.QuotientFreeRing
import DivineProportions.Circles.EqualProducts
import DivineProportions.Trigonometry.Quadrance

/-!
# Divine Proportions, Exercise 16.5: Brahmagupta's theorem

The two diagonal incidences are retained as finite Thales parameters.  The
signed chord-power formula equates their parameter products, and diagonal
perpendicularity then proves directly that the opposite-side midpoint lies on
the required altitude.
-/

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K]

namespace Conic

/-- Exercise 16.5 (Brahmagupta): in a cyclic quadrilateral with perpendicular
diagonals, the altitude from their intersection to one side passes through
the midpoint of the opposite side. -/
theorem exercise_16_5 [DecidableEq K]
    (circle : Conic K) (center : Point K) (circleQuadrance : K)
    (presentation : circle.IsCirclePresentation center circleQuadrance)
    (first second third fourth intersection : Point K)
    (twoNonzero : (2 : K) ≠ 0)
    (distinct :
      first ≠ second ∧ first ≠ third ∧ first ≠ fourth ∧
        second ≠ third ∧ second ≠ fourth ∧ third ≠ fourth)
    (firstOnCircle : circle.Contains first)
    (secondOnCircle : circle.Contains second)
    (thirdOnCircle : circle.Contains third)
    (fourthOnCircle : circle.Contains fourth)
    (intersectionOnFirstThird :
      (lineThrough first third distinct.2.1).Contains intersection)
    (intersectionOnSecondFourth :
      (lineThrough second fourth distinct.2.2.2.2.1).Contains intersection)
    (diagonalsPerpendicular :
      (lineThrough first third distinct.2.1).Perpendicular
        (lineThrough second fourth distinct.2.2.2.2.1)) :
    (altitudeThrough intersection
      (lineThrough first fourth distinct.2.2.1)).Contains
        (midpoint second third) := by
  rcases thalesPoint_exists_of_on_line first third intersection
      distinct.2.1 intersectionOnFirstThird with
    ⟨firstScale, firstParameter⟩
  rcases thalesPoint_exists_of_on_line second fourth intersection
      distinct.2.2.2.2.1 intersectionOnSecondFourth with
    ⟨secondScale, secondParameter⟩
  have parameterPointsEqual :
      thalesPoint firstScale first third =
        thalesPoint secondScale second fourth :=
    firstParameter.trans secondParameter.symm
  have firstPower := thalesPoint_circle_power_of_circle circle center first
    third circleQuadrance firstScale presentation firstOnCircle thirdOnCircle
  have secondPower := thalesPoint_circle_power_of_circle circle center second
    fourth circleQuadrance secondScale presentation secondOnCircle fourthOnCircle
  have negativeProductsEqual :
      -(firstScale * (1 - firstScale) * quadrance first third) =
        -(secondScale * (1 - secondScale) * quadrance second fourth) := by
    calc
      -(firstScale * (1 - firstScale) * quadrance first third) =
          quadrance (thalesPoint firstScale first third) center -
            circleQuadrance := firstPower.symm
      _ = quadrance (thalesPoint secondScale second fourth) center -
          circleQuadrance := by rw [parameterPointsEqual]
      _ = -(secondScale * (1 - secondScale) *
          quadrance second fourth) := secondPower
  have signedProductsEqual :
      firstScale * (1 - firstScale) * quadrance first third =
        secondScale * (1 - secondScale) * quadrance second fourth := by
    calc
      firstScale * (1 - firstScale) * quadrance first third =
          -(-(firstScale * (1 - firstScale) * quadrance first third)) := by ring1
      _ = -(-(secondScale * (1 - secondScale) *
          quadrance second fourth)) := by rw [negativeProductsEqual]
      _ = secondScale * (1 - secondScale) *
          quadrance second fourth := by ring1
  let directionDot :=
    (third.x - first.x) * (fourth.x - second.x) +
      (third.y - first.y) * (fourth.y - second.y)
  have directionDotZero : directionDot = 0 := by
    unfold Line.Perpendicular at diagonalsPerpendicular
    change
      (first.y - third.y) * (second.y - fourth.y) +
        (third.x - first.x) * (fourth.x - second.x) = 0
      at diagonalsPerpendicular
    calc
      directionDot =
          (first.y - third.y) * (second.y - fourth.y) +
            (third.x - first.x) * (fourth.x - second.x) := by
        unfold directionDot
        ring1
      _ = 0 := diagonalsPerpendicular
  have thirdMinusIntersectionX :
      third.x - intersection.x =
        (1 - firstScale) * (third.x - first.x) := by
    rw [← congrArg Point.x firstParameter]
    unfold thalesPoint affineCombination
    ring1
  have thirdMinusIntersectionY :
      third.y - intersection.y =
        (1 - firstScale) * (third.y - first.y) := by
    rw [← congrArg Point.y firstParameter]
    unfold thalesPoint affineCombination
    ring1
  have secondMinusIntersectionX :
      second.x - intersection.x =
        -secondScale * (fourth.x - second.x) := by
    rw [← congrArg Point.x secondParameter]
    unfold thalesPoint affineCombination
    ring1
  have secondMinusIntersectionY :
      second.y - intersection.y =
        -secondScale * (fourth.y - second.y) := by
    rw [← congrArg Point.y secondParameter]
    unfold thalesPoint affineCombination
    ring1
  have intersectionMinusFirstX :
      intersection.x - first.x =
        firstScale * (third.x - first.x) := by
    rw [← congrArg Point.x firstParameter]
    unfold thalesPoint affineCombination
    ring1
  have intersectionMinusFirstY :
      intersection.y - first.y =
        firstScale * (third.y - first.y) := by
    rw [← congrArg Point.y firstParameter]
    unfold thalesPoint affineCombination
    ring1
  have fourthMinusIntersectionX :
      fourth.x - intersection.x =
        (1 - secondScale) * (fourth.x - second.x) := by
    rw [← congrArg Point.x secondParameter]
    unfold thalesPoint affineCombination
    ring1
  have fourthMinusIntersectionY :
      fourth.y - intersection.y =
        (1 - secondScale) * (fourth.y - second.y) := by
    rw [← congrArg Point.y secondParameter]
    unfold thalesPoint affineCombination
    ring1
  have fourthMinusFirstX :
      fourth.x - first.x =
        firstScale * (third.x - first.x) +
          (1 - secondScale) * (fourth.x - second.x) := by
    calc
      fourth.x - first.x =
          (fourth.x - intersection.x) +
            (intersection.x - first.x) := by ring1
      _ = firstScale * (third.x - first.x) +
          (1 - secondScale) * (fourth.x - second.x) := by
        rw [fourthMinusIntersectionX, intersectionMinusFirstX]
        ring1
  have fourthMinusFirstY :
      fourth.y - first.y =
        firstScale * (third.y - first.y) +
          (1 - secondScale) * (fourth.y - second.y) := by
    calc
      fourth.y - first.y =
          (fourth.y - intersection.y) +
            (intersection.y - first.y) := by ring1
      _ = firstScale * (third.y - first.y) +
          (1 - secondScale) * (fourth.y - second.y) := by
        rw [fourthMinusIntersectionY, intersectionMinusFirstY]
        ring1
  have twiceMidpointX :
      2 * (midpoint second third).x = second.x + third.x := by
    change 2 * ((second.x + third.x) / 2) = second.x + third.x
    calc
      2 * ((second.x + third.x) / 2) =
          ((second.x + third.x) / 2) * 2 := by ring1
      _ = second.x + third.x :=
        RFAP.ExplicitField.div_mul_cancel (second.x + third.x) twoNonzero
  have twiceMidpointY :
      2 * (midpoint second third).y = second.y + third.y := by
    change 2 * ((second.y + third.y) / 2) = second.y + third.y
    calc
      2 * ((second.y + third.y) / 2) =
          ((second.y + third.y) / 2) * 2 := by ring1
      _ = second.y + third.y :=
        RFAP.ExplicitField.div_mul_cancel (second.y + third.y) twoNonzero
  have twiceMidpointOffsetX :
      2 * ((midpoint second third).x - intersection.x) =
        (1 - firstScale) * (third.x - first.x) -
          secondScale * (fourth.x - second.x) := by
    calc
      2 * ((midpoint second third).x - intersection.x) =
          2 * (midpoint second third).x - 2 * intersection.x := by ring1
      _ = (second.x + third.x) - 2 * intersection.x := by
        rw [twiceMidpointX]
      _ = (second.x - intersection.x) +
          (third.x - intersection.x) := by ring1
      _ = (1 - firstScale) * (third.x - first.x) -
          secondScale * (fourth.x - second.x) := by
        rw [secondMinusIntersectionX, thirdMinusIntersectionX]
        ring1
  have twiceMidpointOffsetY :
      2 * ((midpoint second third).y - intersection.y) =
        (1 - firstScale) * (third.y - first.y) -
          secondScale * (fourth.y - second.y) := by
    calc
      2 * ((midpoint second third).y - intersection.y) =
          2 * (midpoint second third).y - 2 * intersection.y := by ring1
      _ = (second.y + third.y) - 2 * intersection.y := by
        rw [twiceMidpointY]
      _ = (second.y - intersection.y) +
          (third.y - intersection.y) := by ring1
      _ = (1 - firstScale) * (third.y - first.y) -
          secondScale * (fourth.y - second.y) := by
        rw [secondMinusIntersectionY, thirdMinusIntersectionY]
        ring1
  let midpointDirectionDot :=
    ((midpoint second third).x - intersection.x) *
        (fourth.x - first.x) +
      ((midpoint second third).y - intersection.y) *
        (fourth.y - first.y)
  have twiceMidpointDirectionDot : 2 * midpointDirectionDot = 0 := by
    calc
      2 * midpointDirectionDot =
          (2 * ((midpoint second third).x - intersection.x)) *
              (fourth.x - first.x) +
            (2 * ((midpoint second third).y - intersection.y)) *
              (fourth.y - first.y) := by
        unfold midpointDirectionDot
        ring1
      _ = ((1 - firstScale) * (third.x - first.x) -
              secondScale * (fourth.x - second.x)) *
              (fourth.x - first.x) +
            ((1 - firstScale) * (third.y - first.y) -
              secondScale * (fourth.y - second.y)) *
              (fourth.y - first.y) := by
        rw [twiceMidpointOffsetX, twiceMidpointOffsetY]
      _ = firstScale * (1 - firstScale) * quadrance first third -
            secondScale * (1 - secondScale) *
              quadrance second fourth +
            (1 - firstScale - secondScale) * directionDot := by
        rw [fourthMinusFirstX, fourthMinusFirstY]
        unfold directionDot quadrance
        ring1
      _ = 0 := by
        rw [signedProductsEqual, directionDotZero]
        ring1
  have midpointDirectionDotZero : midpointDirectionDot = 0 := by
    by_cases dotZero : midpointDirectionDot = 0
    · exact dotZero
    · exact False.elim
        ((RFAP.ExplicitField.mul_ne_zero twoNonzero dotZero)
          twiceMidpointDirectionDot)
  unfold altitudeThrough Line.Contains lineThrough
  calc
    -(fourth.x - first.x) * (midpoint second third).x +
          (first.y - fourth.y) * (midpoint second third).y +
          ((fourth.x - first.x) * intersection.x -
            (first.y - fourth.y) * intersection.y) =
        -midpointDirectionDot := by
      unfold midpointDirectionDot
      ring1
    _ = 0 := by rw [midpointDirectionDotZero]; ring1

end Conic

end DivineProportions
