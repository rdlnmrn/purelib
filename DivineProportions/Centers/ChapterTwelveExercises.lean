import DivineProportions.Centers.Inquadrance
import DivineProportions.Triangles.IsoscelesMedian

/-!
# Divine Proportions, remaining Chapter 12 exercises

This module completes the reader exercises: the finite chord argument from
Exercise 12.1, the null-side circumcenter argument from Exercise 12.4, and the
remaining exact polynomial and spread calculations.
-/

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K]

/-- The finite one-chord argument used twice in Exercise 12.1.  The midpoint
line from an equal-quadrance center is perpendicular to the chord.  The
right-triangle Spread ratio and the cleared Extended-spread identity identify
the two center spreads with the spread at the opposite vertex; Complementary
spreads then gives the spread at the chord endpoint. -/
theorem exercise_12_1
    [Nontrivial K] [DecidableEq K]
    (opposite left right center : Point K)
    (rightLeftDistinct : right ≠ left)
    (oppositeLeftDistinct : opposite ≠ left)
    (oppositeRightDistinct : opposite ≠ right)
    (centerRightDistinct : center ≠ right)
    (centerLeftDistinct : center ≠ left)
    (centerMidpointDistinct : center ≠ midpoint right left)
    (rightMidpointDistinct : right ≠ midpoint right left)
    (oppositeLeftNonNull :
      ¬ (lineThrough opposite left oppositeLeftDistinct).IsNull)
    (oppositeRightNonNull :
      ¬ (lineThrough opposite right oppositeRightDistinct).IsNull)
    (chordNonNull :
      ¬ (lineThrough right left rightLeftDistinct).IsNull)
    (centerRightNonNull :
      ¬ (lineThrough center right centerRightDistinct).IsNull)
    (centerLeftNonNull :
      ¬ (lineThrough center left centerLeftDistinct).IsNull)
    (centerMidpointNonNull :
      ¬ (lineThrough center (midpoint right left)
        centerMidpointDistinct).IsNull)
    (twoNonzero : (2 : K) ≠ 0)
    (equalRadii : quadrance center right = quadrance center left)
    (medianPerpendicularChord :
      (lineThrough center (midpoint right left)
        centerMidpointDistinct).Perpendicular
          (lineThrough right left rightLeftDistinct))
    (sourceSpread : K)
    (sourceSpreadValue :
      spread (lineThrough opposite left oppositeLeftDistinct)
          (lineThrough opposite right oppositeRightDistinct)
          oppositeLeftNonNull oppositeRightNonNull = sourceSpread)
    (extendedChord :
      sourceSpread * (4 * quadrance center right) = quadrance left right) :
    let rightCenterNonNull :
        ¬ (lineThrough right center centerRightDistinct.symm).IsNull := by
      intro reversedNull
      apply centerRightNonNull
      apply (null_line_iff_quadrance_zero center right
        centerRightDistinct).2
      calc
        quadrance center right = quadrance right center :=
          quadrance_symm center right
        _ = 0 := (null_line_iff_quadrance_zero right center
          centerRightDistinct.symm).1 reversedNull
    spread (lineThrough opposite left oppositeLeftDistinct)
          (lineThrough opposite right oppositeRightDistinct)
          oppositeLeftNonNull oppositeRightNonNull = sourceSpread ∧
      spread (lineThrough right center centerRightDistinct.symm)
          (lineThrough right left rightLeftDistinct)
          rightCenterNonNull chordNonNull = 1 - sourceSpread ∧
      spread (lineThrough center right centerRightDistinct)
          (lineThrough center (midpoint right left) centerMidpointDistinct)
          centerRightNonNull centerMidpointNonNull = sourceSpread ∧
      spread (lineThrough center left centerLeftDistinct)
          (lineThrough center (midpoint right left) centerMidpointDistinct)
          centerLeftNonNull centerMidpointNonNull = sourceSpread := by
  dsimp only
  let chord := lineThrough right left rightLeftDistinct
  let median := lineThrough center (midpoint right left)
    centerMidpointDistinct
  let centerRight := lineThrough center right centerRightDistinct
  let centerLeft := lineThrough center left centerLeftDistinct
  let rightCenter := lineThrough right center centerRightDistinct.symm
  let rightMidpoint := lineThrough right (midpoint right left)
    rightMidpointDistinct
  have rightMidpointParallelChord : rightMidpoint.Parallel chord := by
    apply lineThrough_parallel_of_contains chord right (midpoint right left)
      rightMidpointDistinct
    · exact lineThrough_contains_first right left rightLeftDistinct
    · exact midpoint_on_line right left rightLeftDistinct twoNonzero
  have medianPerpendicularRightMidpoint :
      median.Perpendicular rightMidpoint := by
    apply Line.perpendicular_symm
    exact perpendicular_of_parallel_left chord rightMidpoint median
      (Line.parallel_symm rightMidpointParallelChord)
      (Line.perpendicular_symm medianPerpendicularChord)
  have centerSpreadRatio :
      spread centerRight median centerRightNonNull centerMidpointNonNull =
        quadrance right (midpoint right left) /
          quadrance center right := by
    exact spread_ratio center right (midpoint right left)
      centerRightDistinct centerMidpointDistinct rightMidpointDistinct
      centerRightNonNull centerMidpointNonNull twoNonzero
      medianPerpendicularRightMidpoint
  have midpointQuadrance :
      quadrance right (midpoint right left) = quadrance left right / 4 := by
    calc
      quadrance right (midpoint right left) =
          quadrance (midpoint right left) right :=
        quadrance_symm right (midpoint right left)
      _ = quadrance right left / 4 :=
        midpoint_quadrance right left twoNonzero
      _ = quadrance left right / 4 := by
        rw [quadrance_symm right left]
  have fourNonzero : (4 : K) ≠ 0 := by
    have squareNonzero :=
      RFAP.ExplicitField.mul_ne_zero twoNonzero twoNonzero
    simpa only [show (4 : K) = 2 * 2 by ring1] using squareNonzero
  have quarterChord :
      quadrance left right / 4 =
        sourceSpread * quadrance center right := by
    have productsEqual :
        (quadrance left right / 4) * 4 =
          (sourceSpread * quadrance center right) * 4 := by
      calc
        (quadrance left right / 4) * 4 = quadrance left right :=
          RFAP.ExplicitField.div_mul_cancel _ fourNonzero
        _ = sourceSpread * (4 * quadrance center right) :=
          extendedChord.symm
        _ = (sourceSpread * quadrance center right) * 4 := by ring1
    have fourCancel : (4 : K) * (4 : K)⁻¹ = 1 :=
      RFAP.ExplicitField.mul_inv_cancel 4 fourNonzero
    calc
      quadrance left right / 4 =
          ((quadrance left right / 4) * 4) * (4 : K)⁻¹ := by
        simp only [RFAP.ExplicitField.div_eq_mul_inv]
        rw [mul_assoc, fourCancel, mul_one]
      _ = ((sourceSpread * quadrance center right) * 4) *
          (4 : K)⁻¹ := by rw [productsEqual]
      _ = sourceSpread * quadrance center right := by
        rw [mul_assoc, fourCancel, mul_one]
  have centerRadiusNonzero : quadrance center right ≠ 0 := by
    intro radiusZero
    apply centerRightNonNull
    exact (null_line_iff_quadrance_zero center right
      centerRightDistinct).2 radiusZero
  have centerSpreadTimesRadius :
      spread centerRight median centerRightNonNull centerMidpointNonNull *
          quadrance center right =
        sourceSpread * quadrance center right := by
    calc
      spread centerRight median centerRightNonNull centerMidpointNonNull *
            quadrance center right =
          (quadrance right (midpoint right left) /
              quadrance center right) * quadrance center right := by
        rw [centerSpreadRatio]
      _ = quadrance right (midpoint right left) :=
        RFAP.ExplicitField.div_mul_cancel _ centerRadiusNonzero
      _ = quadrance left right / 4 := midpointQuadrance
      _ = sourceSpread * quadrance center right := quarterChord
  have radiusCancel :
      quadrance center right * (quadrance center right)⁻¹ = 1 :=
    RFAP.ExplicitField.mul_inv_cancel _ centerRadiusNonzero
  have centerSpreadValue :
      spread centerRight median centerRightNonNull centerMidpointNonNull =
        sourceSpread := by
    calc
      spread centerRight median centerRightNonNull centerMidpointNonNull =
          (spread centerRight median centerRightNonNull
              centerMidpointNonNull * quadrance center right) *
            (quadrance center right)⁻¹ := by
        rw [mul_assoc, radiusCancel, mul_one]
      _ = (sourceSpread * quadrance center right) *
          (quadrance center right)⁻¹ := by
        rw [centerSpreadTimesRadius]
      _ = sourceSpread := by rw [mul_assoc, radiusCancel, mul_one]
  have centerSpreadEquality :=
    isosceles_midpoint_equal_spreads right left center
      centerRightDistinct centerLeftDistinct centerMidpointDistinct
      centerRightNonNull centerLeftNonNull centerMidpointNonNull
      twoNonzero equalRadii
  have centerLeftSpreadValue :
      spread centerLeft median centerLeftNonNull centerMidpointNonNull =
        sourceSpread := centerSpreadEquality.symm.trans centerSpreadValue
  have rightCenterNonNull : ¬ rightCenter.IsNull := by
    intro reversedNull
    apply centerRightNonNull
    apply (null_line_iff_quadrance_zero center right
      centerRightDistinct).2
    calc
      quadrance center right = quadrance right center :=
        quadrance_symm center right
      _ = 0 := (null_line_iff_quadrance_zero right center
        centerRightDistinct.symm).1 reversedNull
  have centerRightParallelReverse : centerRight.Parallel rightCenter := by
    unfold centerRight rightCenter Line.Parallel lineThrough
    ring1
  have centerSpreadReverse :
      spread centerRight median centerRightNonNull centerMidpointNonNull =
        spread rightCenter median rightCenterNonNull centerMidpointNonNull := by
    exact spread_eq_of_parallel_pairs centerRight median rightCenter median
      centerRightNonNull centerMidpointNonNull rightCenterNonNull
      centerMidpointNonNull centerRightParallelReverse
      (Line.parallel_refl median)
  have medianReverseSpreadValue :
      spread median rightCenter centerMidpointNonNull rightCenterNonNull =
        sourceSpread := by
    calc
      spread median rightCenter centerMidpointNonNull rightCenterNonNull =
          spread rightCenter median rightCenterNonNull
            centerMidpointNonNull :=
        spread_symm median rightCenter centerMidpointNonNull
          rightCenterNonNull
      _ = spread centerRight median centerRightNonNull
          centerMidpointNonNull := centerSpreadReverse.symm
      _ = sourceSpread := centerSpreadValue
  have complementary := complementary_spreads median chord rightCenter
    centerMidpointNonNull chordNonNull rightCenterNonNull
    medianPerpendicularChord
  have rightComplement :
      spread rightCenter chord rightCenterNonNull chordNonNull =
        1 - sourceSpread := by
    calc
      spread rightCenter chord rightCenterNonNull chordNonNull =
          spread chord rightCenter chordNonNull rightCenterNonNull :=
        spread_symm rightCenter chord rightCenterNonNull chordNonNull
      _ = (spread chord rightCenter chordNonNull rightCenterNonNull +
            spread median rightCenter centerMidpointNonNull
              rightCenterNonNull) -
          spread median rightCenter centerMidpointNonNull
            rightCenterNonNull := by ring1
      _ = 1 - spread median rightCenter centerMidpointNonNull
          rightCenterNonNull := by rw [complementary]
      _ = 1 - sourceSpread := by rw [medianReverseSpreadValue]
  exact ⟨sourceSpreadValue, rightComplement, centerSpreadValue,
    centerLeftSpreadValue⟩

/-- The finite metric core of Exercise 12.4.  A point equidistant from the
ends of a null segment lies on that segment's line. -/
theorem equal_quadrance_center_collinear_of_null
    [Nontrivial K] [DecidableEq K]
    (first second center : Point K) (twoNonzero : (2 : K) ≠ 0)
    (sideNull : quadrance first second = 0)
    (equalRadii : quadrance center first = quadrance center second) :
    Collinear first second center := by
  let directionX := second.x - first.x
  let directionY := second.y - first.y
  let centerX := center.x - first.x
  let centerY := center.y - first.y
  have directionNull : directionX ^ 2 + directionY ^ 2 = 0 := by
    exact sideNull
  have twiceDot :
      2 * (directionX * centerX + directionY * centerY) = 0 := by
    calc
      2 * (directionX * centerX + directionY * centerY) =
          quadrance center first - quadrance center second +
            quadrance first second := by
        unfold quadrance directionX directionY centerX centerY
        ring1
      _ = 0 := by rw [equalRadii, sideNull]; ring1
  have dotZero : directionX * centerX + directionY * centerY = 0 := by
    by_cases zero : directionX * centerX + directionY * centerY = 0
    · exact zero
    · exact False.elim
        ((RFAP.ExplicitField.mul_ne_zero twoNonzero zero) twiceDot)
  have determinantSquareZero :
      pointDeterminant first second center ^ 2 = 0 := by
    calc
      pointDeterminant first second center ^ 2 =
          (directionX * centerY - directionY * centerX) ^ 2 := by
        unfold pointDeterminant directionX directionY centerX centerY
        ring1
      _ = (directionX ^ 2 + directionY ^ 2) *
            (centerX ^ 2 + centerY ^ 2) -
          (directionX * centerX + directionY * centerY) ^ 2 := by
        ring1
      _ = 0 := by rw [directionNull, dotZero]; ring1
  have determinantZero : pointDeterminant first second center = 0 := by
    by_cases zero : pointDeterminant first second center = 0
    · exact zero
    · have squareNonzero := RFAP.ExplicitField.mul_ne_zero zero zero
      apply False.elim
      apply squareNonzero
      calc
        pointDeterminant first second center *
            pointDeterminant first second center =
          pointDeterminant first second center ^ 2 := by ring1
        _ = 0 := determinantSquareZero
  exact (collinear_iff_pointDeterminant_eq_zero first second center).2
    determinantZero

/-- Exercise 12.4, first clause: the constructed circumcenter lies on every
null side. -/
theorem exercise_12_4_first
    [Nontrivial K] [DecidableEq K]
    (first second third : Point K)
    (firstSecondDistinct : first ≠ second)
    (firstThirdDistinct : first ≠ third)
    (secondThirdDistinct : second ≠ third)
    (notCollinear : ¬ Collinear first second third)
    (twoNonzero : (2 : K) ≠ 0)
    (secondThirdNull :
      (lineThrough second third secondThirdDistinct).IsNull) :
    Collinear second third
      (circumcenterPoint first second third firstThirdDistinct
        secondThirdDistinct notCollinear) := by
  have centerData := circumcenter first second third firstSecondDistinct
    firstThirdDistinct secondThirdDistinct notCollinear twoNonzero
  have sideQuadranceZero :=
    (null_line_iff_quadrance_zero second third secondThirdDistinct).1
      secondThirdNull
  exact equal_quadrance_center_collinear_of_null second third
    (circumcenterPoint first second third firstThirdDistinct
      secondThirdDistinct notCollinear)
    twoNonzero sideQuadranceZero centerData.2.2.2.2

/-- Two independent null sides force the circumcenter to be their common
vertex, completing Exercise 12.4. -/
theorem exercise_12_4_second
    [Nontrivial K] [DecidableEq K]
    (first second third : Point K)
    (firstSecondDistinct : first ≠ second)
    (firstThirdDistinct : first ≠ third)
    (secondThirdDistinct : second ≠ third)
    (notCollinear : ¬ Collinear first second third)
    (twoNonzero : (2 : K) ≠ 0)
    (firstThirdNull :
      (lineThrough first third firstThirdDistinct).IsNull)
    (secondThirdNull :
      (lineThrough second third secondThirdDistinct).IsNull) :
    circumcenterPoint first second third firstThirdDistinct
      secondThirdDistinct notCollinear = third := by
  let center := circumcenterPoint first second third firstThirdDistinct
    secondThirdDistinct notCollinear
  have centerData := circumcenter first second third firstSecondDistinct
    firstThirdDistinct secondThirdDistinct notCollinear twoNonzero
  have firstThirdQuadranceZero :=
    (null_line_iff_quadrance_zero first third firstThirdDistinct).1
      firstThirdNull
  have secondThirdQuadranceZero :=
    (null_line_iff_quadrance_zero second third secondThirdDistinct).1
      secondThirdNull
  have equalFirstThird : quadrance center first = quadrance center third :=
    centerData.2.2.2.1.trans centerData.2.2.2.2
  have firstCollinear : Collinear first third center :=
    equal_quadrance_center_collinear_of_null first third center twoNonzero
      firstThirdQuadranceZero equalFirstThird
  have secondCollinear : Collinear second third center :=
    equal_quadrance_center_collinear_of_null second third center twoNonzero
      secondThirdQuadranceZero centerData.2.2.2.2
  have firstDeterminantZero : pointDeterminant first third center = 0 :=
    (collinear_iff_pointDeterminant_eq_zero first third center).1
      firstCollinear
  have secondDeterminantZero : pointDeterminant second third center = 0 :=
    (collinear_iff_pointDeterminant_eq_zero second third center).1
      secondCollinear
  have triangleDeterminantNonzero :
      pointDeterminant first second third ≠ 0 := by
    intro determinantZero
    apply notCollinear
    exact (collinear_iff_pointDeterminant_eq_zero first second third).2
      determinantZero
  have xProductZero :
      pointDeterminant first second third * (center.x - third.x) = 0 := by
    calc
      pointDeterminant first second third * (center.x - third.x) =
          (first.x - third.x) *
              pointDeterminant second third center -
            (second.x - third.x) *
              pointDeterminant first third center := by
        unfold pointDeterminant
        ring1
      _ = 0 := by
        rw [firstDeterminantZero, secondDeterminantZero]
        ring1
  have yProductZero :
      pointDeterminant first second third * (center.y - third.y) = 0 := by
    calc
      pointDeterminant first second third * (center.y - third.y) =
          (first.y - third.y) *
              pointDeterminant second third center -
            (second.y - third.y) *
              pointDeterminant first third center := by
        unfold pointDeterminant
        ring1
      _ = 0 := by
        rw [firstDeterminantZero, secondDeterminantZero]
        ring1
  have xDifferenceZero : center.x - third.x = 0 := by
    by_cases zero : center.x - third.x = 0
    · exact zero
    · exact False.elim
        ((RFAP.ExplicitField.mul_ne_zero triangleDeterminantNonzero zero)
          xProductZero)
  have yDifferenceZero : center.y - third.y = 0 := by
    by_cases zero : center.y - third.y = 0
    · exact zero
    · exact False.elim
        ((RFAP.ExplicitField.mul_ne_zero triangleDeterminantNonzero zero)
          yProductZero)
  apply Point.ext
  · exact sub_eq_zero.mp xDifferenceZero
  · exact sub_eq_zero.mp yDifferenceZero

/-- Exercise 12.5's displayed polynomial identity. -/
theorem exercise_12_5_identity (x₁ x₂ x₃ : K) :
    ((x₁ + x₂ + x₃) ^ 2 - 2 * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2)) *
          (x₁ + x₂ + x₃) - 8 * x₁ * x₂ * x₃ =
      (x₁ + x₂ - x₃) * (x₂ + x₃ - x₁) * (x₃ + x₁ - x₂) := by
  ring1

/-- The scalar deduction in Exercise 12.5.  The nonzero quadrea is the exact
finite substitute for cancelling the source's triangle area. -/
theorem exercise_12_5_right_iff_sum_eq_eight_circumquadrance
    [DecidableEq K]
    (q₁ q₂ q₃ area circumquadranceValue : K)
    (areaEquation : area = archimedesFunction q₁ q₂ q₃)
    (areaNonzero : area ≠ 0)
    (circumRelation : area * circumquadranceValue = q₁ * q₂ * q₃) :
    q₁ + q₂ + q₃ = 8 * circumquadranceValue ↔
      q₁ + q₂ = q₃ ∨ q₂ + q₃ = q₁ ∨ q₃ + q₁ = q₂ := by
  have factorIdentity :
      area * (q₁ + q₂ + q₃) - 8 * q₁ * q₂ * q₃ =
        (q₁ + q₂ - q₃) * (q₂ + q₃ - q₁) * (q₃ + q₁ - q₂) := by
    rw [areaEquation]
    unfold archimedesFunction
    exact exercise_12_5_identity q₁ q₂ q₃
  constructor
  · intro sumEquation
    have factorsZero :
        (q₁ + q₂ - q₃) * (q₂ + q₃ - q₁) *
            (q₃ + q₁ - q₂) = 0 := by
      calc
        (q₁ + q₂ - q₃) * (q₂ + q₃ - q₁) *
              (q₃ + q₁ - q₂) =
            area * (q₁ + q₂ + q₃) - 8 * q₁ * q₂ * q₃ :=
          factorIdentity.symm
        _ = area * (8 * circumquadranceValue) -
              8 * q₁ * q₂ * q₃ := by rw [sumEquation]
        _ = 8 *
              (area * circumquadranceValue - q₁ * q₂ * q₃) := by
          ring1
        _ = 0 := by rw [circumRelation]; ring1
    by_cases firstZero : q₁ + q₂ - q₃ = 0
    · exact Or.inl (sub_eq_zero.mp firstZero)
    · by_cases secondZero : q₂ + q₃ - q₁ = 0
      · exact Or.inr (Or.inl (sub_eq_zero.mp secondZero))
      · right
        right
        apply sub_eq_zero.mp
        by_cases thirdZero : q₃ + q₁ - q₂ = 0
        · exact thirdZero
        · exact False.elim
            ((RFAP.ExplicitField.mul_ne_zero
              (RFAP.ExplicitField.mul_ne_zero firstZero secondZero)
              thirdZero) factorsZero)
  · intro rightRelation
    have factorsZero :
        (q₁ + q₂ - q₃) * (q₂ + q₃ - q₁) *
            (q₃ + q₁ - q₂) = 0 := by
      rcases rightRelation with firstRight | secondRight | thirdRight
      · rw [firstRight]
        ring1
      · rw [secondRight]
        ring1
      · rw [thirdRight]
        ring1
    have areaTimesDifference :
        area * (q₁ + q₂ + q₃ - 8 * circumquadranceValue) = 0 := by
      calc
        area * (q₁ + q₂ + q₃ - 8 * circumquadranceValue) =
            area * (q₁ + q₂ + q₃) -
              8 * (area * circumquadranceValue) := by ring1
        _ = area * (q₁ + q₂ + q₃) - 8 * q₁ * q₂ * q₃ := by
          rw [circumRelation]
          ring1
        _ = (q₁ + q₂ - q₃) * (q₂ + q₃ - q₁) *
              (q₃ + q₁ - q₂) := factorIdentity
        _ = 0 := factorsZero
    apply sub_eq_zero.mp
    by_cases differenceZero :
        q₁ + q₂ + q₃ - 8 * circumquadranceValue = 0
    · exact differenceZero
    · exact False.elim
        ((RFAP.ExplicitField.mul_ne_zero areaNonzero differenceZero)
          areaTimesDifference)

/-- Two distinct roots of the same Triple-spread quadratic have the displayed
sum.  This is the finite “other root” calculation used in Exercise 12.7. -/
theorem alternate_spread_root_sum
    [DecidableEq K]
    (firstRoot secondRoot fixedFirst fixedSecond : K)
    (firstTriple : SpreadTriple firstRoot fixedFirst fixedSecond)
    (secondTriple : SpreadTriple secondRoot fixedFirst fixedSecond)
    (rootsDistinct : secondRoot ≠ firstRoot) :
    secondRoot + firstRoot =
      2 * (fixedFirst + fixedSecond - 2 * fixedFirst * fixedSecond) := by
  have differenceNonzero : secondRoot - firstRoot ≠ 0 := by
    intro differenceZero
    apply rootsDistinct
    exact sub_eq_zero.mp differenceZero
  have productZero :
      (secondRoot - firstRoot) *
        (secondRoot + firstRoot -
          2 * (fixedFirst + fixedSecond -
            2 * fixedFirst * fixedSecond)) = 0 := by
    calc
      (secondRoot - firstRoot) *
          (secondRoot + firstRoot -
            2 * (fixedFirst + fixedSecond -
              2 * fixedFirst * fixedSecond)) =
        -(tripleSpreadFunction secondRoot fixedFirst fixedSecond -
          tripleSpreadFunction firstRoot fixedFirst fixedSecond) := by
            unfold tripleSpreadFunction
            ring1
      _ = 0 := by
        unfold SpreadTriple at firstTriple secondTriple
        rw [firstTriple, secondTriple]
        ring1
  apply sub_eq_zero.mp
  by_cases sumDifferenceZero :
      secondRoot + firstRoot -
        2 * (fixedFirst + fixedSecond -
          2 * fixedFirst * fixedSecond) = 0
  · exact sumDifferenceZero
  · exact False.elim
      ((RFAP.ExplicitField.mul_ne_zero differenceNonzero sumDifferenceZero)
        productZero)

/-- Exercise 12.7.  The two Triple-spread certificates say that `u₁` and
`r₁` are the two branches obtained from the same other two line spreads; the
explicit inequality selects the other branch. -/
theorem exercise_12_7
    [DecidableEq K]
    (u₁ u₂ u₃ r₁ : K) (twoNonzero : (2 : K) ≠ 0)
    (firstTriple : SpreadTriple u₁ u₂ (1 - u₃))
    (secondTriple : SpreadTriple r₁ u₂ (1 - u₃))
    (otherBranch : r₁ ≠ u₁)
    (firstNotHalf : u₁ ≠ (1 : K) / 2) :
    r₁ =
      (u₁ - 2 * u₂ - 2 * u₃ + 2 * u₂ ^ 2 + 2 * u₃ ^ 2) /
        (2 * u₁ - 1) := by
  have rootSum := alternate_spread_root_sum u₁ r₁ u₂ (1 - u₃)
    firstTriple secondTriple otherBranch
  have rootEquation :
      r₁ = 2 * (u₂ + (1 - u₃) - 2 * u₂ * (1 - u₃)) - u₁ := by
    calc
      r₁ = (r₁ + u₁) - u₁ := by ring1
      _ = 2 * (u₂ + (1 - u₃) - 2 * u₂ * (1 - u₃)) - u₁ := by
        rw [rootSum]
  have denominatorNonzero : 2 * u₁ - 1 ≠ 0 := by
    intro denominatorZero
    apply firstNotHalf
    have twiceFirst : 2 * u₁ = 1 := sub_eq_zero.mp denominatorZero
    have twoCancel : (2 : K) * (2 : K)⁻¹ = 1 :=
      RFAP.ExplicitField.mul_inv_cancel 2 twoNonzero
    simp only [RFAP.ExplicitField.div_eq_mul_inv]
    calc
      u₁ = u₁ * 1 := by ring1
      _ = u₁ * ((2 : K) * (2 : K)⁻¹) := by rw [twoCancel]
      _ = (2 * u₁) * (2 : K)⁻¹ := by ring1
      _ = 1 * (2 : K)⁻¹ := by rw [twiceFirst]
  let numerator :=
    u₁ - 2 * u₂ - 2 * u₃ + 2 * u₂ ^ 2 + 2 * u₃ ^ 2
  have cleared : (2 * u₁ - 1) * r₁ = numerator := by
    apply sub_eq_zero.mp
    calc
      (2 * u₁ - 1) * r₁ - numerator =
          (2 * u₁ - 1) *
              (2 * (u₂ + (1 - u₃) - 2 * u₂ * (1 - u₃)) - u₁) -
            numerator := by rw [rootEquation]
      _ = 2 * tripleSpreadFunction u₁ u₂ (1 - u₃) := by
        unfold numerator tripleSpreadFunction
        ring1
      _ = 0 := by
        unfold SpreadTriple at firstTriple
        rw [firstTriple]
        ring1
  have denominatorCancel :
      (2 * u₁ - 1) * (2 * u₁ - 1)⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel _ denominatorNonzero
  unfold numerator at cleared
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  calc
    r₁ = r₁ * 1 := by ring1
    _ = r₁ * ((2 * u₁ - 1) * (2 * u₁ - 1)⁻¹) := by
      rw [denominatorCancel]
    _ = ((2 * u₁ - 1) * r₁) * (2 * u₁ - 1)⁻¹ := by ring1
    _ = (u₁ - 2 * u₂ - 2 * u₃ + 2 * u₂ ^ 2 + 2 * u₃ ^ 2) *
          (2 * u₁ - 1)⁻¹ := by rw [cleared]

/-- Exercise 12.8 in its finite scalar form.  The four inquadrance formulas
come from Theorem 90 after selecting the four finite bisector branches; the
three double-spread identities and Exercise 12.2 then make the product a
single polynomial calculation. -/
theorem exercise_12_8
    (u₁ u₂ u₃ s₁ s₂ s₃ circumquadranceValue area
      r₀ r₁ r₂ r₃ : K)
    (sixteenNonzero : (16 : K) ≠ 0)
    (firstSideSpread : s₁ = 4 * u₁ * (1 - u₁))
    (secondSideSpread : s₂ = 4 * u₂ * (1 - u₂))
    (thirdSideSpread : s₃ = 4 * u₃ * (1 - u₃))
    (areaFormula :
      area = 64 * circumquadranceValue ^ 2 * s₁ * s₂ * s₃)
    (firstInquadrance :
      r₀ = 16 * circumquadranceValue * u₁ * u₂ * u₃)
    (secondInquadrance :
      r₁ = 16 * circumquadranceValue *
        u₁ * (1 - u₂) * (1 - u₃))
    (thirdInquadrance :
      r₂ = 16 * circumquadranceValue *
        (1 - u₁) * u₂ * (1 - u₃))
    (fourthInquadrance :
      r₃ = 16 * circumquadranceValue *
        (1 - u₁) * (1 - u₂) * u₃) :
    r₀ * r₁ * r₂ * r₃ = (area / 16) ^ 2 := by
  have sixteenCancel : (16 : K) * (16 : K)⁻¹ = 1 :=
    RFAP.ExplicitField.mul_inv_cancel 16 sixteenNonzero
  have scaleCancel : (4096 : K) * (16 : K)⁻¹ = 256 := by
    calc
      (4096 : K) * (16 : K)⁻¹ =
          256 * ((16 : K) * (16 : K)⁻¹) := by ring1
      _ = 256 := by rw [sixteenCancel]; ring1
  rw [firstInquadrance, secondInquadrance, thirdInquadrance,
    fourthInquadrance, areaFormula, firstSideSpread, secondSideSpread,
    thirdSideSpread]
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  rw [show
    64 * circumquadranceValue ^ 2 *
          (4 * u₁ * (1 - u₁)) *
          (4 * u₂ * (1 - u₂)) *
          (4 * u₃ * (1 - u₃)) * (16 : K)⁻¹ =
        (4096 : K) * (16 : K)⁻¹ * circumquadranceValue ^ 2 *
          u₁ * (1 - u₁) * u₂ * (1 - u₂) * u₃ * (1 - u₃) by ring1]
  rw [scaleCancel]
  ring1

end DivineProportions
