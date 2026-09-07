import DivineProportions.Trigonometry.Quadrea

/-!
# Divine Proportions, Exercise 5.16

A triangle described by side lines has vertices `l₂l₃`, `l₃l₁`, and
`l₁l₂`.  The finite dual-determinant calculation below first proves that
the point determinant of those three explicit intersections, multiplied by
their three denominators, is the square of the line determinant.  Squaring
that identity gives the source's fourth-power quadrea formula.
-/

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K]

private theorem eq_of_mul_eq_mul_right
    {left right factor : K} (factorNonzero : factor ≠ 0)
    (productsEqual : left * factor = right * factor) : left = right := by
  have factorCancel : factor * factor⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel factor factorNonzero
  calc
    left = left * 1 := by ring1
    _ = left * (factor * factor⁻¹) := by rw [factorCancel]
    _ = (left * factor) * factor⁻¹ := by ring1
    _ = (right * factor) * factor⁻¹ := by rw [productsEqual]
    _ = right * (factor * factor⁻¹) := by ring1
    _ = right := by rw [factorCancel]; ring1

/-- The finite dual determinant underlying Exercise 5.16.  Each vertex is an
executable line intersection and each factor on the left is its displayed
nonzero denominator. -/
theorem lineTriangle_pointDeterminant_cleared
    (first second third : Line K)
    (secondThirdNonparallel : ¬ second.Parallel third)
    (thirdFirstNonparallel : ¬ third.Parallel first)
    (firstSecondNonparallel : ¬ first.Parallel second) :
    pointDeterminant
          (lineIntersection second third secondThirdNonparallel)
          (lineIntersection third first thirdFirstNonparallel)
          (lineIntersection first second firstSecondNonparallel) *
        ((second.a * third.b - third.a * second.b) *
          (third.a * first.b - first.a * third.b) *
          (first.a * second.b - second.a * first.b)) =
      lineDeterminant first second third ^ 2 := by
  let secondThirdDenominator :=
    second.a * third.b - third.a * second.b
  let thirdFirstDenominator :=
    third.a * first.b - first.a * third.b
  let firstSecondDenominator :=
    first.a * second.b - second.a * first.b
  let firstPoint :=
    lineIntersection second third secondThirdNonparallel
  let secondPoint :=
    lineIntersection third first thirdFirstNonparallel
  let thirdPoint :=
    lineIntersection first second firstSecondNonparallel
  have secondThirdDenominatorNonzero : secondThirdDenominator ≠ 0 := by
    exact secondThirdNonparallel
  have thirdFirstDenominatorNonzero : thirdFirstDenominator ≠ 0 := by
    exact thirdFirstNonparallel
  have firstSecondDenominatorNonzero : firstSecondDenominator ≠ 0 := by
    exact firstSecondNonparallel
  have firstXCancel :
      firstPoint.x * secondThirdDenominator =
        second.b * third.c - third.b * second.c := by
    dsimp only [firstPoint, lineIntersection, secondThirdDenominator]
    exact RFAP.ExplicitField.div_mul_cancel _ secondThirdDenominatorNonzero
  have firstYCancel :
      firstPoint.y * secondThirdDenominator =
        second.c * third.a - third.c * second.a := by
    dsimp only [firstPoint, lineIntersection, secondThirdDenominator]
    exact RFAP.ExplicitField.div_mul_cancel _ secondThirdDenominatorNonzero
  have secondXCancel :
      secondPoint.x * thirdFirstDenominator =
        third.b * first.c - first.b * third.c := by
    dsimp only [secondPoint, lineIntersection, thirdFirstDenominator]
    exact RFAP.ExplicitField.div_mul_cancel _ thirdFirstDenominatorNonzero
  have secondYCancel :
      secondPoint.y * thirdFirstDenominator =
        third.c * first.a - first.c * third.a := by
    dsimp only [secondPoint, lineIntersection, thirdFirstDenominator]
    exact RFAP.ExplicitField.div_mul_cancel _ thirdFirstDenominatorNonzero
  have thirdXCancel :
      thirdPoint.x * firstSecondDenominator =
        first.b * second.c - second.b * first.c := by
    dsimp only [thirdPoint, lineIntersection, firstSecondDenominator]
    exact RFAP.ExplicitField.div_mul_cancel _ firstSecondDenominatorNonzero
  have thirdYCancel :
      thirdPoint.y * firstSecondDenominator =
        first.c * second.a - second.c * first.a := by
    dsimp only [thirdPoint, lineIntersection, firstSecondDenominator]
    exact RFAP.ExplicitField.div_mul_cancel _ firstSecondDenominatorNonzero
  change
    pointDeterminant firstPoint secondPoint thirdPoint *
        (secondThirdDenominator * thirdFirstDenominator *
          firstSecondDenominator) =
      lineDeterminant first second third ^ 2
  calc
    pointDeterminant firstPoint secondPoint thirdPoint *
          (secondThirdDenominator * thirdFirstDenominator *
            firstSecondDenominator) =
        (firstPoint.x * secondThirdDenominator) *
            (secondPoint.y * thirdFirstDenominator) *
              firstSecondDenominator -
          (firstPoint.x * secondThirdDenominator) *
            (thirdPoint.y * firstSecondDenominator) *
              thirdFirstDenominator +
          (secondPoint.x * thirdFirstDenominator) *
            (thirdPoint.y * firstSecondDenominator) *
              secondThirdDenominator -
          (thirdPoint.x * firstSecondDenominator) *
            (secondPoint.y * thirdFirstDenominator) *
              secondThirdDenominator +
          (thirdPoint.x * firstSecondDenominator) *
            (firstPoint.y * secondThirdDenominator) *
              thirdFirstDenominator -
          (secondPoint.x * thirdFirstDenominator) *
            (firstPoint.y * secondThirdDenominator) *
              firstSecondDenominator := by
                unfold pointDeterminant
                ring1
    _ = (second.b * third.c - third.b * second.c) *
            (third.c * first.a - first.c * third.a) *
              firstSecondDenominator -
          (second.b * third.c - third.b * second.c) *
            (first.c * second.a - second.c * first.a) *
              thirdFirstDenominator +
          (third.b * first.c - first.b * third.c) *
            (first.c * second.a - second.c * first.a) *
              secondThirdDenominator -
          (first.b * second.c - second.b * first.c) *
            (third.c * first.a - first.c * third.a) *
              secondThirdDenominator +
          (first.b * second.c - second.b * first.c) *
            (second.c * third.a - third.c * second.a) *
              thirdFirstDenominator -
          (third.b * first.c - first.b * third.c) *
            (second.c * third.a - third.c * second.a) *
              firstSecondDenominator := by
                rw [firstXCancel, firstYCancel, secondXCancel,
                  secondYCancel, thirdXCancel, thirdYCancel]
    _ = lineDeterminant first second third ^ 2 := by
          unfold secondThirdDenominator thirdFirstDenominator
            firstSecondDenominator lineDeterminant
          ring1

/-- The denominator-cleared quadrea formula of Exercise 5.16. -/
theorem exercise_5_16_cleared
    (first second third : Line K)
    (secondThirdNonparallel : ¬ second.Parallel third)
    (thirdFirstNonparallel : ¬ third.Parallel first)
    (firstSecondNonparallel : ¬ first.Parallel second) :
    quadrea
          (lineIntersection second third secondThirdNonparallel)
          (lineIntersection third first thirdFirstNonparallel)
          (lineIntersection first second firstSecondNonparallel) *
        ((second.a * third.b - third.a * second.b) ^ 2 *
          (third.a * first.b - first.a * third.b) ^ 2 *
          (first.a * second.b - second.a * first.b) ^ 2) =
      4 * lineDeterminant first second third ^ 4 := by
  let firstPoint :=
    lineIntersection second third secondThirdNonparallel
  let secondPoint :=
    lineIntersection third first thirdFirstNonparallel
  let thirdPoint :=
    lineIntersection first second firstSecondNonparallel
  let denominatorProduct :=
    (second.a * third.b - third.a * second.b) *
      (third.a * first.b - first.a * third.b) *
      (first.a * second.b - second.a * first.b)
  have pointDeterminantCleared :=
    lineTriangle_pointDeterminant_cleared first second third
      secondThirdNonparallel thirdFirstNonparallel firstSecondNonparallel
  change
    pointDeterminant firstPoint secondPoint thirdPoint * denominatorProduct =
      lineDeterminant first second third ^ 2 at pointDeterminantCleared
  change
    quadrea firstPoint secondPoint thirdPoint *
        ((second.a * third.b - third.a * second.b) ^ 2 *
          (third.a * first.b - first.a * third.b) ^ 2 *
          (first.a * second.b - second.a * first.b) ^ 2) =
      4 * lineDeterminant first second third ^ 4
  rw [quadrea_coordinate_formula]
  calc
    4 * pointDeterminant firstPoint secondPoint thirdPoint ^ 2 *
          ((second.a * third.b - third.a * second.b) ^ 2 *
            (third.a * first.b - first.a * third.b) ^ 2 *
            (first.a * second.b - second.a * first.b) ^ 2) =
        4 * (pointDeterminant firstPoint secondPoint thirdPoint *
          denominatorProduct) ^ 2 := by
            unfold denominatorProduct
            ring1
    _ = 4 * (lineDeterminant first second third ^ 2) ^ 2 := by
          rw [pointDeterminantCleared]
    _ = 4 * lineDeterminant first second third ^ 4 := by ring1

/-- Exercise 5.16: the exact fourth-power formula for the quadrea of the
triangle whose three displayed side lines are `first`, `second`, and `third`.
-/
theorem exercise_5_16
    (first second third : Line K)
    (secondThirdNonparallel : ¬ second.Parallel third)
    (thirdFirstNonparallel : ¬ third.Parallel first)
    (firstSecondNonparallel : ¬ first.Parallel second) :
    quadrea
        (lineIntersection second third secondThirdNonparallel)
        (lineIntersection third first thirdFirstNonparallel)
        (lineIntersection first second firstSecondNonparallel) =
      (4 * lineDeterminant first second third ^ 4) /
        ((second.a * third.b - third.a * second.b) ^ 2 *
          (third.a * first.b - first.a * third.b) ^ 2 *
          (first.a * second.b - second.a * first.b) ^ 2) := by
  let secondThirdDenominator :=
    second.a * third.b - third.a * second.b
  let thirdFirstDenominator :=
    third.a * first.b - first.a * third.b
  let firstSecondDenominator :=
    first.a * second.b - second.a * first.b
  have secondThirdDenominatorNonzero : secondThirdDenominator ≠ 0 := by
    exact secondThirdNonparallel
  have thirdFirstDenominatorNonzero : thirdFirstDenominator ≠ 0 := by
    exact thirdFirstNonparallel
  have firstSecondDenominatorNonzero : firstSecondDenominator ≠ 0 := by
    exact firstSecondNonparallel
  have secondThirdSquareNonzero : secondThirdDenominator ^ 2 ≠ 0 := by
    simpa [pow_two] using
      RFAP.ExplicitField.mul_ne_zero secondThirdDenominatorNonzero
        secondThirdDenominatorNonzero
  have thirdFirstSquareNonzero : thirdFirstDenominator ^ 2 ≠ 0 := by
    simpa [pow_two] using
      RFAP.ExplicitField.mul_ne_zero thirdFirstDenominatorNonzero
        thirdFirstDenominatorNonzero
  have firstSecondSquareNonzero : firstSecondDenominator ^ 2 ≠ 0 := by
    simpa [pow_two] using
      RFAP.ExplicitField.mul_ne_zero firstSecondDenominatorNonzero
        firstSecondDenominatorNonzero
  have denominatorNonzero :
      secondThirdDenominator ^ 2 * thirdFirstDenominator ^ 2 *
          firstSecondDenominator ^ 2 ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero
      (RFAP.ExplicitField.mul_ne_zero secondThirdSquareNonzero
        thirdFirstSquareNonzero)
      firstSecondSquareNonzero
  apply eq_of_mul_eq_mul_right denominatorNonzero
  change
    quadrea
          (lineIntersection second third secondThirdNonparallel)
          (lineIntersection third first thirdFirstNonparallel)
          (lineIntersection first second firstSecondNonparallel) *
        (secondThirdDenominator ^ 2 * thirdFirstDenominator ^ 2 *
          firstSecondDenominator ^ 2) =
      ((4 * lineDeterminant first second third ^ 4) /
          (secondThirdDenominator ^ 2 * thirdFirstDenominator ^ 2 *
            firstSecondDenominator ^ 2)) *
        (secondThirdDenominator ^ 2 * thirdFirstDenominator ^ 2 *
          firstSecondDenominator ^ 2)
  calc
    quadrea
          (lineIntersection second third secondThirdNonparallel)
          (lineIntersection third first thirdFirstNonparallel)
          (lineIntersection first second firstSecondNonparallel) *
        (secondThirdDenominator ^ 2 * thirdFirstDenominator ^ 2 *
          firstSecondDenominator ^ 2) =
      4 * lineDeterminant first second third ^ 4 := by
        unfold secondThirdDenominator thirdFirstDenominator
          firstSecondDenominator
        exact exercise_5_16_cleared first second third
          secondThirdNonparallel thirdFirstNonparallel
          firstSecondNonparallel
    _ = ((4 * lineDeterminant first second third ^ 4) /
          (secondThirdDenominator ^ 2 * thirdFirstDenominator ^ 2 *
            firstSecondDenominator ^ 2)) *
        (secondThirdDenominator ^ 2 * thirdFirstDenominator ^ 2 *
          firstSecondDenominator ^ 2) :=
      (RFAP.ExplicitField.div_mul_cancel _ denominatorNonzero).symm

end DivineProportions
