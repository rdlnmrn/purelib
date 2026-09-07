import DivineProportions.Trigonometry.Quadrance

/-!
# Divine Proportions, Exercise 5.1

The quadrance between `l₁l₂` and `l₁l₃` is proved first after
clearing the two explicit line-intersection denominators.  The printed
quotient is then recovered by cancelling their nonzero squared product.  No
intersection, inverse, or projective representative is selected implicitly.
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

/-- The denominator-cleared core of Exercise 5.1.  The six-term factor is
exactly the finite coefficient determinant of the three displayed lines. -/
theorem exercise_5_1_cleared
    (first second third : Line K)
    (firstSecondNonparallel : ¬ first.Parallel second)
    (firstThirdNonparallel : ¬ first.Parallel third) :
    quadrance
          (lineIntersection first second firstSecondNonparallel)
          (lineIntersection first third firstThirdNonparallel) *
        ((first.a * second.b - second.a * first.b) ^ 2 *
          (first.a * third.b - third.a * first.b) ^ 2) =
      (first.a ^ 2 + first.b ^ 2) *
        lineDeterminant first second third ^ 2 := by
  let firstSecondDenominator :=
    first.a * second.b - second.a * first.b
  let firstThirdDenominator :=
    first.a * third.b - third.a * first.b
  let firstSecondPoint :=
    lineIntersection first second firstSecondNonparallel
  let firstThirdPoint :=
    lineIntersection first third firstThirdNonparallel
  have firstSecondDenominatorNonzero : firstSecondDenominator ≠ 0 := by
    exact firstSecondNonparallel
  have firstThirdDenominatorNonzero : firstThirdDenominator ≠ 0 := by
    exact firstThirdNonparallel
  have firstSecondXCancel :
      firstSecondPoint.x * firstSecondDenominator =
        first.b * second.c - second.b * first.c := by
    dsimp only [firstSecondPoint, lineIntersection, firstSecondDenominator]
    exact RFAP.ExplicitField.div_mul_cancel _
      firstSecondDenominatorNonzero
  have firstSecondYCancel :
      firstSecondPoint.y * firstSecondDenominator =
        first.c * second.a - second.c * first.a := by
    dsimp only [firstSecondPoint, lineIntersection, firstSecondDenominator]
    exact RFAP.ExplicitField.div_mul_cancel _
      firstSecondDenominatorNonzero
  have firstThirdXCancel :
      firstThirdPoint.x * firstThirdDenominator =
        first.b * third.c - third.b * first.c := by
    dsimp only [firstThirdPoint, lineIntersection, firstThirdDenominator]
    exact RFAP.ExplicitField.div_mul_cancel _
      firstThirdDenominatorNonzero
  have firstThirdYCancel :
      firstThirdPoint.y * firstThirdDenominator =
        first.c * third.a - third.c * first.a := by
    dsimp only [firstThirdPoint, lineIntersection, firstThirdDenominator]
    exact RFAP.ExplicitField.div_mul_cancel _
      firstThirdDenominatorNonzero
  have xDifferenceCleared :
      (firstThirdPoint.x - firstSecondPoint.x) *
          (firstSecondDenominator * firstThirdDenominator) =
        first.b * lineDeterminant first second third := by
    calc
      (firstThirdPoint.x - firstSecondPoint.x) *
            (firstSecondDenominator * firstThirdDenominator) =
          (firstThirdPoint.x * firstThirdDenominator) *
              firstSecondDenominator -
            (firstSecondPoint.x * firstSecondDenominator) *
              firstThirdDenominator := by ring1
      _ = (first.b * third.c - third.b * first.c) *
              firstSecondDenominator -
            (first.b * second.c - second.b * first.c) *
              firstThirdDenominator := by
            rw [firstThirdXCancel, firstSecondXCancel]
      _ = first.b * lineDeterminant first second third := by
            unfold firstSecondDenominator firstThirdDenominator
              lineDeterminant
            ring1
  have yDifferenceCleared :
      (firstThirdPoint.y - firstSecondPoint.y) *
          (firstSecondDenominator * firstThirdDenominator) =
        -first.a * lineDeterminant first second third := by
    calc
      (firstThirdPoint.y - firstSecondPoint.y) *
            (firstSecondDenominator * firstThirdDenominator) =
          (firstThirdPoint.y * firstThirdDenominator) *
              firstSecondDenominator -
            (firstSecondPoint.y * firstSecondDenominator) *
              firstThirdDenominator := by ring1
      _ = (first.c * third.a - third.c * first.a) *
              firstSecondDenominator -
            (first.c * second.a - second.c * first.a) *
              firstThirdDenominator := by
            rw [firstThirdYCancel, firstSecondYCancel]
      _ = -first.a * lineDeterminant first second third := by
            unfold firstSecondDenominator firstThirdDenominator
              lineDeterminant
            ring1
  change
    quadrance firstSecondPoint firstThirdPoint *
        (firstSecondDenominator ^ 2 * firstThirdDenominator ^ 2) =
      (first.a ^ 2 + first.b ^ 2) *
        lineDeterminant first second third ^ 2
  calc
    quadrance firstSecondPoint firstThirdPoint *
          (firstSecondDenominator ^ 2 * firstThirdDenominator ^ 2) =
        ((firstThirdPoint.x - firstSecondPoint.x) *
            (firstSecondDenominator * firstThirdDenominator)) ^ 2 +
          ((firstThirdPoint.y - firstSecondPoint.y) *
            (firstSecondDenominator * firstThirdDenominator)) ^ 2 := by
              unfold quadrance
              ring1
    _ = (first.b * lineDeterminant first second third) ^ 2 +
        (-first.a * lineDeterminant first second third) ^ 2 := by
          rw [xDifferenceCleared, yDifferenceCleared]
    _ = (first.a ^ 2 + first.b ^ 2) *
        lineDeterminant first second third ^ 2 := by ring1

/-- Exercise 5.1: the exact printed quadrance between the two intersections
`l₁l₂` and `l₁l₃`.  Its numerator is the norm of `l₁` times the
square of the three-line determinant, and both denominator factors carry
their explicit nonparallel certificates. -/
theorem exercise_5_1
    (first second third : Line K)
    (firstSecondNonparallel : ¬ first.Parallel second)
    (firstThirdNonparallel : ¬ first.Parallel third) :
    quadrance
        (lineIntersection first second firstSecondNonparallel)
        (lineIntersection first third firstThirdNonparallel) =
      ((first.a ^ 2 + first.b ^ 2) *
          lineDeterminant first second third ^ 2) /
        ((first.a * second.b - second.a * first.b) ^ 2 *
          (first.a * third.b - third.a * first.b) ^ 2) := by
  let firstSecondDenominator :=
    first.a * second.b - second.a * first.b
  let firstThirdDenominator :=
    first.a * third.b - third.a * first.b
  have firstSecondDenominatorNonzero : firstSecondDenominator ≠ 0 := by
    exact firstSecondNonparallel
  have firstThirdDenominatorNonzero : firstThirdDenominator ≠ 0 := by
    exact firstThirdNonparallel
  have firstSecondSquareNonzero : firstSecondDenominator ^ 2 ≠ 0 := by
    simpa [pow_two] using
      RFAP.ExplicitField.mul_ne_zero firstSecondDenominatorNonzero
        firstSecondDenominatorNonzero
  have firstThirdSquareNonzero : firstThirdDenominator ^ 2 ≠ 0 := by
    simpa [pow_two] using
      RFAP.ExplicitField.mul_ne_zero firstThirdDenominatorNonzero
        firstThirdDenominatorNonzero
  have denominatorNonzero :
      firstSecondDenominator ^ 2 * firstThirdDenominator ^ 2 ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero firstSecondSquareNonzero
      firstThirdSquareNonzero
  apply eq_of_mul_eq_mul_right denominatorNonzero
  change
    quadrance
          (lineIntersection first second firstSecondNonparallel)
          (lineIntersection first third firstThirdNonparallel) *
        (firstSecondDenominator ^ 2 * firstThirdDenominator ^ 2) =
      (((first.a ^ 2 + first.b ^ 2) *
          lineDeterminant first second third ^ 2) /
        (firstSecondDenominator ^ 2 * firstThirdDenominator ^ 2)) *
          (firstSecondDenominator ^ 2 * firstThirdDenominator ^ 2)
  calc
    quadrance
          (lineIntersection first second firstSecondNonparallel)
          (lineIntersection first third firstThirdNonparallel) *
        (firstSecondDenominator ^ 2 * firstThirdDenominator ^ 2) =
      (first.a ^ 2 + first.b ^ 2) *
        lineDeterminant first second third ^ 2 := by
          unfold firstSecondDenominator firstThirdDenominator
          exact exercise_5_1_cleared first second third
            firstSecondNonparallel firstThirdNonparallel
    _ = (((first.a ^ 2 + first.b ^ 2) *
            lineDeterminant first second third ^ 2) /
          (firstSecondDenominator ^ 2 * firstThirdDenominator ^ 2)) *
        (firstSecondDenominator ^ 2 * firstThirdDenominator ^ 2) :=
      (RFAP.ExplicitField.div_mul_cancel _ denominatorNonzero).symm

end DivineProportions
