import mathlib.Tactic.QuotientFreeRing
import DivineProportions.Trigonometry.Spread
import DivineProportions.Trigonometry.Quadrea

/-!
# Divine Proportions, §§6.4–6.7: triangle ratio theorems

The book's quotient identities are retained exactly.  Every cancellation is
backed by a displayed non-null side or a characteristic hypothesis.
-/

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K]

private theorem eq_zero_of_mul_eq_zero_left [DecidableEq K]
    {left right : K} (leftNonzero : left ≠ 0) (productZero : left * right = 0) :
    right = 0 := by
  by_cases rightZero : right = 0
  · exact rightZero
  · exact False.elim
      ((RFAP.ExplicitField.mul_ne_zero leftNonzero rightZero) productZero)

private theorem div_eq_div_of_cross_mul [DecidableEq K]
    {leftNumerator rightNumerator leftDenominator rightDenominator : K}
    (leftNonzero : leftDenominator ≠ 0)
    (rightNonzero : rightDenominator ≠ 0)
    (crossProduct :
      leftNumerator * rightDenominator =
        rightNumerator * leftDenominator) :
    leftNumerator / leftDenominator =
      rightNumerator / rightDenominator := by
  have leftCancel : leftDenominator * leftDenominator⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel _ leftNonzero
  have rightCancel : rightDenominator * rightDenominator⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel _ rightNonzero
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  calc
    leftNumerator * leftDenominator⁻¹ =
        (leftNumerator * leftDenominator⁻¹) *
          (rightDenominator * rightDenominator⁻¹) := by
            rw [rightCancel, mul_one]
    _ = (leftNumerator * rightDenominator) *
        (leftDenominator⁻¹ * rightDenominator⁻¹) := by ring1
    _ = (rightNumerator * leftDenominator) *
        (leftDenominator⁻¹ * rightDenominator⁻¹) := by
          rw [crossProduct]
    _ = rightNumerator *
        (leftDenominator * leftDenominator⁻¹) *
          rightDenominator⁻¹ := by ring1
    _ = rightNumerator * rightDenominator⁻¹ := by
      rw [leftCancel, mul_one]

private theorem quadrance_ne_zero_of_line_nonNull [DecidableEq K]
    (first second : Point K) (distinct : first ≠ second)
    (nonNull : ¬ (lineThrough first second distinct).IsNull) :
    quadrance first second ≠ 0 := by
  intro quadranceZero
  exact nonNull
    ((null_line_iff_quadrance_zero first second distinct).2 quadranceZero)

private theorem reversedLine_nonNull [DecidableEq K]
    (first second : Point K) (distinct : first ≠ second)
    (nonNull : ¬ (lineThrough first second distinct).IsNull) :
    ¬ (lineThrough second first distinct.symm).IsNull := by
  intro reversedNull
  apply nonNull
  apply (null_line_iff_quadrance_zero first second distinct).2
  have reversedQuadranceZero :=
    (null_line_iff_quadrance_zero second first distinct.symm).1 reversedNull
  calc
    quadrance first second = quadrance second first :=
      quadrance_symm first second
    _ = 0 := reversedQuadranceZero

private theorem spread_lineThrough_reverse_both [DecidableEq K]
    (first second third : Point K)
    (firstSecondDistinct : first ≠ second)
    (firstThirdDistinct : first ≠ third)
    (firstSecondNonNull :
      ¬ (lineThrough first second firstSecondDistinct).IsNull)
    (firstThirdNonNull :
      ¬ (lineThrough first third firstThirdDistinct).IsNull) :
    spread (lineThrough first second firstSecondDistinct)
        (lineThrough first third firstThirdDistinct)
        firstSecondNonNull firstThirdNonNull =
      spread (lineThrough second first firstSecondDistinct.symm)
        (lineThrough third first firstThirdDistinct.symm)
        (reversedLine_nonNull first second firstSecondDistinct firstSecondNonNull)
        (reversedLine_nonNull first third firstThirdDistinct firstThirdNonNull) := by
  unfold spread lineNorm lineThrough
  congr 1 <;> ring1

theorem quadrea_cyclic (first second third : Point K) :
    quadrea second third first = quadrea first second third := by
  unfold quadrea
  rw [quadrance_symm second first, quadrance_symm third first]
  unfold archimedesFunction
  ring1

theorem quadrea_swap_first_second (first second third : Point K) :
    quadrea second first third = quadrea first second third := by
  unfold quadrea
  rw [quadrance_symm second first]
  unfold archimedesFunction
  ring1

theorem quadrea_swap_second_third (first second third : Point K) :
    quadrea first third second = quadrea first second third := by
  unfold quadrea
  rw [quadrance_symm third second, quadrance_symm first second,
    quadrance_symm first third]
  unfold archimedesFunction
  ring1

/-- Theorem 41 (Cross law), proved directly from the point-coordinate cross
formula and one finite denominator cancellation. -/
theorem cross_law [DecidableEq K]
    (first second third : Point K)
    (firstDistinct : first ≠ third) (secondDistinct : second ≠ third)
    (firstNonNull : ¬ (lineThrough first third firstDistinct).IsNull)
    (secondNonNull : ¬ (lineThrough second third secondDistinct).IsNull) :
    (quadrance second third + quadrance first third -
        quadrance first second) ^ 2 =
      4 * quadrance second third * quadrance first third *
        cross (lineThrough first third firstDistinct)
          (lineThrough second third secondDistinct)
          firstNonNull secondNonNull := by
  let dot :=
    (first.y - third.y) * (second.y - third.y) +
      (third.x - first.x) * (third.x - second.x)
  have sideOneNonzero := quadrance_ne_zero_of_line_nonNull
    second third secondDistinct secondNonNull
  have sideTwoNonzero := quadrance_ne_zero_of_line_nonNull
    first third firstDistinct firstNonNull
  have denominatorNonzero :
      quadrance first third * quadrance second third ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero sideTwoNonzero sideOneNonzero
  have denominatorCancel :
      (quadrance first third * quadrance second third) *
        (quadrance first third * quadrance second third)⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel _ denominatorNonzero
  have metricIdentity :
      quadrance second third + quadrance first third -
          quadrance first second = 2 * dot := by
    unfold quadrance dot
    ring1
  rw [cross_from_points first second third firstDistinct secondDistinct
    firstNonNull secondNonNull]
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  rw [metricIdentity]
  calc
    (2 * dot) ^ 2 = 4 * dot ^ 2 := by ring1
    _ = 4 * quadrance second third * quadrance first third *
        (dot ^ 2 *
          (quadrance first third * quadrance second third)⁻¹) := by
            calc
              4 * dot ^ 2 = 4 * dot ^ 2 * 1 := by ring1
              _ = 4 * dot ^ 2 *
                  ((quadrance first third * quadrance second third) *
                    (quadrance first third * quadrance second third)⁻¹) := by
                      rw [denominatorCancel]
              _ = 4 * quadrance second third * quadrance first third *
                  (dot ^ 2 *
                    (quadrance first third * quadrance second third)⁻¹) := by
                      ring1

/-- Theorem 42 (Quadrea spread), at the third vertex. -/
theorem quadrea_spread [DecidableEq K]
    (first second third : Point K)
    (firstDistinct : first ≠ third) (secondDistinct : second ≠ third)
    (firstNonNull : ¬ (lineThrough first third firstDistinct).IsNull)
    (secondNonNull : ¬ (lineThrough second third secondDistinct).IsNull) :
    quadrea first second third =
      4 * quadrance second third * quadrance first third *
        spread (lineThrough first third firstDistinct)
          (lineThrough second third secondDistinct)
          firstNonNull secondNonNull := by
  let determinant := pointDeterminant first second third
  have sideOneNonzero := quadrance_ne_zero_of_line_nonNull
    second third secondDistinct secondNonNull
  have sideTwoNonzero := quadrance_ne_zero_of_line_nonNull
    first third firstDistinct firstNonNull
  have denominatorNonzero :
      quadrance first third * quadrance second third ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero sideTwoNonzero sideOneNonzero
  have denominatorCancel :
      (quadrance first third * quadrance second third) *
        (quadrance first third * quadrance second third)⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel _ denominatorNonzero
  rw [quadrea_coordinate_formula]
  rw [spread_from_points first second third firstDistinct secondDistinct
    firstNonNull secondNonNull]
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  have coordinateDeterminant :
      ((first.y - third.y) * (third.x - second.x) -
        (second.y - third.y) * (third.x - first.x)) ^ 2 =
        determinant ^ 2 := by
    unfold determinant pointDeterminant
    ring1
  rw [coordinateDeterminant]
  calc
    4 * determinant ^ 2 = 4 * determinant ^ 2 * 1 := by ring1
    _ = 4 * determinant ^ 2 *
        ((quadrance first third * quadrance second third) *
          (quadrance first third * quadrance second third)⁻¹) := by
            rw [denominatorCancel]
    _ = 4 * quadrance second third * quadrance first third *
        (determinant ^ 2 *
          (quadrance first third * quadrance second third)⁻¹) := by ring1

/-- Theorem 35 (Spread ratio), at the first vertex of a non-null right
triangle whose right vertex is the third point. -/
theorem spread_ratio [DecidableEq K]
    (first second third : Point K)
    (firstSecondDistinct : first ≠ second)
    (firstThirdDistinct : first ≠ third)
    (secondThirdDistinct : second ≠ third)
    (firstSecondNonNull :
      ¬ (lineThrough first second firstSecondDistinct).IsNull)
    (firstThirdNonNull :
      ¬ (lineThrough first third firstThirdDistinct).IsNull)
    (twoNonzero : (2 : K) ≠ 0)
    (rightAtThird :
      (lineThrough first third firstThirdDistinct).Perpendicular
        (lineThrough second third secondThirdDistinct)) :
    spread (lineThrough first second firstSecondDistinct)
        (lineThrough first third firstThirdDistinct)
        firstSecondNonNull firstThirdNonNull =
      quadrance second third / quadrance first second := by
  have q₂Nonzero := quadrance_ne_zero_of_line_nonNull
    first third firstThirdDistinct firstThirdNonNull
  have q₃Nonzero := quadrance_ne_zero_of_line_nonNull
    first second firstSecondDistinct firstSecondNonNull
  have fourAsProduct : (4 : K) = 2 * 2 := by ring1
  have fourNonzero : (4 : K) ≠ 0 := by
    rw [fourAsProduct]
    exact RFAP.ExplicitField.mul_ne_zero twoNonzero twoNonzero
  have factorNonzero : (4 : K) * quadrance first third ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero fourNonzero q₂Nonzero
  have rightQuadrea := right_triangle_quadrea first second third
    firstThirdDistinct secondThirdDistinct twoNonzero rightAtThird
  have firstSecondReversedNonNull := reversedLine_nonNull
    first second firstSecondDistinct firstSecondNonNull
  have firstThirdReversedNonNull := reversedLine_nonNull
    first third firstThirdDistinct firstThirdNonNull
  have reverseSpread := spread_lineThrough_reverse_both first second third
    firstSecondDistinct firstThirdDistinct
    firstSecondNonNull firstThirdNonNull
  have spreadQuadrea := quadrea_spread second third first
    firstSecondDistinct.symm firstThirdDistinct.symm
    firstSecondReversedNonNull firstThirdReversedNonNull
  rw [quadrea_cyclic first second third] at spreadQuadrea
  rw [quadrance_symm third first, quadrance_symm second first,
    ← reverseSpread] at spreadQuadrea
  have productZero :
      (4 * quadrance first third) *
        (quadrance second third -
          quadrance first second *
            spread (lineThrough first second firstSecondDistinct)
              (lineThrough first third firstThirdDistinct)
              firstSecondNonNull firstThirdNonNull) = 0 := by
    calc
      (4 * quadrance first third) *
          (quadrance second third -
            quadrance first second *
              spread (lineThrough first second firstSecondDistinct)
                (lineThrough first third firstThirdDistinct)
                firstSecondNonNull firstThirdNonNull) =
        4 * quadrance second third * quadrance first third -
          4 * quadrance first third * quadrance first second *
            spread (lineThrough first second firstSecondDistinct)
              (lineThrough first third firstThirdDistinct)
              firstSecondNonNull firstThirdNonNull := by ring1
      _ = 0 := by rw [← rightQuadrea, ← spreadQuadrea]; ring1
  have differenceZero :=
    eq_zero_of_mul_eq_zero_left factorNonzero productZero
  have productRelation :
      spread (lineThrough first second firstSecondDistinct)
          (lineThrough first third firstThirdDistinct)
          firstSecondNonNull firstThirdNonNull * quadrance first second =
        quadrance second third := by
    calc
      spread (lineThrough first second firstSecondDistinct)
            (lineThrough first third firstThirdDistinct)
            firstSecondNonNull firstThirdNonNull * quadrance first second =
          quadrance first second *
            spread (lineThrough first second firstSecondDistinct)
              (lineThrough first third firstThirdDistinct)
              firstSecondNonNull firstThirdNonNull := by ring1
      _ = quadrance second third -
          (quadrance second third - quadrance first second *
            spread (lineThrough first second firstSecondDistinct)
              (lineThrough first third firstThirdDistinct)
              firstSecondNonNull firstThirdNonNull) := by ring1
      _ = quadrance second third := by rw [differenceZero]; ring1
  have denominatorCancel : quadrance first second *
      (quadrance first second)⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel _ q₃Nonzero
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  calc
    spread (lineThrough first second firstSecondDistinct)
        (lineThrough first third firstThirdDistinct)
        firstSecondNonNull firstThirdNonNull =
      spread (lineThrough first second firstSecondDistinct)
          (lineThrough first third firstThirdDistinct)
          firstSecondNonNull firstThirdNonNull *
        (quadrance first second * (quadrance first second)⁻¹) := by
          rw [denominatorCancel, mul_one]
    _ = quadrance second third * (quadrance first second)⁻¹ := by
      rw [← mul_assoc, productRelation]

/-- Theorem 36 (Cross ratio), at the same vertex. -/
theorem cross_ratio [DecidableEq K]
    (first second third : Point K)
    (firstSecondDistinct : first ≠ second)
    (firstThirdDistinct : first ≠ third)
    (secondThirdDistinct : second ≠ third)
    (firstSecondNonNull :
      ¬ (lineThrough first second firstSecondDistinct).IsNull)
    (firstThirdNonNull :
      ¬ (lineThrough first third firstThirdDistinct).IsNull)
    (twoNonzero : (2 : K) ≠ 0)
    (rightAtThird :
      (lineThrough first third firstThirdDistinct).Perpendicular
        (lineThrough second third secondThirdDistinct)) :
    cross (lineThrough first second firstSecondDistinct)
        (lineThrough first third firstThirdDistinct)
        firstSecondNonNull firstThirdNonNull =
      quadrance first third / quadrance first second := by
  have q₃Nonzero := quadrance_ne_zero_of_line_nonNull
    first second firstSecondDistinct firstSecondNonNull
  have q₃Cancel : quadrance first second *
      (quadrance first second)⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel _ q₃Nonzero
  have pythagoras :=
    (pythagoras_iff_perpendicular first second third
      firstThirdDistinct secondThirdDistinct twoNonzero).2 rightAtThird
  have sumOne := spread_add_cross
    (lineThrough first second firstSecondDistinct)
    (lineThrough first third firstThirdDistinct)
    firstSecondNonNull firstThirdNonNull
  have spreadValue := spread_ratio first second third
    firstSecondDistinct firstThirdDistinct secondThirdDistinct
    firstSecondNonNull firstThirdNonNull twoNonzero rightAtThird
  have crossAsComplement :
      cross (lineThrough first second firstSecondDistinct)
          (lineThrough first third firstThirdDistinct)
          firstSecondNonNull firstThirdNonNull =
        1 - spread (lineThrough first second firstSecondDistinct)
          (lineThrough first third firstThirdDistinct)
          firstSecondNonNull firstThirdNonNull := by
    calc
      cross (lineThrough first second firstSecondDistinct)
          (lineThrough first third firstThirdDistinct)
          firstSecondNonNull firstThirdNonNull =
        (spread (lineThrough first second firstSecondDistinct)
            (lineThrough first third firstThirdDistinct)
            firstSecondNonNull firstThirdNonNull +
          cross (lineThrough first second firstSecondDistinct)
            (lineThrough first third firstThirdDistinct)
            firstSecondNonNull firstThirdNonNull) -
          spread (lineThrough first second firstSecondDistinct)
            (lineThrough first third firstThirdDistinct)
            firstSecondNonNull firstThirdNonNull := by ring1
      _ = 1 - spread (lineThrough first second firstSecondDistinct)
          (lineThrough first third firstThirdDistinct)
          firstSecondNonNull firstThirdNonNull := by rw [sumOne]
  rw [crossAsComplement, spreadValue]
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  calc
    1 - quadrance second third * (quadrance first second)⁻¹ =
        quadrance first second * (quadrance first second)⁻¹ -
          quadrance second third * (quadrance first second)⁻¹ := by
            rw [q₃Cancel]
    _ = quadrance first third * (quadrance first second)⁻¹ := by
      rw [← pythagoras]
      ring1

/-- Theorem 37 (Twist ratio).  The only needed metric denominator is the
nonzero second quadrance; the hypotenuse may be null. -/
theorem twist_ratio [DecidableEq K]
    (first second third : Point K)
    (firstSecondDistinct : first ≠ second)
    (firstThirdDistinct : first ≠ third)
    (secondThirdDistinct : second ≠ third)
    (q₂Nonzero : quadrance first third ≠ 0)
    (rightAtThird :
      (lineThrough first third firstThirdDistinct).Perpendicular
        (lineThrough second third secondThirdDistinct))
    (notPerpendicularAtFirst :
      ¬ (lineThrough first second firstSecondDistinct).Perpendicular
        (lineThrough first third firstThirdDistinct)) :
    twist (lineThrough first second firstSecondDistinct)
        (lineThrough first third firstThirdDistinct)
        notPerpendicularAtFirst =
      quadrance second third / quadrance first third := by
  let determinant := pointDeterminant first second third
  let dotAtFirst :=
    (first.y - second.y) * (first.y - third.y) +
      (second.x - first.x) * (third.x - first.x)
  have perpendicularEquation :
      (first.y - third.y) * (second.y - third.y) +
        (third.x - first.x) * (third.x - second.x) = 0 := by
    exact rightAtThird
  have dotValue : dotAtFirst = quadrance first third := by
    unfold dotAtFirst quadrance
    calc
      (first.y - second.y) * (first.y - third.y) +
          (second.x - first.x) * (third.x - first.x) =
        (third.x - first.x) ^ 2 + (third.y - first.y) ^ 2 -
          ((first.y - third.y) * (second.y - third.y) +
            (third.x - first.x) * (third.x - second.x)) := by ring1
      _ = (third.x - first.x) ^ 2 + (third.y - first.y) ^ 2 := by
        rw [perpendicularEquation]
        ring1
  have determinantSquare : determinant ^ 2 =
      quadrance second third * quadrance first third := by
    have fibonacci : determinant ^ 2 +
        ((first.y - third.y) * (second.y - third.y) +
          (third.x - first.x) * (third.x - second.x)) ^ 2 =
        quadrance second third * quadrance first third := by
      unfold determinant pointDeterminant quadrance
      ring1
    rw [perpendicularEquation] at fibonacci
    simpa using fibonacci
  have q₂SquareNonzero : quadrance first third ^ 2 ≠ 0 := by
    simpa [pow_two] using
      RFAP.ExplicitField.mul_ne_zero q₂Nonzero q₂Nonzero
  have q₂SquareCancel : quadrance first third ^ 2 *
      (quadrance first third ^ 2)⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel _ q₂SquareNonzero
  unfold twist
  change
    (((first.y - second.y) * (third.x - first.x) -
      (first.y - third.y) * (second.x - first.x)) ^ 2) /
      dotAtFirst ^ 2 = quadrance second third / quadrance first third
  have determinantCoordinate :
      ((first.y - second.y) * (third.x - first.x) -
        (first.y - third.y) * (second.x - first.x)) ^ 2 =
        determinant ^ 2 := by
    unfold determinant pointDeterminant
    ring1
  rw [determinantCoordinate, determinantSquare, dotValue]
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  calc
    quadrance second third * quadrance first third *
        (quadrance first third ^ 2)⁻¹ =
      quadrance second third * (quadrance first third)⁻¹ *
        (quadrance first third ^ 2 *
          (quadrance first third ^ 2)⁻¹) := by
            have q₂Cancel : quadrance first third *
                (quadrance first third)⁻¹ = (1 : K) :=
              RFAP.ExplicitField.mul_inv_cancel _ q₂Nonzero
            calc
              quadrance second third * quadrance first third *
                  (quadrance first third ^ 2)⁻¹ =
                quadrance second third * (quadrance first third)⁻¹ *
                  (quadrance first third ^ 2 *
                    (quadrance first third ^ 2)⁻¹) +
                  quadrance second third * (quadrance first third ^ 2)⁻¹ *
                    (quadrance first third -
                      quadrance first third ^ 2 *
                        (quadrance first third)⁻¹) := by ring1
              _ = quadrance second third * (quadrance first third)⁻¹ *
                  (quadrance first third ^ 2 *
                    (quadrance first third ^ 2)⁻¹) := by
                      rw [show quadrance first third ^ 2 *
                        (quadrance first third)⁻¹ =
                          quadrance first third by
                            calc
                              quadrance first third ^ 2 *
                                  (quadrance first third)⁻¹ =
                                quadrance first third *
                                  (quadrance first third *
                                    (quadrance first third)⁻¹) := by ring1
                              _ = quadrance first third := by
                                rw [q₂Cancel, mul_one]]
                      ring1
    _ = quadrance second third * (quadrance first third)⁻¹ := by
      rw [q₂SquareCancel, mul_one]

/-- Theorem 38 (Complementary spreads). -/
theorem complementary_spreads [DecidableEq K]
    (first second third : Line K)
    (firstNonNull : ¬ first.IsNull) (secondNonNull : ¬ second.IsNull)
    (thirdNonNull : ¬ third.IsNull)
    (perpendicular : first.Perpendicular second) :
    spread second third secondNonNull thirdNonNull +
      spread first third firstNonNull thirdNonNull = 1 := by
  have firstNormNonzero : lineNorm first ≠ 0 := firstNonNull
  have secondNormNonzero : lineNorm second ≠ 0 := secondNonNull
  have thirdNormNonzero : lineNorm third ≠ 0 := thirdNonNull
  have firstThirdDenominatorNonzero :
      lineNorm first * lineNorm third ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero firstNormNonzero thirdNormNonzero
  have secondThirdDenominatorNonzero :
      lineNorm second * lineNorm third ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero secondNormNonzero thirdNormNonzero
  let uvDet := first.a * second.b - second.a * first.b
  let uwDot := first.a * third.a + first.b * third.b
  let vwDet := second.a * third.b - third.a * second.b
  have perpendicularZero : first.a * second.a + first.b * second.b = 0 :=
    perpendicular
  have determinantSquare : uvDet ^ 2 = lineNorm first * lineNorm second := by
    unfold uvDet lineNorm
    calc
      (first.a * second.b - second.a * first.b) ^ 2 =
          (first.a ^ 2 + first.b ^ 2) *
            (second.a ^ 2 + second.b ^ 2) -
          (first.a * second.a + first.b * second.b) ^ 2 := by ring1
      _ = (first.a ^ 2 + first.b ^ 2) *
          (second.a ^ 2 + second.b ^ 2) := by rw [perpendicularZero]; ring1
  have linearIdentity : lineNorm first * vwDet = -(uvDet * uwDot) := by
    unfold lineNorm vwDet uvDet uwDot
    calc
      (first.a ^ 2 + first.b ^ 2) *
          (second.a * third.b - third.a * second.b) =
        (first.a * second.a + first.b * second.b) *
            (first.a * third.b - third.a * first.b) -
          (first.a * second.b - second.a * first.b) *
            (first.a * third.a + first.b * third.b) := by ring1
      _ = -(uvDet * uwDot) := by rw [perpendicularZero]; ring1
  have squaredIdentity : lineNorm first ^ 2 * vwDet ^ 2 =
      uvDet ^ 2 * uwDot ^ 2 := by
    calc
      lineNorm first ^ 2 * vwDet ^ 2 =
          (lineNorm first * vwDet) ^ 2 := by ring1
      _ = (-(uvDet * uwDot)) ^ 2 := by rw [linearIdentity]
      _ = uvDet ^ 2 * uwDot ^ 2 := by ring1
  have cancellationProduct : lineNorm first *
      (lineNorm first * vwDet ^ 2 - lineNorm second * uwDot ^ 2) = 0 := by
    calc
      lineNorm first *
          (lineNorm first * vwDet ^ 2 - lineNorm second * uwDot ^ 2) =
        lineNorm first ^ 2 * vwDet ^ 2 -
          (lineNorm first * lineNorm second) * uwDot ^ 2 := by ring1
      _ = uvDet ^ 2 * uwDot ^ 2 - uvDet ^ 2 * uwDot ^ 2 := by
        rw [squaredIdentity, determinantSquare]
      _ = 0 := by ring1
  have scaledNumerators : lineNorm first * vwDet ^ 2 =
      lineNorm second * uwDot ^ 2 := by
    have differenceZero := eq_zero_of_mul_eq_zero_left
      firstNormNonzero cancellationProduct
    calc
      lineNorm first * vwDet ^ 2 =
          (lineNorm first * vwDet ^ 2 - lineNorm second * uwDot ^ 2) +
            lineNorm second * uwDot ^ 2 := by ring1
      _ = lineNorm second * uwDot ^ 2 := by rw [differenceZero]; ring1
  have spreadEqualsCross :
      spread second third secondNonNull thirdNonNull =
        cross first third firstNonNull thirdNonNull := by
    apply div_eq_div_of_cross_mul
      secondThirdDenominatorNonzero firstThirdDenominatorNonzero
    change vwDet ^ 2 * (lineNorm first * lineNorm third) =
      uwDot ^ 2 * (lineNorm second * lineNorm third)
    calc
      vwDet ^ 2 * (lineNorm first * lineNorm third) =
        lineNorm third * (lineNorm first * vwDet ^ 2) := by ring1
      _ = lineNorm third * (lineNorm second * uwDot ^ 2) := by
        rw [scaledNumerators]
      _ = uwDot ^ 2 * (lineNorm second * lineNorm third) := by ring1
  rw [spreadEqualsCross]
  calc
    cross first third firstNonNull thirdNonNull +
        spread first third firstNonNull thirdNonNull =
      spread first third firstNonNull thirdNonNull +
        cross first third firstNonNull thirdNonNull := by ring1
    _ = 1 := spread_add_cross first third firstNonNull thirdNonNull

/-- Theorem 39 (Perpendicular spreads). -/
theorem perpendicular_spreads [DecidableEq K]
    (first second firstOther secondOther : Line K)
    (firstNonNull : ¬ first.IsNull) (secondNonNull : ¬ second.IsNull)
    (firstOtherNonNull : ¬ firstOther.IsNull)
    (secondOtherNonNull : ¬ secondOther.IsNull)
    (firstPairPerpendicular : first.Perpendicular second)
    (secondPairPerpendicular : firstOther.Perpendicular secondOther) :
    spread first firstOther firstNonNull firstOtherNonNull =
      spread second secondOther secondNonNull secondOtherNonNull := by
  have firstComplement := complementary_spreads
    first second firstOther firstNonNull secondNonNull firstOtherNonNull
    firstPairPerpendicular
  have secondComplement := complementary_spreads
    firstOther secondOther second firstOtherNonNull secondOtherNonNull
    secondNonNull secondPairPerpendicular
  rw [spread_symm firstOther second firstOtherNonNull secondNonNull,
    spread_symm secondOther second secondOtherNonNull secondNonNull]
    at secondComplement
  have secondComplementReordered :
      spread second firstOther secondNonNull firstOtherNonNull +
        spread second secondOther secondNonNull secondOtherNonNull = 1 := by
    calc
      spread second firstOther secondNonNull firstOtherNonNull +
          spread second secondOther secondNonNull secondOtherNonNull =
        spread second secondOther secondNonNull secondOtherNonNull +
          spread second firstOther secondNonNull firstOtherNonNull := by ring1
      _ = 1 := secondComplement
  calc
    spread first firstOther firstNonNull firstOtherNonNull =
        1 - spread second firstOther secondNonNull firstOtherNonNull := by
          calc
            spread first firstOther firstNonNull firstOtherNonNull =
              (spread second firstOther secondNonNull firstOtherNonNull +
                spread first firstOther firstNonNull firstOtherNonNull) -
                spread second firstOther secondNonNull firstOtherNonNull := by ring1
            _ = 1 - spread second firstOther secondNonNull firstOtherNonNull := by
              rw [firstComplement]
    _ = spread second secondOther secondNonNull secondOtherNonNull := by
      calc
        1 - spread second firstOther secondNonNull firstOtherNonNull =
          (spread second firstOther secondNonNull firstOtherNonNull +
            spread second secondOther secondNonNull secondOtherNonNull) -
            spread second firstOther secondNonNull firstOtherNonNull := by
              rw [secondComplementReordered]
        _ = spread second secondOther secondNonNull secondOtherNonNull := by ring1

/-- Theorem 40 (Spread law), stated as the source's three quotient equalities. -/
theorem spread_law [DecidableEq K]
    (first second third : Point K)
    (firstSecondDistinct : first ≠ second)
    (firstThirdDistinct : first ≠ third)
    (secondThirdDistinct : second ≠ third)
    (firstSecondNonNull :
      ¬ (lineThrough first second firstSecondDistinct).IsNull)
    (firstThirdNonNull :
      ¬ (lineThrough first third firstThirdDistinct).IsNull)
    (secondThirdNonNull :
      ¬ (lineThrough second third secondThirdDistinct).IsNull)
    (twoNonzero : (2 : K) ≠ 0) :
    spread (lineThrough first second firstSecondDistinct)
          (lineThrough first third firstThirdDistinct)
          firstSecondNonNull firstThirdNonNull / quadrance second third =
      spread (lineThrough second first firstSecondDistinct.symm)
          (lineThrough second third secondThirdDistinct)
          (by rwa [null_line_iff_quadrance_zero,
            quadrance_symm second first,
            ← null_line_iff_quadrance_zero first second firstSecondDistinct])
          secondThirdNonNull / quadrance first third ∧
    spread (lineThrough second first firstSecondDistinct.symm)
          (lineThrough second third secondThirdDistinct)
          (by rwa [null_line_iff_quadrance_zero,
            quadrance_symm second first,
            ← null_line_iff_quadrance_zero first second firstSecondDistinct])
          secondThirdNonNull / quadrance first third =
      spread (lineThrough third first firstThirdDistinct.symm)
          (lineThrough third second secondThirdDistinct.symm)
          (by rwa [null_line_iff_quadrance_zero,
            quadrance_symm third first,
            ← null_line_iff_quadrance_zero first third firstThirdDistinct])
          (by rwa [null_line_iff_quadrance_zero,
            quadrance_symm third second,
            ← null_line_iff_quadrance_zero second third secondThirdDistinct]) /
        quadrance first second := by
  -- The proof is algebraically cleaner after naming the reversed-side
  -- non-null certificates used at the second and third vertices.
  let firstSecondReversedNonNull :
      ¬ (lineThrough second first firstSecondDistinct.symm).IsNull := by
    rwa [null_line_iff_quadrance_zero,
      quadrance_symm second first,
      ← null_line_iff_quadrance_zero first second firstSecondDistinct]
  let firstThirdReversedNonNull :
      ¬ (lineThrough third first firstThirdDistinct.symm).IsNull := by
    rwa [null_line_iff_quadrance_zero,
      quadrance_symm third first,
      ← null_line_iff_quadrance_zero first third firstThirdDistinct]
  let secondThirdReversedNonNull :
      ¬ (lineThrough third second secondThirdDistinct.symm).IsNull := by
    rwa [null_line_iff_quadrance_zero,
      quadrance_symm third second,
      ← null_line_iff_quadrance_zero second third secondThirdDistinct]
  let s₁ := spread (lineThrough first second firstSecondDistinct)
    (lineThrough first third firstThirdDistinct)
    firstSecondNonNull firstThirdNonNull
  let s₂ := spread (lineThrough second first firstSecondDistinct.symm)
    (lineThrough second third secondThirdDistinct)
    firstSecondReversedNonNull secondThirdNonNull
  let s₃ := spread (lineThrough third first firstThirdDistinct.symm)
    (lineThrough third second secondThirdDistinct.symm)
    firstThirdReversedNonNull secondThirdReversedNonNull
  have q₁Nonzero := quadrance_ne_zero_of_line_nonNull
    second third secondThirdDistinct secondThirdNonNull
  have q₂Nonzero := quadrance_ne_zero_of_line_nonNull
    first third firstThirdDistinct firstThirdNonNull
  have q₃Nonzero := quadrance_ne_zero_of_line_nonNull
    first second firstSecondDistinct firstSecondNonNull
  have fourAsProduct : (4 : K) = 2 * 2 := by ring1
  have fourNonzero : (4 : K) ≠ 0 := by
    rw [fourAsProduct]
    exact RFAP.ExplicitField.mul_ne_zero twoNonzero twoNonzero
  have factorFor12 : (4 : K) * quadrance first second ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero fourNonzero q₃Nonzero
  have factorFor23 : (4 : K) * quadrance second third ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero fourNonzero q₁Nonzero
  have reverseSpreadAtFirst := spread_lineThrough_reverse_both
    first second third firstSecondDistinct firstThirdDistinct
    firstSecondNonNull firstThirdNonNull
  have reverseSpreadAtSecond := spread_lineThrough_reverse_both
    second first third firstSecondDistinct.symm secondThirdDistinct
    firstSecondReversedNonNull secondThirdNonNull
  have reverseSpreadAtThird := spread_lineThrough_reverse_both
    third first second firstThirdDistinct.symm secondThirdDistinct.symm
    firstThirdReversedNonNull secondThirdReversedNonNull
  have areaAtFirst := quadrea_spread second third first
    firstSecondDistinct.symm firstThirdDistinct.symm
    firstSecondReversedNonNull firstThirdReversedNonNull
  have areaAtSecond := quadrea_spread first third second
    firstSecondDistinct secondThirdDistinct.symm
    firstSecondNonNull secondThirdReversedNonNull
  have areaAtThird := quadrea_spread first second third
    firstThirdDistinct secondThirdDistinct
    firstThirdNonNull secondThirdNonNull
  rw [quadrea_cyclic first second third] at areaAtFirst
  rw [quadrea_swap_second_third first second third] at areaAtSecond
  rw [quadrance_symm third first, quadrance_symm second first,
    ← reverseSpreadAtFirst] at areaAtFirst
  rw [quadrance_symm third second, ← reverseSpreadAtSecond] at areaAtSecond
  rw [← reverseSpreadAtThird] at areaAtThird
  change quadrea first second third =
      4 * quadrance first third * quadrance first second * s₁ at areaAtFirst
  change quadrea first second third =
      4 * quadrance second third * quadrance first second * s₂ at areaAtSecond
  change quadrea first second third =
      4 * quadrance second third * quadrance first third * s₃ at areaAtThird
  have firstSecondCross : s₁ * quadrance first third =
      s₂ * quadrance second third := by
    have productZero : (4 * quadrance first second) *
        (s₁ * quadrance first third -
          s₂ * quadrance second third) = 0 := by
      calc
        (4 * quadrance first second) *
            (s₁ * quadrance first third -
              s₂ * quadrance second third) =
          4 * quadrance first third * quadrance first second * s₁ -
            4 * quadrance second third * quadrance first second * s₂ := by
              ring1
        _ = 0 := by rw [← areaAtFirst, ← areaAtSecond]; ring1
    have differenceZero :=
      eq_zero_of_mul_eq_zero_left factorFor12 productZero
    calc
      s₁ * quadrance first third =
          (s₁ * quadrance first third -
            s₂ * quadrance second third) +
            s₂ * quadrance second third := by ring1
      _ = s₂ * quadrance second third := by rw [differenceZero]; ring1
  have secondThirdCross : s₂ * quadrance first second =
      s₃ * quadrance first third := by
    have productZero : (4 * quadrance second third) *
        (s₂ * quadrance first second -
          s₃ * quadrance first third) = 0 := by
      calc
        (4 * quadrance second third) *
            (s₂ * quadrance first second -
              s₃ * quadrance first third) =
          4 * quadrance second third * quadrance first second * s₂ -
            4 * quadrance second third * quadrance first third * s₃ := by
              ring1
        _ = 0 := by rw [← areaAtSecond, ← areaAtThird]; ring1
    have differenceZero :=
      eq_zero_of_mul_eq_zero_left factorFor23 productZero
    calc
      s₂ * quadrance first second =
          (s₂ * quadrance first second -
            s₃ * quadrance first third) +
            s₃ * quadrance first third := by ring1
      _ = s₃ * quadrance first third := by rw [differenceZero]; ring1
  change s₁ / quadrance second third =
      s₂ / quadrance first third ∧
    s₂ / quadrance first third = s₃ / quadrance first second
  constructor
  · exact div_eq_div_of_cross_mul q₁Nonzero q₂Nonzero
      firstSecondCross
  · exact div_eq_div_of_cross_mul q₂Nonzero q₃Nonzero
      secondThirdCross

end DivineProportions
