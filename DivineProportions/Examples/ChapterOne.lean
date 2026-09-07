import DivineProportions.Trigonometry.Quadrea

/-!
# Divine Proportions, Chapter 1 finite calculation

The introductory `4,5,7` triangle is recorded entirely through its three
quadrances.  Its Archimedes value is the common numerator in the three spread
ratios, so Exercise 1.1 reduces to two exact finite fraction calculations.
Exercise 1.2 asks the reader to inspect other books; it makes no mathematical
claim to encode in Lean.
-/

namespace DivineProportions
namespace ChapterOneExamples

variable {K : Type*} [RFAP.ExplicitField K]

private theorem div_eq_div_of_cross_mul
    {leftNumerator rightNumerator leftDenominator rightDenominator : K}
    (leftNonzero : leftDenominator ≠ 0)
    (rightNonzero : rightDenominator ≠ 0)
    (crossProduct :
      leftNumerator * rightDenominator =
        rightNumerator * leftDenominator) :
    leftNumerator / leftDenominator =
      rightNumerator / rightDenominator := by
  have leftCancel : leftDenominator * leftDenominator⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel leftDenominator leftNonzero
  have rightCancel : rightDenominator * rightDenominator⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel rightDenominator rightNonzero
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  calc
    leftNumerator * leftDenominator⁻¹ =
        leftNumerator * leftDenominator⁻¹ *
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

/-- The `4,5,7` triangle has the exact denominator-free quadrea `1536`. -/
theorem introductory_quadrea :
    archimedesFunction (25 : K) 16 49 = 1536 := by
  unfold archimedesFunction
  ring1

/-- Exercise 1.1, together with the preceding displayed value of `s₁`.
The three denominators are justified from exactly the source's characteristic
exclusions for `2`, `5`, and `7`. -/
theorem exercise_1_1
    (twoNonzero : (2 : K) ≠ 0)
    (fiveNonzero : (5 : K) ≠ 0)
    (sevenNonzero : (7 : K) ≠ 0) :
    let area := archimedesFunction (25 : K) 16 49
    area / (4 * 25 * 49) = 384 / 1225 ∧
      area / (4 * 25 * 16) = 24 / 25 ∧
      area / (4 * 49 * 16) = 24 / 49 := by
  dsimp only
  rw [introductory_quadrea]
  have fourNonzero : (4 : K) ≠ 0 := by
    rw [show (4 : K) = 2 * 2 by ring1]
    exact RFAP.ExplicitField.mul_ne_zero twoNonzero twoNonzero
  have sixteenNonzero : (16 : K) ≠ 0 := by
    rw [show (16 : K) = 4 * 4 by ring1]
    exact RFAP.ExplicitField.mul_ne_zero fourNonzero fourNonzero
  have twentyFiveNonzero : (25 : K) ≠ 0 := by
    rw [show (25 : K) = 5 * 5 by ring1]
    exact RFAP.ExplicitField.mul_ne_zero fiveNonzero fiveNonzero
  have fortyNineNonzero : (49 : K) ≠ 0 := by
    rw [show (49 : K) = 7 * 7 by ring1]
    exact RFAP.ExplicitField.mul_ne_zero sevenNonzero sevenNonzero
  have twelveTwentyFiveNonzero : (1225 : K) ≠ 0 := by
    rw [show (1225 : K) = 25 * 49 by ring1]
    exact RFAP.ExplicitField.mul_ne_zero twentyFiveNonzero fortyNineNonzero
  have firstDenominatorNonzero : (4 * 25 * 49 : K) ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero
      (RFAP.ExplicitField.mul_ne_zero fourNonzero twentyFiveNonzero)
      fortyNineNonzero
  have secondDenominatorNonzero : (4 * 25 * 16 : K) ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero
      (RFAP.ExplicitField.mul_ne_zero fourNonzero twentyFiveNonzero)
      sixteenNonzero
  have thirdDenominatorNonzero : (4 * 49 * 16 : K) ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero
      (RFAP.ExplicitField.mul_ne_zero fourNonzero fortyNineNonzero)
      sixteenNonzero
  constructor
  · apply div_eq_div_of_cross_mul firstDenominatorNonzero
      twelveTwentyFiveNonzero
    ring1
  constructor
  · apply div_eq_div_of_cross_mul secondDenominatorNonzero twentyFiveNonzero
    ring1
  · apply div_eq_div_of_cross_mul thirdDenominatorNonzero fortyNineNonzero
    ring1

end ChapterOneExamples
end DivineProportions
