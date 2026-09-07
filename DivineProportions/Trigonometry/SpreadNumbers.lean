import DivineProportions.Trigonometry.Spread

/-!
# Divine Proportions, Exercises 2.1–2.2: spread-number parameters

The square root in the definition of a spread number is an explicit witness.
Consequently the converse parametrization computes its parameter directly;
it never selects a root or searches a field.
-/

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K]

/-- The rational parametrization `u²/(1+u²)` from Exercise 2.1. -/
def spreadParameter (parameter : K) : K :=
  parameter ^ 2 / (1 + parameter ^ 2)

private theorem one_add_square_nonzero {value : K}
    (squareNotNegativeOne : value ^ 2 ≠ -1) :
    1 + value ^ 2 ≠ 0 := by
  intro sumZero
  apply squareNotNegativeOne
  calc
    value ^ 2 = (1 + value ^ 2) - 1 := by ring1
    _ = -1 := by rw [sumZero]; ring1

private theorem one_sub_nonzero {value : K} (notOne : value ≠ 1) :
    1 - value ≠ 0 := by
  intro differenceZero
  apply notOne
  calc
    value = 1 - (1 - value) := by ring1
    _ = 1 := by rw [differenceZero]; ring1

private theorem eq_of_nonzero_mul_right
    {factor left right : K} (factorNonzero : factor ≠ 0)
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

private theorem div_eq_div_of_cross_mul
    {leftNumerator rightNumerator leftDenominator rightDenominator : K}
    (leftNonzero : leftDenominator ≠ 0)
    (rightNonzero : rightDenominator ≠ 0)
    (crossProduct :
      leftNumerator * rightDenominator =
        rightNumerator * leftDenominator) :
    leftNumerator / leftDenominator =
      rightNumerator / rightDenominator := by
  have leftCancel :
      leftDenominator * leftDenominator⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel leftDenominator leftNonzero
  have rightCancel :
      rightDenominator * rightDenominator⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel rightDenominator rightNonzero
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  calc
    leftNumerator * leftDenominator⁻¹ =
        leftNumerator * leftDenominator⁻¹ *
          (rightDenominator * rightDenominator⁻¹) := by
      rw [rightCancel]
      ring1
    _ = (leftNumerator * rightDenominator) *
        (leftDenominator⁻¹ * rightDenominator⁻¹) := by ring1
    _ = (rightNumerator * leftDenominator) *
        (leftDenominator⁻¹ * rightDenominator⁻¹) := by rw [crossProduct]
    _ = rightNumerator *
        (leftDenominator * leftDenominator⁻¹) * rightDenominator⁻¹ := by
      ring1
    _ = rightNumerator * rightDenominator⁻¹ := by rw [leftCancel]; ring1

/-- First half of Exercise 2.1: every valid rational parameter produces a
spread number, with the square witness displayed. -/
theorem spreadParameter_isSpreadNumber
    (parameter : K) (squareNotNegativeOne : parameter ^ 2 ≠ -1) :
    IsSpreadNumber (spreadParameter parameter) := by
  let denominator := 1 + parameter ^ 2
  have denominatorNonzero : denominator ≠ 0 :=
    one_add_square_nonzero squareNotNegativeOne
  have denominatorCancel : denominator * denominator⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel denominator denominatorNonzero
  refine ⟨parameter / denominator, ?_⟩
  unfold spreadParameter
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  have complement :
      1 - parameter ^ 2 * denominator⁻¹ = denominator⁻¹ := by
    calc
      1 - parameter ^ 2 * denominator⁻¹ =
          denominator * denominator⁻¹ -
            parameter ^ 2 * denominator⁻¹ := by rw [denominatorCancel]
      _ = denominator⁻¹ := by unfold denominator; ring1
  rw [complement]
  ring1

/-- Converse half of Exercise 2.1: the stored square witness gives the
explicit parameter `root/(1-s)`. -/
theorem spreadNumber_has_parameter
    (value : K) (spreadNumber : IsSpreadNumber value)
    (notOne : value ≠ 1) :
    ∃ parameter : K,
      parameter ^ 2 ≠ -1 ∧ value = spreadParameter parameter := by
  rcases spreadNumber with ⟨root, squareWitness⟩
  let denominator := 1 - value
  let parameter := root / denominator
  have denominatorNonzero : denominator ≠ 0 := one_sub_nonzero notOne
  have denominatorCancel : denominator * denominator⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel denominator denominatorNonzero
  have parameterSquare :
      parameter ^ 2 = value * denominator⁻¹ := by
    unfold parameter
    simp only [RFAP.ExplicitField.div_eq_mul_inv]
    calc
      (root * denominator⁻¹) ^ 2 =
          root ^ 2 * denominator⁻¹ ^ 2 := by ring1
      _ = value * denominator * denominator⁻¹ ^ 2 := by
        rw [← squareWitness]
      _ = value * denominator⁻¹ *
          (denominator * denominator⁻¹) := by ring1
      _ = value * denominator⁻¹ := by rw [denominatorCancel]; ring1
  have parameterDenominator :
      1 + parameter ^ 2 = denominator⁻¹ := by
    rw [parameterSquare]
    calc
      1 + value * denominator⁻¹ =
          denominator * denominator⁻¹ + value * denominator⁻¹ := by
        rw [denominatorCancel]
      _ = denominator⁻¹ := by unfold denominator; ring1
  have parameterDenominatorNonzero : 1 + parameter ^ 2 ≠ 0 := by
    rw [parameterDenominator]
    exact RFAP.ExplicitField.inv_ne_zero denominatorNonzero
  have parameterSquareNotNegativeOne : parameter ^ 2 ≠ -1 := by
    intro squareNegativeOne
    apply parameterDenominatorNonzero
    rw [squareNegativeOne]
    ring1
  refine ⟨parameter, parameterSquareNotNegativeOne, ?_⟩
  unfold spreadParameter
  apply eq_of_nonzero_mul_right parameterDenominatorNonzero
  calc
    value * (1 + parameter ^ 2) = value * denominator⁻¹ := by
      rw [parameterDenominator]
    _ = parameter ^ 2 := parameterSquare.symm
    _ = (parameter ^ 2 / (1 + parameter ^ 2)) *
        (1 + parameter ^ 2) :=
      (RFAP.ExplicitField.div_mul_cancel _
        parameterDenominatorNonzero).symm

/-- Exercise 2.1, with both directions and all denominator certificates. -/
theorem exercise_2_1
    (parameter : K) (squareNotNegativeOne : parameter ^ 2 ≠ -1) :
    IsSpreadNumber (spreadParameter parameter) ∧
      ∀ value : K, IsSpreadNumber value → value ≠ 1 →
        ∃ recovered : K,
          recovered ^ 2 ≠ -1 ∧ value = spreadParameter recovered := by
  exact ⟨spreadParameter_isSpreadNumber parameter squareNotNegativeOne,
    spreadNumber_has_parameter⟩

/-- The two-input number in Exercise 2.2. -/
def twoPointSpreadNumber (x y : K) : K :=
  (x - y) ^ 2 / ((1 + x ^ 2) * (1 + y ^ 2))

/-- The parameter requested in the final clause of Exercise 2.2. -/
def twoPointSpreadParameter (x y : K) : K :=
  (x - y) / (1 + x * y)

/-- First clause of Exercise 2.2, including the explicit square witness. -/
theorem twoPointSpreadNumber_isSpreadNumber
    (x y : K) (xSquareNotNegativeOne : x ^ 2 ≠ -1)
    (ySquareNotNegativeOne : y ^ 2 ≠ -1) :
    IsSpreadNumber (twoPointSpreadNumber x y) := by
  let numerator := x - y
  let complementNumerator := 1 + x * y
  let denominator := (1 + x ^ 2) * (1 + y ^ 2)
  have denominatorNonzero : denominator ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero
      (one_add_square_nonzero xSquareNotNegativeOne)
      (one_add_square_nonzero ySquareNotNegativeOne)
  have denominatorCancel : denominator * denominator⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel denominator denominatorNonzero
  have fibonacci :
      denominator = numerator ^ 2 + complementNumerator ^ 2 := by
    unfold denominator numerator complementNumerator
    ring1
  refine ⟨numerator * complementNumerator / denominator, ?_⟩
  unfold twoPointSpreadNumber
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  change
    numerator ^ 2 * denominator⁻¹ *
        (1 - numerator ^ 2 * denominator⁻¹) =
      (numerator * complementNumerator * denominator⁻¹) ^ 2
  have complement :
      1 - numerator ^ 2 * denominator⁻¹ =
        complementNumerator ^ 2 * denominator⁻¹ := by
    calc
      1 - numerator ^ 2 * denominator⁻¹ =
          denominator * denominator⁻¹ -
            numerator ^ 2 * denominator⁻¹ := by rw [denominatorCancel]
      _ = complementNumerator ^ 2 * denominator⁻¹ := by
        rw [fibonacci]
        ring1
  rw [complement]
  ring1

/-- Final clause of Exercise 2.2: if `xy≠-1`, the requested parameter is
exactly `(x-y)/(1+xy)`. -/
theorem twoPointSpreadNumber_eq_spreadParameter
    (x y : K) (xSquareNotNegativeOne : x ^ 2 ≠ -1)
    (ySquareNotNegativeOne : y ^ 2 ≠ -1)
    (productNotNegativeOne : x * y ≠ -1) :
    let parameter := twoPointSpreadParameter x y
    parameter ^ 2 ≠ -1 ∧
      twoPointSpreadNumber x y = spreadParameter parameter := by
  let numerator := x - y
  let productSum := 1 + x * y
  let denominator := (1 + x ^ 2) * (1 + y ^ 2)
  let parameter := twoPointSpreadParameter x y
  have productSumNonzero : productSum ≠ 0 := by
    intro productSumZero
    change 1 + x * y = 0 at productSumZero
    apply productNotNegativeOne
    calc
      x * y = (1 + x * y) - 1 := by ring1
      _ = -1 := by rw [productSumZero]; ring1
  have productSumCancel : productSum * productSum⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel productSum productSumNonzero
  have denominatorNonzero : denominator ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero
      (one_add_square_nonzero xSquareNotNegativeOne)
      (one_add_square_nonzero ySquareNotNegativeOne)
  have fibonacci :
      denominator = numerator ^ 2 + productSum ^ 2 := by
    unfold denominator numerator productSum
    ring1
  have parameterFormula : parameter = numerator * productSum⁻¹ := by
    unfold parameter twoPointSpreadParameter numerator productSum
    rw [RFAP.ExplicitField.div_eq_mul_inv]
  have parameterDenominatorTimesSquare :
      (1 + parameter ^ 2) * productSum ^ 2 = denominator := by
    rw [parameterFormula, fibonacci]
    calc
      (1 + (numerator * productSum⁻¹) ^ 2) * productSum ^ 2 =
          productSum ^ 2 +
            numerator ^ 2 * (productSum * productSum⁻¹) ^ 2 := by ring1
      _ = numerator ^ 2 + productSum ^ 2 := by
        rw [productSumCancel]
        ring1
  have parameterDenominatorNonzero : 1 + parameter ^ 2 ≠ 0 := by
    intro parameterDenominatorZero
    apply denominatorNonzero
    calc
      denominator = (1 + parameter ^ 2) * productSum ^ 2 :=
        parameterDenominatorTimesSquare.symm
      _ = 0 := by rw [parameterDenominatorZero]; ring1
  have parameterSquareNotNegativeOne : parameter ^ 2 ≠ -1 := by
    intro parameterSquareNegativeOne
    apply parameterDenominatorNonzero
    rw [parameterSquareNegativeOne]
    ring1
  refine ⟨parameterSquareNotNegativeOne, ?_⟩
  unfold twoPointSpreadNumber spreadParameter
  change numerator ^ 2 / denominator =
    parameter ^ 2 / (1 + parameter ^ 2)
  apply div_eq_div_of_cross_mul denominatorNonzero
    parameterDenominatorNonzero
  have crossDifference :
      numerator ^ 2 * (1 + parameter ^ 2) -
          parameter ^ 2 * denominator = 0 := by
    rw [parameterFormula, fibonacci]
    calc
      numerator ^ 2 * (1 + (numerator * productSum⁻¹) ^ 2) -
            (numerator * productSum⁻¹) ^ 2 *
              (numerator ^ 2 + productSum ^ 2) =
          numerator ^ 2 *
            (1 - (productSum * productSum⁻¹) ^ 2) := by ring1
      _ = 0 := by rw [productSumCancel]; ring1
  calc
    numerator ^ 2 * (1 + parameter ^ 2) =
        (numerator ^ 2 * (1 + parameter ^ 2) -
          parameter ^ 2 * denominator) + parameter ^ 2 * denominator := by
      ring1
    _ = parameter ^ 2 * denominator := by rw [crossDifference]; ring1

/-- Exercise 2.2 packaged with its universal spread witness and its requested
extra parameter when `xy≠-1`. -/
theorem exercise_2_2
    (x y : K) (xSquareNotNegativeOne : x ^ 2 ≠ -1)
    (ySquareNotNegativeOne : y ^ 2 ≠ -1) :
    IsSpreadNumber (twoPointSpreadNumber x y) ∧
      (x * y ≠ -1 →
        let parameter := twoPointSpreadParameter x y
        parameter ^ 2 ≠ -1 ∧
          twoPointSpreadNumber x y = spreadParameter parameter) := by
  exact ⟨twoPointSpreadNumber_isSpreadNumber x y
      xSquareNotNegativeOne ySquareNotNegativeOne,
    fun productNotNegativeOne =>
      twoPointSpreadNumber_eq_spreadParameter x y
        xSquareNotNegativeOne ySquareNotNegativeOne productNotNegativeOne⟩

end DivineProportions
