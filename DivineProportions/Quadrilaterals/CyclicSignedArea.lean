import DivineProportions.Circles.UnitCircle
import DivineProportions.Oriented.SignedArea

/-!
# Divine Proportions, Theorem 113: cyclic signed area

The source's unit-circle points are explicit finite coordinate pairs.  The
proof clears the product of their four certified denominators and computes
the shoelace sum.  No orientation quotient, square root, or completed circle
is introduced.
-/

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K]

namespace Quadrilateral

/-- The coordinate order used in Theorem 113:
`[2*lambda/(1+lambda^2), (1-lambda^2)/(1+lambda^2)]`. -/
def orientedUnitCirclePoint (parameter : K) : Point K :=
  ⟨(2 * parameter) / (1 + parameter ^ 2),
    (1 - parameter ^ 2) / (1 + parameter ^ 2)⟩

/-- The displayed point really lies on the unit circle. -/
theorem orientedUnitCirclePoint_contains [Nontrivial K]
    (parameter : K) (squareNotNegativeOne : parameter ^ 2 ≠ -1) :
    Conic.unitCircle.Contains (orientedUnitCirclePoint parameter) := by
  have originalOnCircle :=
    Conic.unitCirclePoint_contains parameter squareNotNegativeOne
  apply (Conic.unitCircle_contains_iff _).2
  have originalEquation :=
    (Conic.unitCircle_contains_iff (Conic.unitCirclePoint parameter)).1
      originalOnCircle
  change
    ((2 * parameter) / (1 + parameter ^ 2)) ^ 2 +
      ((1 - parameter ^ 2) / (1 + parameter ^ 2)) ^ 2 - 1 = 0
  calc
    ((2 * parameter) / (1 + parameter ^ 2)) ^ 2 +
          ((1 - parameter ^ 2) / (1 + parameter ^ 2)) ^ 2 - 1 =
        (Conic.unitCirclePoint parameter).x ^ 2 +
          (Conic.unitCirclePoint parameter).y ^ 2 - 1 := by
      unfold Conic.unitCirclePoint
      ring1
    _ = 0 := originalEquation

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

/-- The position determinant of two parametrized unit-circle points after
clearing their two denominators. -/
theorem orientedUnitCircle_positionDeterminant_cleared
    (left right : K)
    (leftSquareNotNegativeOne : left ^ 2 ≠ -1)
    (rightSquareNotNegativeOne : right ^ 2 ≠ -1) :
    positionDeterminant (orientedUnitCirclePoint left)
        (orientedUnitCirclePoint right) *
        ((1 + left ^ 2) * (1 + right ^ 2)) =
      (2 * left) * (1 - right ^ 2) -
        (2 * right) * (1 - left ^ 2) := by
  have leftDenominatorNonzero : 1 + left ^ 2 ≠ 0 :=
    (Conic.projectiveParameter_denominator_ne_zero_iff left).2
      leftSquareNotNegativeOne
  have rightDenominatorNonzero : 1 + right ^ 2 ≠ 0 :=
    (Conic.projectiveParameter_denominator_ne_zero_iff right).2
      rightSquareNotNegativeOne
  have leftXCancel :
      ((2 * left) / (1 + left ^ 2)) * (1 + left ^ 2) = 2 * left :=
    RFAP.ExplicitField.div_mul_cancel _ leftDenominatorNonzero
  have leftYCancel :
      ((1 - left ^ 2) / (1 + left ^ 2)) * (1 + left ^ 2) =
        1 - left ^ 2 :=
    RFAP.ExplicitField.div_mul_cancel _ leftDenominatorNonzero
  have rightXCancel :
      ((2 * right) / (1 + right ^ 2)) * (1 + right ^ 2) = 2 * right :=
    RFAP.ExplicitField.div_mul_cancel _ rightDenominatorNonzero
  have rightYCancel :
      ((1 - right ^ 2) / (1 + right ^ 2)) * (1 + right ^ 2) =
        1 - right ^ 2 :=
    RFAP.ExplicitField.div_mul_cancel _ rightDenominatorNonzero
  unfold positionDeterminant orientedUnitCirclePoint
  dsimp only
  calc
    (((2 * left) / (1 + left ^ 2)) *
          ((1 - right ^ 2) / (1 + right ^ 2)) -
        ((2 * right) / (1 + right ^ 2)) *
          ((1 - left ^ 2) / (1 + left ^ 2))) *
          ((1 + left ^ 2) * (1 + right ^ 2)) =
      (((2 * left) / (1 + left ^ 2)) * (1 + left ^ 2)) *
          (((1 - right ^ 2) / (1 + right ^ 2)) *
            (1 + right ^ 2)) -
        (((2 * right) / (1 + right ^ 2)) * (1 + right ^ 2)) *
          (((1 - left ^ 2) / (1 + left ^ 2)) *
            (1 + left ^ 2)) := by ring1
    _ = (2 * left) * (1 - right ^ 2) -
        (2 * right) * (1 - left ^ 2) := by
      rw [leftXCancel, rightYCancel, rightXCancel, leftYCancel]

/-- The antisymmetric numerator printed in Theorem 113. -/
def cyclicSignedAreaNumerator (parameter₁ parameter₂ parameter₃ parameter₄ : K) : K :=
  2 * (parameter₁ - parameter₃) * (parameter₂ - parameter₄) *
    (parameter₁ + parameter₃ - parameter₂ - parameter₄ +
      parameter₁ * parameter₂ * parameter₃ + parameter₁ * parameter₃ * parameter₄ -
      parameter₂ * parameter₃ * parameter₄ - parameter₁ * parameter₂ * parameter₄)

/-- The product of the four unit-circle chart denominators. -/
def cyclicSignedAreaDenominator (parameter₁ parameter₂ parameter₃ parameter₄ : K) : K :=
  (1 + parameter₁ ^ 2) * (1 + parameter₂ ^ 2) *
    (1 + parameter₃ ^ 2) * (1 + parameter₄ ^ 2)

/-- Theorem 113 (Cyclic signed area), with every chart denominator and the
signed-area normalization certified nonzero. -/
theorem cyclic_signed_area
    (parameter₁ parameter₂ parameter₃ parameter₄ : K)
    (parameter₁SquareNotNegativeOne : parameter₁ ^ 2 ≠ -1)
    (parameter₂SquareNotNegativeOne : parameter₂ ^ 2 ≠ -1)
    (parameter₃SquareNotNegativeOne : parameter₃ ^ 2 ≠ -1)
    (parameter₄SquareNotNegativeOne : parameter₄ ^ 2 ≠ -1)
    (twoNonzero : (2 : K) ≠ 0) :
    polygonSignedArea
        [orientedUnitCirclePoint parameter₁, orientedUnitCirclePoint parameter₂,
          orientedUnitCirclePoint parameter₃, orientedUnitCirclePoint parameter₄] =
      cyclicSignedAreaNumerator parameter₁ parameter₂ parameter₃ parameter₄ /
        cyclicSignedAreaDenominator parameter₁ parameter₂ parameter₃ parameter₄ := by
  let d₁ := 1 + parameter₁ ^ 2
  let d₂ := 1 + parameter₂ ^ 2
  let d₃ := 1 + parameter₃ ^ 2
  let d₄ := 1 + parameter₄ ^ 2
  let denominator := d₁ * d₂ * d₃ * d₄
  let doubleArea := polygonDoubleSignedArea
    [orientedUnitCirclePoint parameter₁, orientedUnitCirclePoint parameter₂,
      orientedUnitCirclePoint parameter₃, orientedUnitCirclePoint parameter₄]
  let numerator := cyclicSignedAreaNumerator parameter₁ parameter₂ parameter₃ parameter₄
  have d₁Nonzero : d₁ ≠ 0 :=
    (Conic.projectiveParameter_denominator_ne_zero_iff parameter₁).2
      parameter₁SquareNotNegativeOne
  have d₂Nonzero : d₂ ≠ 0 :=
    (Conic.projectiveParameter_denominator_ne_zero_iff parameter₂).2
      parameter₂SquareNotNegativeOne
  have d₃Nonzero : d₃ ≠ 0 :=
    (Conic.projectiveParameter_denominator_ne_zero_iff parameter₃).2
      parameter₃SquareNotNegativeOne
  have d₄Nonzero : d₄ ≠ 0 :=
    (Conic.projectiveParameter_denominator_ne_zero_iff parameter₄).2
      parameter₄SquareNotNegativeOne
  have denominatorNonzero : denominator ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero
      (RFAP.ExplicitField.mul_ne_zero
        (RFAP.ExplicitField.mul_ne_zero d₁Nonzero d₂Nonzero) d₃Nonzero)
      d₄Nonzero
  have firstEdge := orientedUnitCircle_positionDeterminant_cleared parameter₁ parameter₂
    parameter₁SquareNotNegativeOne parameter₂SquareNotNegativeOne
  have secondEdge := orientedUnitCircle_positionDeterminant_cleared parameter₂ parameter₃
    parameter₂SquareNotNegativeOne parameter₃SquareNotNegativeOne
  have thirdEdge := orientedUnitCircle_positionDeterminant_cleared parameter₃ parameter₄
    parameter₃SquareNotNegativeOne parameter₄SquareNotNegativeOne
  have fourthEdge := orientedUnitCircle_positionDeterminant_cleared parameter₄ parameter₁
    parameter₄SquareNotNegativeOne parameter₁SquareNotNegativeOne
  change positionDeterminant (orientedUnitCirclePoint parameter₁)
      (orientedUnitCirclePoint parameter₂) * (d₁ * d₂) =
        (2 * parameter₁) * (1 - parameter₂ ^ 2) -
          (2 * parameter₂) * (1 - parameter₁ ^ 2) at firstEdge
  change positionDeterminant (orientedUnitCirclePoint parameter₂)
      (orientedUnitCirclePoint parameter₃) * (d₂ * d₃) =
        (2 * parameter₂) * (1 - parameter₃ ^ 2) -
          (2 * parameter₃) * (1 - parameter₂ ^ 2) at secondEdge
  change positionDeterminant (orientedUnitCirclePoint parameter₃)
      (orientedUnitCirclePoint parameter₄) * (d₃ * d₄) =
        (2 * parameter₃) * (1 - parameter₄ ^ 2) -
          (2 * parameter₄) * (1 - parameter₃ ^ 2) at thirdEdge
  change positionDeterminant (orientedUnitCirclePoint parameter₄)
      (orientedUnitCirclePoint parameter₁) * (d₄ * d₁) =
        (2 * parameter₄) * (1 - parameter₁ ^ 2) -
          (2 * parameter₁) * (1 - parameter₄ ^ 2) at fourthEdge
  have doubleAreaScaled : doubleArea * denominator = 2 * numerator := by
    calc
      doubleArea * denominator =
          (positionDeterminant (orientedUnitCirclePoint parameter₁)
              (orientedUnitCirclePoint parameter₂) * (d₁ * d₂)) * (d₃ * d₄) +
            (positionDeterminant (orientedUnitCirclePoint parameter₂)
              (orientedUnitCirclePoint parameter₃) * (d₂ * d₃)) * (d₁ * d₄) +
            (positionDeterminant (orientedUnitCirclePoint parameter₃)
              (orientedUnitCirclePoint parameter₄) * (d₃ * d₄)) * (d₁ * d₂) +
            (positionDeterminant (orientedUnitCirclePoint parameter₄)
              (orientedUnitCirclePoint parameter₁) * (d₄ * d₁)) * (d₂ * d₃) := by
        simp only [doubleArea, polygonDoubleSignedArea,
          polygonDoubleSignedAreaAux]
        unfold denominator
        ring1
      _ = 2 * numerator := by
        rw [firstEdge, secondEdge, thirdEdge, fourthEdge]
        unfold numerator cyclicSignedAreaNumerator d₁ d₂ d₃ d₄
        ring1
  have twoDenominatorNonzero : 2 * denominator ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero twoNonzero denominatorNonzero
  have doubleAreaTwoCancel : (doubleArea / 2) * 2 = doubleArea :=
    RFAP.ExplicitField.div_mul_cancel doubleArea twoNonzero
  have numeratorDenominatorCancel :
      (numerator / denominator) * denominator = numerator :=
    RFAP.ExplicitField.div_mul_cancel numerator denominatorNonzero
  apply eq_of_mul_eq_mul_right twoDenominatorNonzero
  calc
    polygonSignedArea
          [orientedUnitCirclePoint parameter₁, orientedUnitCirclePoint parameter₂,
            orientedUnitCirclePoint parameter₃, orientedUnitCirclePoint parameter₄] *
        (2 * denominator) = doubleArea * denominator := by
      unfold polygonSignedArea doubleArea
      calc
        (polygonDoubleSignedArea
              [orientedUnitCirclePoint parameter₁,
                orientedUnitCirclePoint parameter₂,
                orientedUnitCirclePoint parameter₃,
                orientedUnitCirclePoint parameter₄] / 2) *
            (2 * denominator) =
          ((polygonDoubleSignedArea
              [orientedUnitCirclePoint parameter₁,
                orientedUnitCirclePoint parameter₂,
                orientedUnitCirclePoint parameter₃,
                orientedUnitCirclePoint parameter₄] / 2) * 2) *
            denominator := by ring1
        _ = polygonDoubleSignedArea
              [orientedUnitCirclePoint parameter₁,
                orientedUnitCirclePoint parameter₂,
                orientedUnitCirclePoint parameter₃,
                orientedUnitCirclePoint parameter₄] * denominator := by
          rw [doubleAreaTwoCancel]
    _ = 2 * numerator := doubleAreaScaled
    _ = (numerator / denominator) * (2 * denominator) := by
      calc
        2 * numerator = 2 * ((numerator / denominator) * denominator) := by
          rw [numeratorDenominatorCancel]
        _ = (numerator / denominator) * (2 * denominator) := by ring1
    _ = (cyclicSignedAreaNumerator parameter₁ parameter₂ parameter₃ parameter₄ /
        cyclicSignedAreaDenominator parameter₁ parameter₂ parameter₃ parameter₄) *
          (2 * denominator) := by
      unfold numerator denominator cyclicSignedAreaDenominator d₁ d₂ d₃ d₄
      rfl

/-- Exercise 17.2: repeating the third point as the fourth reduces the
quadrilateral formula to the printed oriented-triangle signed area. -/
theorem exercise_17_2
    (parameter₁ parameter₂ parameter₃ : K)
    (parameter₁SquareNotNegativeOne : parameter₁ ^ 2 ≠ -1)
    (parameter₂SquareNotNegativeOne : parameter₂ ^ 2 ≠ -1)
    (parameter₃SquareNotNegativeOne : parameter₃ ^ 2 ≠ -1)
    (twoNonzero : (2 : K) ≠ 0) :
    triangleSignedArea (orientedUnitCirclePoint parameter₁)
        (orientedUnitCirclePoint parameter₂) (orientedUnitCirclePoint parameter₃) =
      (2 * (parameter₁ - parameter₂) * (parameter₂ - parameter₃) * (parameter₁ - parameter₃)) /
        ((1 + parameter₁ ^ 2) * (1 + parameter₂ ^ 2) * (1 + parameter₃ ^ 2)) := by
  let d₁ := 1 + parameter₁ ^ 2
  let d₂ := 1 + parameter₂ ^ 2
  let d₃ := 1 + parameter₃ ^ 2
  let shortDenominator := d₁ * d₂ * d₃
  let longDenominator := shortDenominator * d₃
  have d₁Nonzero : d₁ ≠ 0 :=
    (Conic.projectiveParameter_denominator_ne_zero_iff parameter₁).2
      parameter₁SquareNotNegativeOne
  have d₂Nonzero : d₂ ≠ 0 :=
    (Conic.projectiveParameter_denominator_ne_zero_iff parameter₂).2
      parameter₂SquareNotNegativeOne
  have d₃Nonzero : d₃ ≠ 0 :=
    (Conic.projectiveParameter_denominator_ne_zero_iff parameter₃).2
      parameter₃SquareNotNegativeOne
  have shortDenominatorNonzero : shortDenominator ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero
      (RFAP.ExplicitField.mul_ne_zero d₁Nonzero d₂Nonzero) d₃Nonzero
  have longDenominatorNonzero : longDenominator ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero shortDenominatorNonzero d₃Nonzero
  have quadrilateralFormula := cyclic_signed_area parameter₁ parameter₂ parameter₃ parameter₃
    parameter₁SquareNotNegativeOne parameter₂SquareNotNegativeOne
    parameter₃SquareNotNegativeOne parameter₃SquareNotNegativeOne twoNonzero
  have repeatedPointArea :
      polygonSignedArea
          [orientedUnitCirclePoint parameter₁, orientedUnitCirclePoint parameter₂,
            orientedUnitCirclePoint parameter₃, orientedUnitCirclePoint parameter₃] =
        triangleSignedArea (orientedUnitCirclePoint parameter₁)
          (orientedUnitCirclePoint parameter₂) (orientedUnitCirclePoint parameter₃) := by
    unfold polygonSignedArea triangleSignedArea
    congr 1
    simp only [polygonDoubleSignedArea, polygonDoubleSignedAreaAux]
    unfold triangleDoubleSignedArea
    unfold positionDeterminant
    ring1
  rw [repeatedPointArea] at quadrilateralFormula
  change triangleSignedArea (orientedUnitCirclePoint parameter₁)
      (orientedUnitCirclePoint parameter₂) (orientedUnitCirclePoint parameter₃) =
    cyclicSignedAreaNumerator parameter₁ parameter₂ parameter₃ parameter₃ /
      longDenominator at quadrilateralFormula
  have shortCancel :
      ((2 * (parameter₁ - parameter₂) * (parameter₂ - parameter₃) *
          (parameter₁ - parameter₃)) / shortDenominator) *
        shortDenominator =
      2 * (parameter₁ - parameter₂) * (parameter₂ - parameter₃) *
        (parameter₁ - parameter₃) :=
    RFAP.ExplicitField.div_mul_cancel _ shortDenominatorNonzero
  calc
    triangleSignedArea (orientedUnitCirclePoint parameter₁)
        (orientedUnitCirclePoint parameter₂) (orientedUnitCirclePoint parameter₃) =
      cyclicSignedAreaNumerator parameter₁ parameter₂ parameter₃ parameter₃ / longDenominator :=
        quadrilateralFormula
    _ = (2 * (parameter₁ - parameter₂) * (parameter₂ - parameter₃) * (parameter₁ - parameter₃)) /
        shortDenominator := by
      apply eq_of_mul_eq_mul_right longDenominatorNonzero
      calc
        (cyclicSignedAreaNumerator parameter₁ parameter₂ parameter₃ parameter₃ / longDenominator) *
            longDenominator = cyclicSignedAreaNumerator parameter₁ parameter₂ parameter₃ parameter₃ :=
          RFAP.ExplicitField.div_mul_cancel _ longDenominatorNonzero
        _ = 2 * (parameter₁ - parameter₂) * (parameter₂ - parameter₃) * (parameter₁ - parameter₃) * d₃ := by
          unfold cyclicSignedAreaNumerator d₃
          ring1
        _ = ((2 * (parameter₁ - parameter₂) * (parameter₂ - parameter₃) * (parameter₁ - parameter₃)) /
              shortDenominator) * longDenominator := by
          calc
            2 * (parameter₁ - parameter₂) * (parameter₂ - parameter₃) *
                (parameter₁ - parameter₃) * d₃ =
              (((2 * (parameter₁ - parameter₂) * (parameter₂ - parameter₃) *
                  (parameter₁ - parameter₃)) / shortDenominator) *
                shortDenominator) * d₃ := by rw [shortCancel]
            _ = ((2 * (parameter₁ - parameter₂) * (parameter₂ - parameter₃) *
                  (parameter₁ - parameter₃)) / shortDenominator) *
                longDenominator := by unfold longDenominator; ring1
    _ = (2 * (parameter₁ - parameter₂) * (parameter₂ - parameter₃) * (parameter₁ - parameter₃)) /
        ((1 + parameter₁ ^ 2) * (1 + parameter₂ ^ 2) * (1 + parameter₃ ^ 2)) := by
      rfl

end Quadrilateral

end DivineProportions
