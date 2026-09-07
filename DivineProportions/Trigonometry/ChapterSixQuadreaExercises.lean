import DivineProportions.Trigonometry.TriangleRatios
import mathlib.RFAP.ConstructiveFraction

/-!
# Divine Proportions, Exercises 6.3--6.6

The common spread ratio and the two null-triangle formulas are finite
consequences of the Quadrea-spread identity.  The rational triangle inequality
is the statement that the coordinate-determinant square is nonnegative; no
absolute value, square root, compactness, or extremum is introduced.
-/

namespace DivineProportions

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

private theorem four_ne_zero (twoNonzero : (2 : K) ≠ 0) : (4 : K) ≠ 0 := by
  have fourAsProduct : (4 : K) = 2 * 2 := by ring1
  rw [fourAsProduct]
  exact RFAP.ExplicitField.mul_ne_zero twoNonzero twoNonzero

/-- Exercise 6.3 in its finite scalar form.  The three hypotheses are exactly
the cyclic conclusions of the Quadrea-spread theorem. -/
theorem exercise_6_3
    (q₁ q₂ q₃ s₁ s₂ s₃ area : K)
    (twoNonzero : (2 : K) ≠ 0)
    (q₁Nonzero : q₁ ≠ 0) (q₂Nonzero : q₂ ≠ 0)
    (q₃Nonzero : q₃ ≠ 0)
    (areaAtFirst : area = 4 * q₂ * q₃ * s₁)
    (areaAtSecond : area = 4 * q₁ * q₃ * s₂)
    (areaAtThird : area = 4 * q₁ * q₂ * s₃) :
    s₁ / q₁ = s₂ / q₂ ∧
      s₂ / q₂ = s₃ / q₃ ∧
      s₃ / q₃ = area / (4 * q₁ * q₂ * q₃) := by
  have fourNonzero := four_ne_zero twoNonzero
  have denominatorNonzero : 4 * q₁ * q₂ * q₃ ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero
      (RFAP.ExplicitField.mul_ne_zero
        (RFAP.ExplicitField.mul_ne_zero fourNonzero q₁Nonzero)
        q₂Nonzero)
      q₃Nonzero
  have firstCommon :
      s₁ / q₁ = area / (4 * q₁ * q₂ * q₃) := by
    apply div_eq_div_of_cross_mul q₁Nonzero denominatorNonzero
    rw [areaAtFirst]
    ring1
  have secondCommon :
      s₂ / q₂ = area / (4 * q₁ * q₂ * q₃) := by
    apply div_eq_div_of_cross_mul q₂Nonzero denominatorNonzero
    rw [areaAtSecond]
    ring1
  have thirdCommon :
      s₃ / q₃ = area / (4 * q₁ * q₂ * q₃) := by
    apply div_eq_div_of_cross_mul q₃Nonzero denominatorNonzero
    rw [areaAtThird]
    ring1
  exact ⟨firstCommon.trans secondCommon.symm,
    secondCommon.trans thirdCommon.symm, thirdCommon⟩

/-- First clause of Exercise 6.4: setting the null-side quadrance to zero
reduces quadrea to the negative square `-(q₁-q₂)²`. -/
theorem exercise_6_4_quadrea (q₁ q₂ : K) :
    archimedesFunction q₁ q₂ 0 = -(q₁ - q₂) ^ 2 := by
  unfold archimedesFunction
  ring1

/-- Exercise 6.4: the Quadrea-spread equation for a null-side triangle gives
the exact displayed third spread. -/
theorem exercise_6_4
    (q₁ q₂ s₃ : K) (twoNonzero : (2 : K) ≠ 0)
    (q₁Nonzero : q₁ ≠ 0) (q₂Nonzero : q₂ ≠ 0)
    (areaSpread : archimedesFunction q₁ q₂ 0 = 4 * q₁ * q₂ * s₃) :
    archimedesFunction q₁ q₂ 0 = -(q₁ - q₂) ^ 2 ∧
      s₃ = -(q₁ - q₂) ^ 2 / (4 * q₁ * q₂) := by
  have fourNonzero := four_ne_zero twoNonzero
  have denominatorNonzero : 4 * q₁ * q₂ ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero
      (RFAP.ExplicitField.mul_ne_zero fourNonzero q₁Nonzero)
      q₂Nonzero
  have areaFormula := exercise_6_4_quadrea q₁ q₂
  refine ⟨areaFormula, ?_⟩
  apply eq_of_mul_eq_mul_right denominatorNonzero
  calc
    s₃ * (4 * q₁ * q₂) = 4 * q₁ * q₂ * s₃ := by ring1
    _ = archimedesFunction q₁ q₂ 0 := areaSpread.symm
    _ = -(q₁ - q₂) ^ 2 := areaFormula
    _ = (-(q₁ - q₂) ^ 2 / (4 * q₁ * q₂)) *
        (4 * q₁ * q₂) :=
      (RFAP.ExplicitField.div_mul_cancel _ denominatorNonzero).symm

/-- Exercise 6.5: if the other two quadrances vanish, quadrea is `-q₁²`.
The source's premise `q₁≠0` is unnecessary for this polynomial identity. -/
theorem exercise_6_5 (q₁ : K) :
    archimedesFunction q₁ 0 0 = -q₁ ^ 2 := by
  unfold archimedesFunction
  ring1

namespace ExerciseSixSix

abbrev Rational := RFAP.ConstructiveFraction.Rational

/-- Exercise 6.6 (Triangle inequality): for any three constructive-rational
points, the Cross-law square is at most `4Q₁Q₂`. -/
theorem exercise_6_6 (first second third : Point Rational) :
    (quadrance second third + quadrance first third -
        quadrance first second) ^ 2 ≤
      4 * quadrance second third * quadrance first third := by
  have fourNonnegative : (0 : Rational) ≤ 4 := by decide
  have determinantSquareNonnegative :
      (0 : Rational) ≤ pointDeterminant first second third ^ 2 :=
    RFAP.ConstructiveFraction.sq_nonneg_direct _
  have areaNonnegative : (0 : Rational) ≤ quadrea first second third := by
    rw [quadrea_coordinate_formula]
    exact RFAP.ConstructiveFraction.mul_nonneg_direct
      fourNonnegative determinantSquareNonnegative
  apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
  calc
    (0 : Rational) ≤ quadrea first second third := areaNonnegative
    _ = 4 * quadrance second third * quadrance first third -
        (quadrance second third + quadrance first third -
          quadrance first second) ^ 2 := by
            unfold quadrea archimedesFunction
            ring1

end ExerciseSixSix

end DivineProportions
