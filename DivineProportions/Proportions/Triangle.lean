import mathlib.Tactic.QuotientFreeRing
import DivineProportions.Trigonometry.TriangleRatios

/-!
# Divine Proportions, Chapter 11: triangle proportions

The denominator-free theorem records exactly the three cross-products supplied
by the Spread law.  The printed quotient chain is then recovered only from its
visible nonzero denominators.  This separation keeps the result meaningful in
finite fields even when a displayed quotient would be undefined geometrically.
-/

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K]

/-- Equal cross-products with nonzero displayed denominators give equal
ratios. -/
theorem ratio_eq_of_cross_product
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

/-- Equal ratios with nonzero displayed denominators give equal
cross-products. -/
theorem cross_product_of_ratio_eq
    {leftNumerator rightNumerator leftDenominator rightDenominator : K}
    (leftNonzero : leftDenominator ≠ 0)
    (rightNonzero : rightDenominator ≠ 0)
    (equalRatios :
      leftNumerator / leftDenominator =
        rightNumerator / rightDenominator) :
    leftNumerator * rightDenominator =
      rightNumerator * leftDenominator := by
  calc
    leftNumerator * rightDenominator =
        ((leftNumerator / leftDenominator) * leftDenominator) *
          rightDenominator := by
      rw [RFAP.ExplicitField.div_mul_cancel leftNumerator leftNonzero]
    _ = (leftNumerator / leftDenominator) *
        (leftDenominator * rightDenominator) := by ring1
    _ = (rightNumerator / rightDenominator) *
        (leftDenominator * rightDenominator) := by rw [equalRatios]
    _ = ((rightNumerator / rightDenominator) * rightDenominator) *
        leftDenominator := by ring1
    _ = rightNumerator * leftDenominator := by
      rw [RFAP.ExplicitField.div_mul_cancel rightNumerator rightNonzero]

/-- Denominator-free core of Theorem 72.  The three hypotheses are the cleared
Spread-law proportions in `DA₁A₃`, `DA₂A₃`, and `A₁A₂A₃` respectively. -/
theorem triangle_proportions_cleared
    (r₁ r₂ s₁ s₂ q₁ q₂ R₁ R₂ R₃ : K)
    (firstSubtriangle : s₁ * R₁ = r₁ * R₃)
    (secondSubtriangle : s₂ * R₂ = r₂ * R₃)
    (originalTriangle : s₁ * q₂ = s₂ * q₁) :
    r₁ * (s₂ * R₂) = (s₁ * R₁) * r₂ ∧
      (s₁ * R₁) * (q₂ * R₂) = (q₁ * R₁) * (s₂ * R₂) := by
  constructor
  · calc
      r₁ * (s₂ * R₂) = r₁ * (r₂ * R₃) := by rw [secondSubtriangle]
      _ = (r₁ * R₃) * r₂ := by ring1
      _ = (s₁ * R₁) * r₂ := by rw [firstSubtriangle]
  · calc
      (s₁ * R₁) * (q₂ * R₂) =
          (s₁ * q₂) * (R₁ * R₂) := by ring1
      _ = (s₂ * q₁) * (R₁ * R₂) := by rw [originalTriangle]
      _ = (q₁ * R₁) * (s₂ * R₂) := by ring1

/-- Theorem 72 (Triangle proportions), in the exact printed quotient form:
`r₁/r₂ = s₁R₁/(s₂R₂) = q₁R₁/(q₂R₂)`. -/
theorem triangle_proportions
    (r₁ r₂ s₁ s₂ q₁ q₂ R₁ R₂ R₃ : K)
    (r₂Nonzero : r₂ ≠ 0) (s₂Nonzero : s₂ ≠ 0)
    (q₂Nonzero : q₂ ≠ 0) (R₂Nonzero : R₂ ≠ 0)
    (firstSubtriangle : s₁ * R₁ = r₁ * R₃)
    (secondSubtriangle : s₂ * R₂ = r₂ * R₃)
    (originalTriangle : s₁ * q₂ = s₂ * q₁) :
    r₁ / r₂ = (s₁ * R₁) / (s₂ * R₂) ∧
      (s₁ * R₁) / (s₂ * R₂) = (q₁ * R₁) / (q₂ * R₂) := by
  have s₂R₂Nonzero : s₂ * R₂ ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero s₂Nonzero R₂Nonzero
  have q₂R₂Nonzero : q₂ * R₂ ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero q₂Nonzero R₂Nonzero
  rcases triangle_proportions_cleared r₁ r₂ s₁ s₂ q₁ q₂ R₁ R₂ R₃
    firstSubtriangle secondSubtriangle originalTriangle with
    ⟨firstCrossProduct, secondCrossProduct⟩
  exact ⟨ratio_eq_of_cross_product r₂Nonzero s₂R₂Nonzero
      firstCrossProduct,
    ratio_eq_of_cross_product s₂R₂Nonzero q₂R₂Nonzero
      secondCrossProduct⟩

/-- The book's proof interface: each premise is one of the three quotient
equalities read directly from the corresponding application of the Spread
law. -/
theorem triangle_proportions_of_spread_laws
    (r₁ r₂ s₁ s₂ q₁ q₂ R₁ R₂ R₃ : K)
    (r₂Nonzero : r₂ ≠ 0) (s₂Nonzero : s₂ ≠ 0)
    (q₁Nonzero : q₁ ≠ 0) (q₂Nonzero : q₂ ≠ 0)
    (R₁Nonzero : R₁ ≠ 0) (R₂Nonzero : R₂ ≠ 0)
    (R₃Nonzero : R₃ ≠ 0)
    (firstSubtriangle : s₁ / R₃ = r₁ / R₁)
    (secondSubtriangle : s₂ / R₃ = r₂ / R₂)
    (originalTriangle : s₁ / q₁ = s₂ / q₂) :
    r₁ / r₂ = (s₁ * R₁) / (s₂ * R₂) ∧
      (s₁ * R₁) / (s₂ * R₂) = (q₁ * R₁) / (q₂ * R₂) := by
  have firstCleared : s₁ * R₁ = r₁ * R₃ :=
    cross_product_of_ratio_eq R₃Nonzero R₁Nonzero firstSubtriangle
  have secondCleared : s₂ * R₂ = r₂ * R₃ :=
    cross_product_of_ratio_eq R₃Nonzero R₂Nonzero secondSubtriangle
  have originalCleared : s₁ * q₂ = s₂ * q₁ :=
    cross_product_of_ratio_eq q₁Nonzero q₂Nonzero originalTriangle
  exact triangle_proportions r₁ r₂ s₁ s₂ q₁ q₂ R₁ R₂ R₃
    r₂Nonzero s₂Nonzero q₂Nonzero R₂Nonzero firstCleared
    secondCleared originalCleared

end DivineProportions
