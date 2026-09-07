import mathlib.Tactic.QuotientFreeRing
import DivineProportions.Proportions.Median

/-!
# Divine Proportions, Chapter 11: Menelaus and Ceva

The cyclic arguments are stated first as product identities retaining the
common spread factor.  The geometric nonparallel hypotheses supply explicit
nonzero certificates exactly where the printed conclusions cancel that factor.
-/

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K]

private theorem eq_of_mul_eq_mul_right
    {left right factor : K} (factorNonzero : factor ≠ 0)
    (productsEqual : left * factor = right * factor) : left = right := by
  have factorCancel : factor * factor⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel factor factorNonzero
  calc
    left = left * 1 := by rw [mul_one]
    _ = left * (factor * factor⁻¹) := by rw [factorCancel]
    _ = (left * factor) * factor⁻¹ := by ring1
    _ = (right * factor) * factor⁻¹ := by rw [productsEqual]
    _ = right * (factor * factor⁻¹) := by ring1
    _ = right := by rw [factorCancel, mul_one]

/-- Denominator-free cyclic product at the core of Menelaus' theorem.  The
three hypotheses are the cleared forms of
`r₁/r₂=R₂/P₁`, `r₂/r₃=R₃/P₂`, and `r₃/r₁=R₁/P₃`. -/
theorem menelaus_cleared
    (r₁ r₂ r₃ R₁ R₂ R₃ P₁ P₂ P₃ : K)
    (firstRatio : r₁ * P₁ = R₂ * r₂)
    (secondRatio : r₂ * P₂ = R₃ * r₃)
    (thirdRatio : r₃ * P₃ = R₁ * r₁) :
    (R₁ * R₂ * R₃) * (r₁ * r₂ * r₃) =
      (P₁ * P₂ * P₃) * (r₁ * r₂ * r₃) := by
  calc
    (R₁ * R₂ * R₃) * (r₁ * r₂ * r₃) =
        (R₁ * r₁) * (R₂ * r₂) * (R₃ * r₃) := by ring1
    _ = (r₃ * P₃) * (r₁ * P₁) * (r₂ * P₂) := by
      rw [← firstRatio, ← secondRatio, ← thirdRatio]
    _ = (P₁ * P₂ * P₃) * (r₁ * r₂ * r₃) := by ring1

/-- Theorem 78 (Menelaus), in the exact quadrance-product form. -/
theorem menelaus
    (r₁ r₂ r₃ R₁ R₂ R₃ P₁ P₂ P₃ : K)
    (r₁Nonzero : r₁ ≠ 0) (r₂Nonzero : r₂ ≠ 0)
    (r₃Nonzero : r₃ ≠ 0)
    (firstRatio : r₁ * P₁ = R₂ * r₂)
    (secondRatio : r₂ * P₂ = R₃ * r₃)
    (thirdRatio : r₃ * P₃ = R₁ * r₁) :
    R₁ * R₂ * R₃ = P₁ * P₂ * P₃ := by
  have firstPairNonzero :=
    RFAP.ExplicitField.mul_ne_zero r₁Nonzero r₂Nonzero
  have spreadProductNonzero : r₁ * r₂ * r₃ ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero firstPairNonzero r₃Nonzero
  apply eq_of_mul_eq_mul_right spreadProductNonzero
  exact menelaus_cleared r₁ r₂ r₃ R₁ R₂ R₃ P₁ P₂ P₃
    firstRatio secondRatio thirdRatio

/-- The book-proof interface taking the three cyclic quotient equalities
directly from the Spread law. -/
theorem menelaus_of_spread_laws
    (r₁ r₂ r₃ R₁ R₂ R₃ P₁ P₂ P₃ : K)
    (r₁Nonzero : r₁ ≠ 0) (r₂Nonzero : r₂ ≠ 0)
    (r₃Nonzero : r₃ ≠ 0)
    (P₁Nonzero : P₁ ≠ 0) (P₂Nonzero : P₂ ≠ 0)
    (P₃Nonzero : P₃ ≠ 0)
    (firstRatio : r₁ / r₂ = R₂ / P₁)
    (secondRatio : r₂ / r₃ = R₃ / P₂)
    (thirdRatio : r₃ / r₁ = R₁ / P₃) :
    R₁ * R₂ * R₃ = P₁ * P₂ * P₃ := by
  have firstCleared := cross_product_of_ratio_eq r₂Nonzero P₁Nonzero
    firstRatio
  have secondCleared := cross_product_of_ratio_eq r₃Nonzero P₂Nonzero
    secondRatio
  have thirdCleared := cross_product_of_ratio_eq r₁Nonzero P₃Nonzero
    thirdRatio
  exact menelaus r₁ r₂ r₃ R₁ R₂ R₃ P₁ P₂ P₃
    r₁Nonzero r₂Nonzero r₃Nonzero firstCleared secondCleared thirdCleared

/-- Denominator-free cyclic product at the core of Theorem 79.  The hypotheses
are the cleared forms of `r₂/p₃=N₃/N₂`, `r₃/p₁=N₁/N₃`, and
`r₁/p₂=N₂/N₁`. -/
theorem alternate_spreads_cleared
    (r₁ r₂ r₃ p₁ p₂ p₃ N₁ N₂ N₃ : K)
    (firstRatio : r₂ * N₂ = N₃ * p₃)
    (secondRatio : r₃ * N₃ = N₁ * p₁)
    (thirdRatio : r₁ * N₁ = N₂ * p₂) :
    (r₁ * r₂ * r₃) * (N₁ * N₂ * N₃) =
      (p₁ * p₂ * p₃) * (N₁ * N₂ * N₃) := by
  calc
    (r₁ * r₂ * r₃) * (N₁ * N₂ * N₃) =
        (r₂ * N₂) * (r₃ * N₃) * (r₁ * N₁) := by ring1
    _ = (N₃ * p₃) * (N₁ * p₁) * (N₂ * p₂) := by
      rw [firstRatio, secondRatio, thirdRatio]
    _ = (p₁ * p₂ * p₃) * (N₁ * N₂ * N₃) := by ring1

/-- Theorem 79 (Alternate spreads). -/
theorem alternate_spreads
    (r₁ r₂ r₃ p₁ p₂ p₃ N₁ N₂ N₃ : K)
    (N₁Nonzero : N₁ ≠ 0) (N₂Nonzero : N₂ ≠ 0)
    (N₃Nonzero : N₃ ≠ 0)
    (firstRatio : r₂ * N₂ = N₃ * p₃)
    (secondRatio : r₃ * N₃ = N₁ * p₁)
    (thirdRatio : r₁ * N₁ = N₂ * p₂) :
    r₁ * r₂ * r₃ = p₁ * p₂ * p₃ := by
  have firstPairNonzero :=
    RFAP.ExplicitField.mul_ne_zero N₁Nonzero N₂Nonzero
  have quadranceProductNonzero : N₁ * N₂ * N₃ ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero firstPairNonzero N₃Nonzero
  apply eq_of_mul_eq_mul_right quadranceProductNonzero
  exact alternate_spreads_cleared r₁ r₂ r₃ p₁ p₂ p₃ N₁ N₂ N₃
    firstRatio secondRatio thirdRatio

/-- The book-proof interface taking the three cyclic Spread-law ratios. -/
theorem alternate_spreads_of_spread_laws
    (r₁ r₂ r₃ p₁ p₂ p₃ N₁ N₂ N₃ : K)
    (p₁Nonzero : p₁ ≠ 0) (p₂Nonzero : p₂ ≠ 0)
    (p₃Nonzero : p₃ ≠ 0)
    (N₁Nonzero : N₁ ≠ 0) (N₂Nonzero : N₂ ≠ 0)
    (N₃Nonzero : N₃ ≠ 0)
    (firstRatio : r₂ / p₃ = N₃ / N₂)
    (secondRatio : r₃ / p₁ = N₁ / N₃)
    (thirdRatio : r₁ / p₂ = N₂ / N₁) :
    r₁ * r₂ * r₃ = p₁ * p₂ * p₃ := by
  have firstCleared := cross_product_of_ratio_eq p₃Nonzero N₂Nonzero
    firstRatio
  have secondCleared := cross_product_of_ratio_eq p₁Nonzero N₃Nonzero
    secondRatio
  have thirdCleared := cross_product_of_ratio_eq p₂Nonzero N₁Nonzero
    thirdRatio
  exact alternate_spreads r₁ r₂ r₃ p₁ p₂ p₃ N₁ N₂ N₃
    N₁Nonzero N₂Nonzero N₃Nonzero firstCleared secondCleared thirdCleared

/-- Denominator-free core of Ceva's theorem.  The common factor retained on
both sides is precisely the product cancelled after invoking Alternate
spreads. -/
theorem ceva_cleared
    (r₁ r₂ r₃ p₁ p₂ p₃ s₁ s₂ s₃ R₁ R₂ R₃ P₁ P₂ P₃ : K)
    (firstRatio : r₁ * (s₃ * P₁) = (s₂ * R₁) * p₁)
    (secondRatio : r₂ * (s₁ * P₂) = (s₃ * R₂) * p₂)
    (thirdRatio : r₃ * (s₂ * P₃) = (s₁ * R₃) * p₃)
    (alternateSpreads : r₁ * r₂ * r₃ = p₁ * p₂ * p₃) :
    (R₁ * R₂ * R₃) * ((s₁ * s₂ * s₃) * (p₁ * p₂ * p₃)) =
      (P₁ * P₂ * P₃) * ((s₁ * s₂ * s₃) * (p₁ * p₂ * p₃)) := by
  have multipliedRatios :
      (r₁ * r₂ * r₃) * (s₁ * s₂ * s₃) * (P₁ * P₂ * P₃) =
        (s₁ * s₂ * s₃) * (R₁ * R₂ * R₃) * (p₁ * p₂ * p₃) := by
    calc
      (r₁ * r₂ * r₃) * (s₁ * s₂ * s₃) * (P₁ * P₂ * P₃) =
          (r₁ * (s₃ * P₁)) * (r₂ * (s₁ * P₂)) *
            (r₃ * (s₂ * P₃)) := by ring1
      _ = ((s₂ * R₁) * p₁) * ((s₃ * R₂) * p₂) *
          ((s₁ * R₃) * p₃) := by
        rw [firstRatio, secondRatio, thirdRatio]
      _ = (s₁ * s₂ * s₃) * (R₁ * R₂ * R₃) *
          (p₁ * p₂ * p₃) := by ring1
  calc
    (R₁ * R₂ * R₃) * ((s₁ * s₂ * s₃) * (p₁ * p₂ * p₃)) =
        (s₁ * s₂ * s₃) * (R₁ * R₂ * R₃) *
          (p₁ * p₂ * p₃) := by ring1
    _ = (r₁ * r₂ * r₃) * (s₁ * s₂ * s₃) *
        (P₁ * P₂ * P₃) := multipliedRatios.symm
    _ = (P₁ * P₂ * P₃) *
        ((s₁ * s₂ * s₃) * (p₁ * p₂ * p₃)) := by
      rw [alternateSpreads]
      ring1

/-- Theorem 80 (Ceva), in the exact quadrance-product form. -/
theorem ceva
    (r₁ r₂ r₃ p₁ p₂ p₃ s₁ s₂ s₃ R₁ R₂ R₃ P₁ P₂ P₃ : K)
    (p₁Nonzero : p₁ ≠ 0) (p₂Nonzero : p₂ ≠ 0)
    (p₃Nonzero : p₃ ≠ 0)
    (s₁Nonzero : s₁ ≠ 0) (s₂Nonzero : s₂ ≠ 0)
    (s₃Nonzero : s₃ ≠ 0)
    (firstRatio : r₁ * (s₃ * P₁) = (s₂ * R₁) * p₁)
    (secondRatio : r₂ * (s₁ * P₂) = (s₃ * R₂) * p₂)
    (thirdRatio : r₃ * (s₂ * P₃) = (s₁ * R₃) * p₃)
    (alternateSpreads : r₁ * r₂ * r₃ = p₁ * p₂ * p₃) :
    R₁ * R₂ * R₃ = P₁ * P₂ * P₃ := by
  have firstSpreadPairNonzero :=
    RFAP.ExplicitField.mul_ne_zero s₁Nonzero s₂Nonzero
  have spreadProductNonzero : s₁ * s₂ * s₃ ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero firstSpreadPairNonzero s₃Nonzero
  have firstBisectorPairNonzero :=
    RFAP.ExplicitField.mul_ne_zero p₁Nonzero p₂Nonzero
  have bisectorProductNonzero : p₁ * p₂ * p₃ ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero firstBisectorPairNonzero p₃Nonzero
  have commonFactorNonzero :
      (s₁ * s₂ * s₃) * (p₁ * p₂ * p₃) ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero spreadProductNonzero
      bisectorProductNonzero
  apply eq_of_mul_eq_mul_right commonFactorNonzero
  exact ceva_cleared r₁ r₂ r₃ p₁ p₂ p₃ s₁ s₂ s₃
    R₁ R₂ R₃ P₁ P₂ P₃ firstRatio secondRatio thirdRatio
    alternateSpreads

/-- The book-proof interface taking the three Triangle-proportion quotient
equalities and the Alternate-spreads product. -/
theorem ceva_of_triangle_proportions
    (r₁ r₂ r₃ p₁ p₂ p₃ s₁ s₂ s₃ R₁ R₂ R₃ P₁ P₂ P₃ : K)
    (p₁Nonzero : p₁ ≠ 0) (p₂Nonzero : p₂ ≠ 0)
    (p₃Nonzero : p₃ ≠ 0)
    (s₁Nonzero : s₁ ≠ 0) (s₂Nonzero : s₂ ≠ 0)
    (s₃Nonzero : s₃ ≠ 0)
    (P₁Nonzero : P₁ ≠ 0) (P₂Nonzero : P₂ ≠ 0)
    (P₃Nonzero : P₃ ≠ 0)
    (firstRatio : r₁ / p₁ = (s₂ * R₁) / (s₃ * P₁))
    (secondRatio : r₂ / p₂ = (s₃ * R₂) / (s₁ * P₂))
    (thirdRatio : r₃ / p₃ = (s₁ * R₃) / (s₂ * P₃))
    (alternateSpreads : r₁ * r₂ * r₃ = p₁ * p₂ * p₃) :
    R₁ * R₂ * R₃ = P₁ * P₂ * P₃ := by
  have s₃P₁Nonzero := RFAP.ExplicitField.mul_ne_zero s₃Nonzero P₁Nonzero
  have s₁P₂Nonzero := RFAP.ExplicitField.mul_ne_zero s₁Nonzero P₂Nonzero
  have s₂P₃Nonzero := RFAP.ExplicitField.mul_ne_zero s₂Nonzero P₃Nonzero
  have firstCleared := cross_product_of_ratio_eq p₁Nonzero s₃P₁Nonzero
    firstRatio
  have secondCleared := cross_product_of_ratio_eq p₂Nonzero s₁P₂Nonzero
    secondRatio
  have thirdCleared := cross_product_of_ratio_eq p₃Nonzero s₂P₃Nonzero
    thirdRatio
  exact ceva r₁ r₂ r₃ p₁ p₂ p₃ s₁ s₂ s₃ R₁ R₂ R₃ P₁ P₂ P₃
    p₁Nonzero p₂Nonzero p₃Nonzero s₁Nonzero s₂Nonzero s₃Nonzero
    firstCleared secondCleared thirdCleared alternateSpreads

end DivineProportions
