import mathlib.Tactic.QuotientFreeRing
import DivineProportions.Proportions.Triangle

/-!
# Divine Proportions, Chapter 11: quadrilateral proportions

As for triangle proportions, the cross-product identity is primary and the
book's quotient is recovered from explicit nonzero denominator certificates.
-/

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K]

/-- Denominator-free core of Theorem 73.  The hypotheses are the two cleared
Spread laws in `ABD` and `CBD`, sharing `R = Q(B,D)`. -/
theorem quadrilateral_proportions_cleared
    (r₁ r₂ s₁ s₂ R₁ R₂ R : K)
    (firstTriangle : r₁ * R = s₁ * R₁)
    (secondTriangle : r₂ * R = s₂ * R₂) :
    r₁ * (s₂ * R₂) = (s₁ * R₁) * r₂ := by
  calc
    r₁ * (s₂ * R₂) = r₁ * (r₂ * R) := by rw [← secondTriangle]
    _ = (r₁ * R) * r₂ := by ring1
    _ = (s₁ * R₁) * r₂ := by rw [firstTriangle]

/-- Theorem 73 (Quadrilateral proportions), in the printed form
`r₁/r₂ = s₁R₁/(s₂R₂)`. -/
theorem quadrilateral_proportions
    (r₁ r₂ s₁ s₂ R₁ R₂ R : K)
    (r₂Nonzero : r₂ ≠ 0) (s₂Nonzero : s₂ ≠ 0)
    (R₂Nonzero : R₂ ≠ 0)
    (firstTriangle : r₁ * R = s₁ * R₁)
    (secondTriangle : r₂ * R = s₂ * R₂) :
    r₁ / r₂ = (s₁ * R₁) / (s₂ * R₂) := by
  have denominatorNonzero : s₂ * R₂ ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero s₂Nonzero R₂Nonzero
  exact ratio_eq_of_cross_product r₂Nonzero denominatorNonzero
    (quadrilateral_proportions_cleared r₁ r₂ s₁ s₂ R₁ R₂ R
      firstTriangle secondTriangle)

/-- The book's proof interface, taking the two quotient equalities directly
from the Spread law. -/
theorem quadrilateral_proportions_of_spread_laws
    (r₁ r₂ s₁ s₂ R₁ R₂ R : K)
    (r₂Nonzero : r₂ ≠ 0) (s₂Nonzero : s₂ ≠ 0)
    (R₁Nonzero : R₁ ≠ 0) (R₂Nonzero : R₂ ≠ 0)
    (RNonzero : R ≠ 0)
    (firstTriangle : r₁ / R₁ = s₁ / R)
    (secondTriangle : r₂ / R₂ = s₂ / R) :
    r₁ / r₂ = (s₁ * R₁) / (s₂ * R₂) := by
  have firstCleared : r₁ * R = s₁ * R₁ :=
    cross_product_of_ratio_eq R₁Nonzero RNonzero firstTriangle
  have secondCleared : r₂ * R = s₂ * R₂ :=
    cross_product_of_ratio_eq R₂Nonzero RNonzero secondTriangle
  exact quadrilateral_proportions r₁ r₂ s₁ s₂ R₁ R₂ R
    r₂Nonzero s₂Nonzero R₂Nonzero firstCleared secondCleared

end DivineProportions
