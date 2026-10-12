module
public import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.Field.Ratio
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra.Field

section
@[expose] public section

/-!
# Divine Proportions, Chapter 11: Menelaus and Ceva

The cyclic arguments are stated first as product identities retaining the
common spread factor.  The geometric nonparallel hypotheses supply explicit
nonzero certificates exactly where the printed conclusions cancel that factor.
-/

namespace Purelib.Geometry.Triangles.Menelaus.Proportions

variable {K : Type*} [ExplicitField K]

/-- Denominator-free cyclic product at the core of Menelaus' theorem. The three hypotheses are the cleared forms of
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

/-- Menelaus's quadrance-product equality from three cleared cyclic ratios.

The three cancelled spread factors are nonzero. -/
theorem menelaus
    (r₁ r₂ r₃ R₁ R₂ R₃ P₁ P₂ P₃ : K)
    (r₁Nonzero : r₁ ≠ 0) (r₂Nonzero : r₂ ≠ 0)
    (r₃Nonzero : r₃ ≠ 0)
    (firstRatio : r₁ * P₁ = R₂ * r₂)
    (secondRatio : r₂ * P₂ = R₃ * r₃)
    (thirdRatio : r₃ * P₃ = R₁ * r₁) :
    R₁ * R₂ * R₃ = P₁ * P₂ * P₃ := by
  have firstPairNonzero :=
    ExplicitField.mul_ne_zero r₁Nonzero r₂Nonzero
  have spreadProductNonzero : r₁ * r₂ * r₃ ≠ 0 :=
    ExplicitField.mul_ne_zero firstPairNonzero r₃Nonzero
  apply ExplicitField.eq_of_mul_eq_mul_right spreadProductNonzero
  exact menelaus_cleared r₁ r₂ r₃ R₁ R₂ R₃ P₁ P₂ P₃
    firstRatio secondRatio thirdRatio

/-- Menelaus's quadrance-product equality from three quotient spread laws with nonzero denominators. -/
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
  have firstCleared := Ratio.cross_product_of_ratio_eq r₂Nonzero P₁Nonzero
    firstRatio
  have secondCleared := Ratio.cross_product_of_ratio_eq r₃Nonzero P₂Nonzero
    secondRatio
  have thirdCleared := Ratio.cross_product_of_ratio_eq r₁Nonzero P₃Nonzero
    thirdRatio
  exact menelaus r₁ r₂ r₃ R₁ R₂ R₃ P₁ P₂ P₃
    r₁Nonzero r₂Nonzero r₃Nonzero firstCleared secondCleared thirdCleared

/-- Denominator-free cyclic product at the core of Theorem 79. The hypotheses are the cleared forms of `r₂/p₃=N₃/N₂`,
`r₃/p₁=N₁/N₃`, and `r₁/p₂=N₂/N₁`. -/
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

/-- Three cleared cyclic ratios imply equality of the alternate-spread products.

The three common quadrance factors are nonzero and can be cancelled. -/
theorem alternate_spreads
    (r₁ r₂ r₃ p₁ p₂ p₃ N₁ N₂ N₃ : K)
    (N₁Nonzero : N₁ ≠ 0) (N₂Nonzero : N₂ ≠ 0)
    (N₃Nonzero : N₃ ≠ 0)
    (firstRatio : r₂ * N₂ = N₃ * p₃)
    (secondRatio : r₃ * N₃ = N₁ * p₁)
    (thirdRatio : r₁ * N₁ = N₂ * p₂) :
    r₁ * r₂ * r₃ = p₁ * p₂ * p₃ := by
  have firstPairNonzero :=
    ExplicitField.mul_ne_zero N₁Nonzero N₂Nonzero
  have quadranceProductNonzero : N₁ * N₂ * N₃ ≠ 0 :=
    ExplicitField.mul_ne_zero firstPairNonzero N₃Nonzero
  apply ExplicitField.eq_of_mul_eq_mul_right quadranceProductNonzero
  exact alternate_spreads_cleared r₁ r₂ r₃ p₁ p₂ p₃ N₁ N₂ N₃
    firstRatio secondRatio thirdRatio

/-- Three quotient spread laws imply equality of the alternate-spread products, with every displayed denominator
nonzero. -/
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
  have firstCleared := Ratio.cross_product_of_ratio_eq p₃Nonzero N₂Nonzero
    firstRatio
  have secondCleared := Ratio.cross_product_of_ratio_eq p₁Nonzero N₃Nonzero
    secondRatio
  have thirdCleared := Ratio.cross_product_of_ratio_eq p₂Nonzero N₁Nonzero
    thirdRatio
  exact alternate_spreads r₁ r₂ r₃ p₁ p₂ p₃ N₁ N₂ N₃
    N₁Nonzero N₂Nonzero N₃Nonzero firstCleared secondCleared thirdCleared
end Purelib.Geometry.Triangles.Menelaus.Proportions

end
