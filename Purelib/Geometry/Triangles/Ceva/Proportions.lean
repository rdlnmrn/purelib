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

namespace Purelib.Geometry.Triangles.Ceva.Proportions

variable {K : Type*} [ExplicitField K]

/-- Denominator-free core of Ceva's theorem. The common factor retained on both sides is precisely the product cancelled
after invoking Alternate spreads. -/
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

/-- Ceva's quadrance-product equality from three cleared proportion laws.

The alternate-spread product relation and the six nonzero spread factors allow cancellation of the common product. -/
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
    ExplicitField.mul_ne_zero s₁Nonzero s₂Nonzero
  have spreadProductNonzero : s₁ * s₂ * s₃ ≠ 0 :=
    ExplicitField.mul_ne_zero firstSpreadPairNonzero s₃Nonzero
  have firstBisectorPairNonzero :=
    ExplicitField.mul_ne_zero p₁Nonzero p₂Nonzero
  have bisectorProductNonzero : p₁ * p₂ * p₃ ≠ 0 :=
    ExplicitField.mul_ne_zero firstBisectorPairNonzero p₃Nonzero
  have commonFactorNonzero :
      (s₁ * s₂ * s₃) * (p₁ * p₂ * p₃) ≠ 0 :=
    ExplicitField.mul_ne_zero spreadProductNonzero
      bisectorProductNonzero
  apply ExplicitField.eq_of_mul_eq_mul_right commonFactorNonzero
  exact ceva_cleared r₁ r₂ r₃ p₁ p₂ p₃ s₁ s₂ s₃
    R₁ R₂ R₃ P₁ P₂ P₃ firstRatio secondRatio thirdRatio
    alternateSpreads

/-- Ceva's quadrance-product equality from three quotient proportion laws.

The displayed denominators and cancelled spread factors are nonzero, and the alternate-spread products agree. -/
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
  have s₃P₁Nonzero := ExplicitField.mul_ne_zero s₃Nonzero P₁Nonzero
  have s₁P₂Nonzero := ExplicitField.mul_ne_zero s₁Nonzero P₂Nonzero
  have s₂P₃Nonzero := ExplicitField.mul_ne_zero s₂Nonzero P₃Nonzero
  have firstCleared := Ratio.cross_product_of_ratio_eq p₁Nonzero s₃P₁Nonzero
    firstRatio
  have secondCleared := Ratio.cross_product_of_ratio_eq p₂Nonzero s₁P₂Nonzero
    secondRatio
  have thirdCleared := Ratio.cross_product_of_ratio_eq p₃Nonzero s₂P₃Nonzero
    thirdRatio
  exact ceva r₁ r₂ r₃ p₁ p₂ p₃ s₁ s₂ s₃ R₁ R₂ R₃ P₁ P₂ P₃
    p₁Nonzero p₂Nonzero p₃Nonzero s₁Nonzero s₂Nonzero s₃Nonzero
    firstCleared secondCleared thirdCleared alternateSpreads

end Purelib.Geometry.Triangles.Ceva.Proportions

end
