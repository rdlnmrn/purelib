module
public import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.Field.Ratio
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra.Field

@[expose] public section

/-!
# Divine Proportions, Chapter 11: triangle proportions

The denominator-free theorem records exactly the three cross-products supplied
by the Spread law.  The printed quotient chain is then recovered only from its
visible nonzero denominators.  This separation keeps the result meaningful in
finite fields even when a displayed quotient would be undefined geometrically.
-/

namespace Purelib.Geometry.Triangles.Proportions

variable {K : Type*} [ExplicitField K]

/-- Three cleared spread laws imply two cross-product relations between triangle proportions. -/
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

/-- Three cleared spread laws imply the chain of triangle proportion ratios.

Each factor in the displayed denominators has an explicit nonzero certificate. -/
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
    ExplicitField.mul_ne_zero s₂Nonzero R₂Nonzero
  have q₂R₂Nonzero : q₂ * R₂ ≠ 0 :=
    ExplicitField.mul_ne_zero q₂Nonzero R₂Nonzero
  rcases triangle_proportions_cleared r₁ r₂ s₁ s₂ q₁ q₂ R₁ R₂ R₃
    firstSubtriangle secondSubtriangle originalTriangle with
    ⟨firstCrossProduct, secondCrossProduct⟩
  exact ⟨Ratio.ratio_eq_of_cross_product r₂Nonzero s₂R₂Nonzero
      firstCrossProduct,
    Ratio.ratio_eq_of_cross_product s₂R₂Nonzero q₂R₂Nonzero
      secondCrossProduct⟩

/-- Three quotient spread laws imply the chain of triangle proportion ratios.

The displayed side and spread denominators are assumed nonzero before the laws are cleared and combined. -/
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
    Ratio.cross_product_of_ratio_eq R₃Nonzero R₁Nonzero firstSubtriangle
  have secondCleared : s₂ * R₂ = r₂ * R₃ :=
    Ratio.cross_product_of_ratio_eq R₃Nonzero R₂Nonzero secondSubtriangle
  have originalCleared : s₁ * q₂ = s₂ * q₁ :=
    Ratio.cross_product_of_ratio_eq q₁Nonzero q₂Nonzero originalTriangle
  exact triangle_proportions r₁ r₂ s₁ s₂ q₁ q₂ R₁ R₂ R₃
    r₂Nonzero s₂Nonzero q₂Nonzero R₂Nonzero firstCleared
    secondCleared originalCleared

end Purelib.Geometry.Triangles.Proportions

end
