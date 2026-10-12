module
public import Purelib.Algebra.Field.ExplicitField
import Purelib.Geometry.Triangles.Ceva.Proportions
import Purelib.Tactic.Ring

open Purelib.Algebra.Field

open Purelib

section
@[expose] public section

/-!
# Divine Proportions, Chapter 11 exercises

This module begins the reader problems following the Two-struts theorem.  All
normalizations are retained as finite polynomial equalities.  In particular,
Example 11.1 is checked by scaling the two quad triples by the displayed
factor `256`; no quadratic formula or selected root is used.
-/

namespace Purelib.Algebra.Proportions.Ceva.RetainedFactor

variable {K : Type*} [ExplicitField K]

/-- Retain the common factor in three cleared Ceva ratio equations.

Equality of the two spread products forces the quadrance-product difference times the displayed common factor to vanish;
the factor may be zero. -/
theorem exercise_11_11_ceva_relaxed
    (r₁ r₂ r₃ p₁ p₂ p₃ s₁ s₂ s₃ R₁ R₂ R₃ P₁ P₂ P₃ : K)
    (firstRatio : r₁ * (s₃ * P₁) = (s₂ * R₁) * p₁)
    (secondRatio : r₂ * (s₁ * P₂) = (s₃ * R₂) * p₂)
    (thirdRatio : r₃ * (s₂ * P₃) = (s₁ * R₃) * p₃)
    (alternateSpreads : r₁ * r₂ * r₃ = p₁ * p₂ * p₃) :
    (R₁ * R₂ * R₃ - P₁ * P₂ * P₃) *
      ((s₁ * s₂ * s₃) * (p₁ * p₂ * p₃)) = 0 := by
  have retained := Geometry.Triangles.Ceva.Proportions.ceva_cleared r₁ r₂ r₃ p₁ p₂ p₃ s₁ s₂ s₃
    R₁ R₂ R₃ P₁ P₂ P₃ firstRatio secondRatio thirdRatio
      alternateSpreads
  calc
    (R₁ * R₂ * R₃ - P₁ * P₂ * P₃) *
        ((s₁ * s₂ * s₃) * (p₁ * p₂ * p₃)) =
      (R₁ * R₂ * R₃) * ((s₁ * s₂ * s₃) * (p₁ * p₂ * p₃)) -
        (P₁ * P₂ * P₃) * ((s₁ * s₂ * s₃) *
          (p₁ * p₂ * p₃)) := by ring1
    _ = 0 := by rw [retained]; ring1

end Purelib.Algebra.Proportions.Ceva.RetainedFactor

end
