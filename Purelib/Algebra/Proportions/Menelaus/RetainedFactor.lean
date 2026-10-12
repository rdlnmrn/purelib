module
public import Purelib.Algebra.Field.ExplicitField
import Purelib.Geometry.Triangles.Menelaus.Proportions
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

namespace Purelib.Algebra.Proportions.Menelaus.RetainedFactor

variable {K : Type*} [ExplicitField K]

/-- Retain the spread product in three cleared Menelaus ratio equations.

The quadrance-product difference annihilates the supplied spread product, without requiring any spread to be nonzero. -/
theorem exercise_11_11_menelaus_relaxed
    (r₁ r₂ r₃ R₁ R₂ R₃ P₁ P₂ P₃ : K)
    (firstRatio : r₁ * P₁ = R₂ * r₂)
    (secondRatio : r₂ * P₂ = R₃ * r₃)
    (thirdRatio : r₃ * P₃ = R₁ * r₁) :
    (R₁ * R₂ * R₃ - P₁ * P₂ * P₃) * (r₁ * r₂ * r₃) = 0 := by
  have retained := Geometry.Triangles.Menelaus.Proportions.menelaus_cleared r₁ r₂ r₃ R₁ R₂ R₃ P₁ P₂ P₃
    firstRatio secondRatio thirdRatio
  calc
    (R₁ * R₂ * R₃ - P₁ * P₂ * P₃) * (r₁ * r₂ * r₃) =
        (R₁ * R₂ * R₃) * (r₁ * r₂ * r₃) -
          (P₁ * P₂ * P₃) * (r₁ * r₂ * r₃) := by ring1
    _ = 0 := by rw [retained]; ring1
end Purelib.Algebra.Proportions.Menelaus.RetainedFactor

end
