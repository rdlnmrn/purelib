module
import Purelib.Tactic.Ring

import Mathlib.Tactic.TypeStar

public import Mathlib.Algebra.Ring.Defs

/-!
# Divine Proportions, §2.2–2.3: proportions and identities

The source's elementary identities are stated directly over constructive
commutative rings.  Its three-index antisymmetrization is an explicit six-term
operation, so none of these declarations uses permutations, finite sums, or a
global enumeration.
-/

@[expose] public section

namespace Purelib.Algebra

variable {K : Type*}

section Identities

variable [CommRing K]

/-- Express a product of two sums of two squares as a sum of two squares.

The two terms are the determinant and dot product of the displayed coordinate pairs in a commutative ring. -/
theorem Identities.SumSquares.example_2_9 (x₁ y₁ x₂ y₂ : K) :
    (x₁ * y₂ - x₂ * y₁) ^ 2 + (x₁ * x₂ + y₁ * y₂) ^ 2 =
      (x₁ ^ 2 + y₁ ^ 2) * (x₂ ^ 2 + y₂ ^ 2) := by
  ring1

/-- Express a product of two sums of three squares using cross products and a dot product.

The identity sums the squares of all three coordinate minors and the three-coordinate dot product in a commutative ring.
-/
theorem Identities.SumSquares.example_2_10
    (x₁ y₁ z₁ x₂ y₂ z₂ : K) :
    (x₁ * y₂ - x₂ * y₁) ^ 2 +
        (y₁ * z₂ - y₂ * z₁) ^ 2 +
        (z₁ * x₂ - z₂ * x₁) ^ 2 +
        (x₁ * x₂ + y₁ * y₂ + z₁ * z₂) ^ 2 =
      (x₁ ^ 2 + y₁ ^ 2 + z₁ ^ 2) *
        (x₂ ^ 2 + y₂ ^ 2 + z₂ ^ 2) := by
  ring1

/-- Package the two- and three-coordinate sum-of-squares identities and their sign variant.

The three conjuncts hold for arbitrary displayed coordinates in a commutative ring. -/
theorem Identities.SumSquares.exercise_2_5
    (x₁ y₁ z₁ x₂ y₂ z₂ : K) :
    ((x₁ * y₂ - x₂ * y₁) ^ 2 + (x₁ * x₂ + y₁ * y₂) ^ 2 =
      (x₁ ^ 2 + y₁ ^ 2) * (x₂ ^ 2 + y₂ ^ 2)) ∧
    ((x₁ * y₂ - x₂ * y₁) ^ 2 +
        (y₁ * z₂ - y₂ * z₁) ^ 2 +
        (z₁ * x₂ - z₂ * x₁) ^ 2 +
        (x₁ * x₂ + y₁ * y₂ + z₁ * z₂) ^ 2 =
      (x₁ ^ 2 + y₁ ^ 2 + z₁ ^ 2) *
        (x₂ ^ 2 + y₂ ^ 2 + z₂ ^ 2)) ∧
    ((x₁ * y₂ + x₂ * y₁) ^ 2 + (x₁ * x₂ - y₁ * y₂) ^ 2 =
      (x₁ ^ 2 + y₁ ^ 2) * (x₂ ^ 2 + y₂ ^ 2)) := by
  exact ⟨by ring1, by ring1, by ring1⟩
end Identities

end Purelib.Algebra

end
