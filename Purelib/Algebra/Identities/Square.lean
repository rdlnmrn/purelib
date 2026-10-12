module
public import Purelib.Data.Nat.Order
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

/-- Expand the square of a sum of three elements.

In a commutative ring, the expansion contains each square and twice each pairwise product. -/
theorem Identities.Square.example_2_8 (x₁ x₂ x₃ : K) :
    (x₁ + x₂ + x₃) ^ 2 =
      x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2 +
        2 * (x₁ * x₂ + x₁ * x₃ + x₂ * x₃) := by
  ring1
end Identities

end Purelib.Algebra

end
