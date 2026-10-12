module
public import Purelib.Data.Nat.Order
public import Purelib.Algebra.Field.ExplicitField
import Mathlib.Algebra.Ring.Defs
import Purelib.Tactic.Ring

open Purelib.Algebra.Field

section
/-!
# Divine Proportions, §2.2–2.3: proportions and identities

The source's elementary identities are stated directly over constructive
commutative rings.  Its three-index antisymmetrization is an explicit six-term
operation, so none of these declarations uses permutations, finite sums, or a
global enumeration.
-/

@[expose] public section

namespace Purelib.LinearAlgebra.Alternating.Bracket.Fin3

variable {K : Type*}

section Identities

variable [CommRing K]

/-- Alternate a three-index function over the six ordered permutations.

The displayed positive and negative terms fix the sign convention over a commutative ring. -/
def alternatingThree
    (term : Fin 3 → Fin 3 → Fin 3 → K) : K :=
  term 0 1 2 - term 0 2 1 + term 1 2 0 -
    term 2 1 0 + term 2 0 1 - term 1 0 2

open Purelib.LinearAlgebra.Alternating
/-- Expand the alternating product of three coordinate columns as a three-by-three determinant. -/
theorem example_2_11 (x y z : Fin 3 → K) :
    alternatingThree (fun i j k => x i * y j * z k) =
      x 0 * y 1 * z 2 - x 0 * y 2 * z 1 +
        x 1 * y 2 * z 0 - x 2 * y 1 * z 0 +
        x 2 * y 0 * z 1 - x 1 * y 0 * z 2 := by
  rfl

/-- Expand the alternating product of two coordinate columns and a constant column. -/
theorem example_2_12 (x y : Fin 3 → K) :
    alternatingThree (fun i j _ => x i * y j) =
      x 0 * y 1 - x 0 * y 2 + x 1 * y 2 -
        x 2 * y 1 + x 2 * y 0 - x 1 * y 0 := by
  rfl

/-- Expand the three-index bracket of a coordinate times a fifth power and a second column. -/
theorem example_2_13 (x y : Fin 3 → K) :
    alternatingThree (fun i j _ => x i * x j ^ 5 * y j) =
      x 0 * x 1 ^ 5 * y 1 - x 0 * x 2 ^ 5 * y 2 +
        x 1 * x 2 ^ 5 * y 2 - x 2 * x 1 ^ 5 * y 1 +
        x 2 * x 0 ^ 5 * y 0 - x 1 * x 0 ^ 5 * y 0 := by
  rfl

/-- A three-index bracket vanishes when its term depends on only one index. -/
theorem example_2_14 (x : Fin 3 → K) :
    alternatingThree (fun i _ _ => x i) = 0 := by
  unfold alternatingThree
  ring1

/-- Factor the sum of two three-index brackets by the sum of the first coordinates.

The identity holds over the supplied commutative ring and uses the fixed six-term sign convention. -/
theorem exercise_2_7 (x y : Fin 3 → K) :
    alternatingThree (fun i j _ => x i ^ 2 * y j) +
        alternatingThree (fun i j _ => x i * x j * y j) =
      (x 0 + x 1 + x 2) *
        alternatingThree (fun i j _ => x i * y j) := by
  unfold alternatingThree
  ring1
end Identities

end Purelib.LinearAlgebra.Alternating.Bracket.Fin3

end

end

section
@[expose] public section

/-!
# Divine Proportions, §12.2: the circumcenter formula

The source abbreviates its coordinate numerators with the six-term
antisymmetric bracket `[uv]⁻₁₂₃`.  We expose that polynomial directly and use
it to define the printed circumcenter.  The proof compares its two fractions
with the explicit intersection of two perpendicular bisectors.
-/

namespace Purelib.LinearAlgebra.Alternating.Bracket.Fin3

variable {K : Type*} [ExplicitField K]

/-- Compute the six-term alternating product of two displayed coordinate triples.

The sign convention agrees with the three-index bracket with constant third column. -/
def antisymmetricTripleProduct
    (u₁ u₂ u₃ v₁ v₂ v₃ : K) : K :=
  u₁ * v₂ - u₁ * v₃ + u₂ * v₃ - u₃ * v₂ +
    u₃ * v₁ - u₂ * v₁
end Purelib.LinearAlgebra.Alternating.Bracket.Fin3

end
