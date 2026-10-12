module
public import Purelib.Data.Nat.Order
public import Mathlib.Algebra.Ring.Defs

import Mathlib.Tactic.TypeStar

/-!
# Divine Proportions, §2.2–2.3: proportions and identities

The source's elementary identities are stated directly over constructive
commutative rings.  Its three-index antisymmetrization is an explicit six-term
operation, so none of these declarations uses permutations, finite sums, or a
global enumeration.
-/

@[expose] public section

namespace Purelib.LinearAlgebra.Alternating.Bracket.Fin4

variable {K : Type*}

section Identities

variable [CommRing K]

/-- Alternate a four-index function over all 24 signed permutations.

The explicit term order fixes the determinant sign convention over a commutative ring. -/
def alternatingFour
    (term : Fin 4 → Fin 4 → Fin 4 → Fin 4 → K) : K :=
  term 0 1 2 3 - term 0 1 3 2 + term 0 2 3 1 - term 0 3 2 1 +
    term 0 3 1 2 - term 0 2 1 3 +
  term 1 2 0 3 - term 1 3 0 2 + term 2 3 0 1 - term 2 3 1 0 +
    term 1 3 2 0 - term 1 2 3 0 +
  term 2 1 3 0 - term 3 1 2 0 + term 3 2 1 0 - term 3 2 0 1 +
    term 3 1 0 2 - term 2 1 0 3 +
  term 2 0 1 3 - term 3 0 1 2 + term 3 0 2 1 - term 2 0 3 1 +
    term 1 0 3 2 - term 1 0 2 3

open Purelib.LinearAlgebra.Alternating in
/-- Expand the four-index bracket of a squared coordinate, a coordinate and a second column. -/
theorem example_2_15 (x y : Fin 4 → K) :
    alternatingFour (fun i j k _ => x i ^ 2 * x j * y k) =
      x 0 ^ 2 * x 1 * y 2 - x 0 ^ 2 * x 1 * y 3 +
      x 0 ^ 2 * x 2 * y 3 - x 0 ^ 2 * x 3 * y 2 +
      x 0 ^ 2 * x 3 * y 1 - x 0 ^ 2 * x 2 * y 1 +
      x 1 ^ 2 * x 2 * y 0 - x 1 ^ 2 * x 3 * y 0 +
      x 2 ^ 2 * x 3 * y 0 - x 2 ^ 2 * x 3 * y 1 +
      x 1 ^ 2 * x 3 * y 2 - x 1 ^ 2 * x 2 * y 3 +
      x 2 ^ 2 * x 1 * y 3 - x 3 ^ 2 * x 1 * y 2 +
      x 3 ^ 2 * x 2 * y 1 - x 3 ^ 2 * x 2 * y 0 +
      x 3 ^ 2 * x 1 * y 0 - x 2 ^ 2 * x 1 * y 0 +
      x 2 ^ 2 * x 0 * y 1 - x 3 ^ 2 * x 0 * y 1 +
      x 3 ^ 2 * x 0 * y 2 - x 2 ^ 2 * x 0 * y 3 +
      x 1 ^ 2 * x 0 * y 3 - x 1 ^ 2 * x 0 * y 2 := by
  rfl

end Identities

end Purelib.LinearAlgebra.Alternating.Bracket.Fin4

end
