module
public import Purelib.Algebra.Field.ExplicitField

import Purelib.Tactic.QuotientFreeOmega
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

namespace Purelib.LinearAlgebra.Coordinates2.Determinant

variable {K : Type*}

section Identities

variable [CommRing K]

/-- Exercise 2.6: the coordinate-difference identity later used by the
Spread-ratio theorem. -/
theorem exercise_2_6
    (x₁ y₁ x₂ y₂ x₃ y₃ : K) :
    (y₁ - y₂) * (x₃ - x₁) - (y₁ - y₃) * (x₂ - x₁) =
      (y₁ - y₃) * (x₃ - x₂) - (y₂ - y₃) * (x₃ - x₁) := by
  ring1
end Identities

end Purelib.LinearAlgebra.Coordinates2.Determinant

end

end

section
@[expose] public section

/-!
# Divine Proportions, Chapter 27: rational spherical coordinates

This module formalizes the finite algebra beneath the source's coordinate
changes: squared-coordinate reconstruction, the two-, three-, and
four-dimensional Jacobian determinants, squared density identities, the
lemniscate conversion, and a witness-based finite polygon-refinement step.

The chapter's improper integrals, exponentials, Gamma/Beta integrals, `π`, and
limit assertions are intentionally not introduced.  Their finite endpoint
polynomial simplifications are retained at the end of the module.
-/

namespace Purelib.LinearAlgebra.Coordinates2.Determinant

namespace RationalSphericalCoordinates

variable {K : Type*} [ExplicitField K]

/-- Compute the signed two-by-two determinant from its four entries. -/
def determinantTwo (a b c d : K) : K
  := a * d - b * c
end RationalSphericalCoordinates
end Purelib.LinearAlgebra.Coordinates2.Determinant

end

section
@[expose] public section

/-!
# Divine Proportions, Chapter 8: bordered-tridiagonal determinants

The determinant family in Exercise 8.8 is evaluated by its finite continuant
and last-column cofactor expansion.  The first four literal determinants from
the source are also checked independently.
-/

namespace Purelib.LinearAlgebra.Coordinates2.Determinant.SpreadDeterminant

variable {K : Type*} [ExplicitField K]

/-- Ordinary two-by-two determinant, used to check the second displayed
matrix literally. -/
def determinantTwo {R : Type*} [CommRing R]
    (a₀₀ a₀₁ a₁₀ a₁₁ : R) : R :=
  a₀₀ * a₁₁ - a₀₁ * a₁₀
end Purelib.LinearAlgebra.Coordinates2.Determinant.SpreadDeterminant

end
