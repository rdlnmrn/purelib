module
public import Purelib.Algebra.Field.ExplicitField
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Purelib.Tactic.Ring

section
@[expose] public section

/-!
# Divine Proportions, Chapter 24: surveying

Every construction is expressed by its finite quadrance/spread equations.
Decimal readings are retained as exact integer coefficient pairs, with
integer interval certificates for the source's numerical approximations.
-/

namespace Purelib.Geometry.Space.Spherical.Quadrance.Cleared

section

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- The complement-product relation gives the spherical quadrance identity.

From `1 - q = (1 - q₁) * (1 - q₂)`, recover `q = q₁ + q₂ - q₁*q₂` over the explicit field. -/
theorem spherical_pythagoras (q q₁ q₂ : K)
    (complementProduct : 1 - q = (1 - q₁) * (1 - q₂)) :
    q = q₁ + q₂ - q₁ * q₂ := by
  calc
    q = 1 - (1 - q) := by ring1
    _ = 1 - (1 - q₁) * (1 - q₂) := by rw [complementProduct]
    _ = q₁ + q₂ - q₁ * q₂ := by ring1

end
end Purelib.Geometry.Space.Spherical.Quadrance.Cleared

end
