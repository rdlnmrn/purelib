module
public import Purelib.Data.Nat.Order
public import Purelib.Algebra.Field.ExplicitField
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Tactic.Ring

section
@[expose] public section

/-!
# Divine Proportions, Chapter 24: surveying

Every construction is expressed by its finite quadrance/spread equations.
Decimal readings are retained as exact integer coefficient pairs, with
integer interval certificates for the source's numerical approximations.
-/

namespace Purelib.Geometry.Space.Spread.LinePlane.Relation.Cleared

section

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- Derive the cleared relation between line and plane spreads from their common dot ratio.

The equations `q = 1 - t²` and `S(1+t)² = 1+2t` imply `(1-Sq)² = 4(1-S)(1-q)` without dividing by any parameter
(Exercise 24.1). -/
theorem exercise_24_1 (q S t : K)
    (lineSpread : q = 1 - t ^ 2)
    (planeSpreadCleared : S * (1 + t) ^ 2 = 1 + 2 * t) :
    (1 - S * q) ^ 2 = 4 * (1 - S) * (1 - q) := by
  have complementPlane : (1 - S) * (1 + t) ^ 2 = t ^ 2 := by
    calc
      (1 - S) * (1 + t) ^ 2 =
          (1 + t) ^ 2 - S * (1 + t) ^ 2 := by ring1
      _ = (1 + t) ^ 2 - (1 + 2 * t) := by rw [planeSpreadCleared]
      _ = t ^ 2 := by ring1
  have mixedRelation : S * t ^ 2 = (1 - S) * (1 + 2 * t) := by
    calc
      S * t ^ 2 = S * (1 + t) ^ 2 - S * (1 + 2 * t) := by ring1
      _ = (1 + 2 * t) - S * (1 + 2 * t) := by rw [planeSpreadCleared]
      _ = (1 - S) * (1 + 2 * t) := by ring1
  rw [lineSpread]
  calc
    (1 - S * (1 - t ^ 2)) ^ 2 = ((1 - S) + S * t ^ 2) ^ 2 := by ring1
    _ = ((1 - S) + (1 - S) * (1 + 2 * t)) ^ 2 := by rw [mixedRelation]
    _ = 4 * (1 - S) * ((1 - S) * (1 + t) ^ 2) := by ring1
    _ = 4 * (1 - S) * t ^ 2 := by rw [complementPlane]
    _ = 4 * (1 - S) * (1 - (1 - t ^ 2)) := by ring1
end
end Purelib.Geometry.Space.Spread.LinePlane.Relation.Cleared

end
