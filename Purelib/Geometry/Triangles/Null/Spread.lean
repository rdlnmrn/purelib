module
import Purelib.Algebra.Field.Characteristic.Nonzero
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Geometry.Trigonometry.QuadTriple.Basic
import Purelib.Geometry.Trigonometry.QuadTriple.Null
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra.Field

open Purelib.Geometry.Trigonometry

open Purelib.Geometry.Trigonometry.QuadTriple

/-!
# Divine Proportions, Exercises 6.3--6.6

The common spread ratio and the two null-triangle formulas are finite
consequences of the Quadrea-spread identity.  The rational triangle inequality
is the statement that the coordinate-determinant square is nonnegative; no
absolute value, square root, compactness, or extremum is introduced.
-/

@[expose] public section

namespace Purelib.Geometry.Triangles.Null.Spread

variable {K : Type*} [ExplicitField K]

/-- Exercise 6.4: the Quadrea-spread equation for a null-side triangle gives the exact displayed third spread. -/
theorem spread_formula
    (q₁ q₂ s₃ : K) (twoNonzero : (2 : K) ≠ 0)
    (q₁Nonzero : q₁ ≠ 0) (q₂Nonzero : q₂ ≠ 0)
    (areaSpread : QuadTriple.Basic.archimedesFunction q₁ q₂ 0 = 4 * q₁ * q₂ * s₃) :
    QuadTriple.Basic.archimedesFunction q₁ q₂ 0 = -(q₁ - q₂) ^ 2 ∧
      s₃ = -(q₁ - q₂) ^ 2 / (4 * q₁ * q₂) := by
  have fourNonzero := Characteristic.Nonzero.four_ne_zero twoNonzero
  have denominatorNonzero : 4 * q₁ * q₂ ≠ 0 :=
    ExplicitField.mul_ne_zero
      (ExplicitField.mul_ne_zero fourNonzero q₁Nonzero)
      q₂Nonzero
  have areaFormula := Null.archimedesFunction_third_zero q₁ q₂
  refine ⟨areaFormula, ?_⟩
  apply ExplicitField.eq_of_mul_eq_mul_right denominatorNonzero
  calc
    s₃ * (4 * q₁ * q₂) = 4 * q₁ * q₂ * s₃ := by ring1
    _ = QuadTriple.Basic.archimedesFunction q₁ q₂ 0 := areaSpread.symm
    _ = -(q₁ - q₂) ^ 2 := areaFormula
    _ = (-(q₁ - q₂) ^ 2 / (4 * q₁ * q₂)) *
        (4 * q₁ * q₂) :=
      (ExplicitField.div_mul_cancel _ denominatorNonzero).symm

end Purelib.Geometry.Triangles.Null.Spread

end
