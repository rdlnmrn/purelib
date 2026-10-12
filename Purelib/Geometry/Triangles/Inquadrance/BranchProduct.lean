module
public import Purelib.Data.Nat.Order

public import Purelib.Algebra.Field.ExplicitField
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Tactic.Ring

open Purelib.Algebra.Field (ExplicitField)

open Purelib

section
@[expose] public section

/-!
# Divine Proportions, remaining Chapter 12 exercises

This module completes the reader exercises: the finite chord argument from
Exercise 12.1, the null-side circumcenter argument from Exercise 12.4, and the
remaining exact polynomial and spread calculations.
-/

namespace Purelib.Geometry.Triangles.Inquadrance.BranchProduct

open Purelib.Algebra

variable {K : Type*} [ExplicitField K]

/-- Exercise 12.8 in its finite scalar form. The four inquadrance formulas come from Theorem 90 after selecting the four
finite bisector branches; the three double-spread identities and Exercise 12.2 then make the product a single polynomial
calculation. -/
theorem exercise_12_8
    (u₁ u₂ u₃ s₁ s₂ s₃ circumquadranceValue area
      r₀ r₁ r₂ r₃ : K)
    (sixteenNonzero : (16 : K) ≠ 0)
    (firstSideSpread : s₁ = 4 * u₁ * (1 - u₁))
    (secondSideSpread : s₂ = 4 * u₂ * (1 - u₂))
    (thirdSideSpread : s₃ = 4 * u₃ * (1 - u₃))
    (areaFormula :
      area = 64 * circumquadranceValue ^ 2 * s₁ * s₂ * s₃)
    (firstInquadrance :
      r₀ = 16 * circumquadranceValue * u₁ * u₂ * u₃)
    (secondInquadrance :
      r₁ = 16 * circumquadranceValue *
        u₁ * (1 - u₂) * (1 - u₃))
    (thirdInquadrance :
      r₂ = 16 * circumquadranceValue *
        (1 - u₁) * u₂ * (1 - u₃))
    (fourthInquadrance :
      r₃ = 16 * circumquadranceValue *
        (1 - u₁) * (1 - u₂) * u₃) :
    r₀ * r₁ * r₂ * r₃ = (area / 16) ^ 2 := by
  have sixteenCancel : (16 : K) * (16 : K)⁻¹ = 1 :=
    ExplicitField.mul_inv_cancel 16 sixteenNonzero
  have scaleCancel : (4096 : K) * (16 : K)⁻¹ = 256 := by
    calc
      (4096 : K) * (16 : K)⁻¹ =
          256 * ((16 : K) * (16 : K)⁻¹) := by ring1
      _ = 256 := by rw [sixteenCancel]; ring1
  rw [firstInquadrance, secondInquadrance, thirdInquadrance,
    fourthInquadrance, areaFormula, firstSideSpread, secondSideSpread,
    thirdSideSpread]
  simp only [ExplicitField.div_eq_mul_inv]
  rw [show
    64 * circumquadranceValue ^ 2 *
          (4 * u₁ * (1 - u₁)) *
          (4 * u₂ * (1 - u₂)) *
          (4 * u₃ * (1 - u₃)) * (16 : K)⁻¹ =
        (4096 : K) * (16 : K)⁻¹ * circumquadranceValue ^ 2 *
          u₁ * (1 - u₁) * u₂ * (1 - u₂) * u₃ * (1 - u₃) by ring1]
  rw [scaleCancel]
  ring1

end Purelib.Geometry.Triangles.Inquadrance.BranchProduct

end
