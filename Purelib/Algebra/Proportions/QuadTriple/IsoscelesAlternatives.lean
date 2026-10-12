module
public import Purelib.Data.Nat.Order
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Geometry.Trigonometry.QuadTriple.Basic
import Purelib.Tactic.Ring
import Purelib.Algebra.Group.Basic

open Purelib.Algebra
open Purelib.Algebra.Field

open Purelib.Geometry.Trigonometry

public section

/-!
# Isosceles quad-triple alternatives

Polynomial factorization gives the two linear alternatives of an isosceles
quad-triple configuration over an explicitly supplied field.
-/

namespace Purelib.Algebra.Proportions.QuadTriple.IsoscelesAlternatives

variable {K : Type*} [ExplicitField K]

/-- Factor the constraints of an isosceles quad-triple configuration.

The base quad triple and the squared product relation make the two displayed linear alternatives multiply to zero. -/
theorem exercise_11_6_cleared
    (Q R₁ R₂ R₃ : K)
    (baseTriple : Geometry.Trigonometry.QuadTriple R₂ R₁ Q)
    (isoscelesProduct : (Q - R₃) ^ 2 = R₁ * R₂) :
    (Q - (2 * R₃ - R₁ - R₂)) *
      (3 * Q - (2 * R₃ + R₁ + R₂)) = 0 := by
  change QuadTriple.Basic.archimedesFunction R₂ R₁ Q = 0 at baseTriple
  calc
    (Q - (2 * R₃ - R₁ - R₂)) *
        (3 * Q - (2 * R₃ + R₁ + R₂)) =
      QuadTriple.Basic.archimedesFunction R₂ R₁ Q -
        4 * (R₁ * R₂ - (Q - R₃) ^ 2) := by
      unfold QuadTriple.Basic.archimedesFunction
      ring1
    _ = 0 := by rw [baseTriple, isoscelesProduct]; ring1

/-- Resolve the two linear alternatives of an isosceles quad-triple configuration.

Decidable equality and nonzero three allow the zero-product factorization to yield the displayed linear or divided
expression for the base value. -/
theorem exercise_11_6 [DecidableEq K]
    (Q R₁ R₂ R₃ : K) (threeNonzero : (3 : K) ≠ 0)
    (baseTriple : Geometry.Trigonometry.QuadTriple R₂ R₁ Q)
    (isoscelesProduct : (Q - R₃) ^ 2 = R₁ * R₂) :
    Q = 2 * R₃ - R₁ - R₂ ∨
      Q = (2 * R₃ + R₁ + R₂) / 3 := by
  have factored := exercise_11_6_cleared Q R₁ R₂ R₃ baseTriple
    isoscelesProduct
  by_cases firstFactorZero : Q - (2 * R₃ - R₁ - R₂) = 0
  · exact Or.inl (Group.eq_of_sub_eq_zero firstFactorZero)
  · have secondFactorZero :
        3 * Q - (2 * R₃ + R₁ + R₂) = 0 := by
      by_cases zero : 3 * Q - (2 * R₃ + R₁ + R₂) = 0
      · exact zero
      · exact False.elim
          ((ExplicitField.mul_ne_zero firstFactorZero zero) factored)
    apply Or.inr
    apply ExplicitField.eq_of_mul_eq_mul_right threeNonzero
    calc
      Q * 3 = 3 * Q := by ring1
      _ = 2 * R₃ + R₁ + R₂ := Group.eq_of_sub_eq_zero secondFactorZero
      _ = ((2 * R₃ + R₁ + R₂) / 3) * 3 :=
        (ExplicitField.div_mul_cancel _ threeNonzero).symm
end Purelib.Algebra.Proportions.QuadTriple.IsoscelesAlternatives
