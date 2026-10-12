module
public import Purelib.Algebra.Group.Basic
public import Purelib.Data.Nat.Order
public import Purelib.Algebra.Group.Negation
public import Purelib.Algebra.Field.ExplicitField
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Tactic.Ring

section
open Purelib.Algebra
open Purelib.Data

-- These owned adapters retain the complete original operation dictionaries.
attribute [local instance 2000] Group.Negation.subNegZeroMonoid
  Nat.successorNeZero Nat.successorAtLeastTwo

open Purelib

section
public section

/-!
# Divine Proportions, Chapter 7: the triple spread formula

The proof is performed directly on the six finite line coefficients.  A
single explicit common denominator replaces the book's auxiliary triangle,
and every cancellation is witnessed by the three non-null hypotheses.
-/

namespace Purelib.Geometry.Trigonometry.Cross.Triple

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- Exercise 7.7: both normal forms of the Triple cross formula. The second clause names the complementary spreads
`s₁=1-c₁` and `s₂=1-c₂` without adding any geometric or infinitary data. -/
theorem exercise_7_7
    (c₁ c₂ c₃ : K)
    (tripleCross : (c₁ + c₂ + c₃ - 1) ^ 2 = 4 * c₁ * c₂ * c₃) :
    (c₃ + c₁ + c₂ - 2 * c₁ * c₂ - 1) ^ 2 =
        4 * c₁ * c₂ * (1 - c₁) * (1 - c₂) ∧
      let s₁ := 1 - c₁
      let s₂ := 1 - c₂
      (c₃ - (c₁ * c₂ + s₁ * s₂)) ^ 2 =
        4 * c₁ * c₂ * s₁ * s₂ := by
  have differenceZero :
      (c₁ + c₂ + c₃ - 1) ^ 2 - 4 * c₁ * c₂ * c₃ = 0 := by
    rw [tripleCross]
    ring1
  constructor
  · apply Group.eq_of_sub_eq_zero
    calc
      (c₃ + c₁ + c₂ - 2 * c₁ * c₂ - 1) ^ 2 -
          4 * c₁ * c₂ * (1 - c₁) * (1 - c₂) =
        (c₁ + c₂ + c₃ - 1) ^ 2 - 4 * c₁ * c₂ * c₃ := by
          ring1
      _ = 0 := differenceZero
  · dsimp only
    apply Group.eq_of_sub_eq_zero
    calc
      (c₃ - (c₁ * c₂ + (1 - c₁) * (1 - c₂))) ^ 2 -
          4 * c₁ * c₂ * (1 - c₁) * (1 - c₂) =
        (c₁ + c₂ + c₃ - 1) ^ 2 - 4 * c₁ * c₂ * c₃ := by
          ring1
      _ = 0 := differenceZero

/-- The four-by-four determinant displayed in Exercise 7.8, expanded along its first row. -/
@[expose] def tripleCrossDeterminant (c₁ c₂ c₃ : K) : K :=
  (1 * (1 * 2 - 1 * 1) - c₃ * (c₃ * 2 - 1 * 1) +
      1 * (c₃ * 1 - 1 * 1)) -
    c₁ * (c₁ * (1 * 2 - 1 * 1) - c₃ * (c₂ * 2 - 1 * 1) +
      1 * (c₂ * 1 - 1 * 1)) +
    c₂ * (c₁ * (c₃ * 2 - 1 * 1) - 1 * (c₂ * 2 - 1 * 1) +
      1 * (c₂ * 1 - c₃ * 1)) -
    (c₁ * (c₃ * 1 - 1 * 1) - 1 * (c₂ * 1 - 1 * 1) +
      c₃ * (c₂ * 1 - c₃ * 1))

/-- Exercise 7.8: determinant form of the Triple cross polynomial. -/
theorem exercise_7_8 (c₁ c₂ c₃ : K) :
    (c₁ + c₂ + c₃ - 1) ^ 2 - 4 * c₁ * c₂ * c₃ =
      -tripleCrossDeterminant c₁ c₂ c₃ := by
  unfold tripleCrossDeterminant
  ring1
end Purelib.Geometry.Trigonometry.Cross.Triple

end

end
