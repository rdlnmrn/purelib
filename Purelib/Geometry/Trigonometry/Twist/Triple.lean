module
public import Purelib.Algebra.Group.Basic
public import Purelib.Data.Nat.Order
public import Purelib.Algebra.Group.Negation
public import Purelib.Algebra.Field.ExplicitField
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
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

section
public section

/-!
# Divine Proportions, §§7.3 and 9.2: turns and the triple twist formula

The oriented turn is retained as the explicit determinant/dot quotient.  Its
cyclic three-line identity is linear; squaring that finite identity gives the
book's Triple twist formula without separating null and non-null cases.
-/

namespace Purelib.Geometry.Trigonometry.Twist.Triple

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- Exercise 7.12: squaring any triple-turn relation gives a triple-twist relation. -/
theorem exercise_7_12
    (r₁ r₂ r₃ : K) (turnEquation : r₁ + r₂ + r₃ = r₁ * r₂ * r₃) :
    let t₁ := r₁ ^ 2
    let t₂ := r₂ ^ 2
    let t₃ := r₃ ^ 2
    (t₁ + t₂ + t₃ - t₁ * t₂ * t₃) ^ 2 =
      4 * (t₁ * t₂ + t₁ * t₃ + t₂ * t₃ + 2 * t₁ * t₂ * t₃) := by
  dsimp only
  have turnDifference : r₁ + r₂ + r₃ - r₁ * r₂ * r₃ = 0 := by
    rw [turnEquation]
    ring1
  have differenceZero :
      (r₁ ^ 2 + r₂ ^ 2 + r₃ ^ 2 -
            r₁ ^ 2 * r₂ ^ 2 * r₃ ^ 2) ^ 2 -
          4 * (r₁ ^ 2 * r₂ ^ 2 + r₁ ^ 2 * r₃ ^ 2 +
            r₂ ^ 2 * r₃ ^ 2 + 2 * r₁ ^ 2 * r₂ ^ 2 * r₃ ^ 2) = 0 := by
    calc
      (r₁ ^ 2 + r₂ ^ 2 + r₃ ^ 2 -
              r₁ ^ 2 * r₂ ^ 2 * r₃ ^ 2) ^ 2 -
            4 * (r₁ ^ 2 * r₂ ^ 2 + r₁ ^ 2 * r₃ ^ 2 +
              r₂ ^ 2 * r₃ ^ 2 + 2 * r₁ ^ 2 * r₂ ^ 2 * r₃ ^ 2) =
        -(r₁ + r₂ + r₃ - r₁ * r₂ * r₃) *
          (r₁ + r₂ - r₃ + r₁ * r₂ * r₃) *
          (r₁ - r₂ + r₃ + r₁ * r₂ * r₃) *
          (-r₁ + r₂ + r₃ + r₁ * r₂ * r₃) := by ring1
      _ = 0 := by rw [turnDifference]; ring1
  exact Group.eq_of_sub_eq_zero differenceZero

/-- Exercise 7.10: the Triple twist relation as a quadratic in `t₃`, followed by its denominator-free completed-square
normal form. -/
theorem exercise_7_10
    (t₁ t₂ t₃ : K)
    (tripleTwist :
      (t₁ + t₂ + t₃ - t₁ * t₂ * t₃) ^ 2 =
        4 * (t₁ * t₂ + t₁ * t₃ + t₂ * t₃ +
          2 * t₁ * t₂ * t₃)) :
    (1 - t₁ * t₂) ^ 2 * t₃ ^ 2 -
          2 * ((t₁ + t₂) * (1 + t₁ * t₂) +
            4 * t₁ * t₂) * t₃ +
          (t₁ - t₂) ^ 2 = 0 ∧
      (((1 - t₁ * t₂) ^ 2 * t₃ -
          ((t₁ + t₂) * (1 + t₁ * t₂) +
            4 * t₁ * t₂)) ^ 2 =
        4 * t₁ * t₂ *
          ((1 + t₁) * (1 + t₂)) ^ 2) := by
  have twistDifference :
      (t₁ + t₂ + t₃ - t₁ * t₂ * t₃) ^ 2 -
          4 * (t₁ * t₂ + t₁ * t₃ + t₂ * t₃ +
            2 * t₁ * t₂ * t₃) = 0 := by
    rw [tripleTwist]
    ring1
  have quadraticZero :
      (1 - t₁ * t₂) ^ 2 * t₃ ^ 2 -
          2 * ((t₁ + t₂) * (1 + t₁ * t₂) +
            4 * t₁ * t₂) * t₃ +
          (t₁ - t₂) ^ 2 = 0 := by
    calc
      (1 - t₁ * t₂) ^ 2 * t₃ ^ 2 -
            2 * ((t₁ + t₂) * (1 + t₁ * t₂) +
              4 * t₁ * t₂) * t₃ +
            (t₁ - t₂) ^ 2 =
        (t₁ + t₂ + t₃ - t₁ * t₂ * t₃) ^ 2 -
          4 * (t₁ * t₂ + t₁ * t₃ + t₂ * t₃ +
            2 * t₁ * t₂ * t₃) := by ring1
      _ = 0 := twistDifference
  refine ⟨quadraticZero, ?_⟩
  apply Group.eq_of_sub_eq_zero
  calc
    ((1 - t₁ * t₂) ^ 2 * t₃ -
          ((t₁ + t₂) * (1 + t₁ * t₂) +
            4 * t₁ * t₂)) ^ 2 -
        4 * t₁ * t₂ *
          ((1 + t₁) * (1 + t₂)) ^ 2 =
      (1 - t₁ * t₂) ^ 2 *
        ((1 - t₁ * t₂) ^ 2 * t₃ ^ 2 -
          2 * ((t₁ + t₂) * (1 + t₁ * t₂) +
            4 * t₁ * t₂) * t₃ +
          (t₁ - t₂) ^ 2) := by ring1
    _ = 0 := by rw [quadraticZero]; ring1

/-- Exercise 7.11: the symmetric-looking alternative form of the Triple twist relation. -/
theorem exercise_7_11
    (t₁ t₂ t₃ : K)
    (tripleTwist :
      (t₁ + t₂ + t₃ - t₁ * t₂ * t₃) ^ 2 =
        4 * (t₁ * t₂ + t₁ * t₃ + t₂ * t₃ +
          2 * t₁ * t₂ * t₃)) :
    (t₁ + t₂ - t₃ - t₁ * t₂ * t₃) ^ 2 =
      4 * t₁ * t₂ * (1 + t₃) ^ 2 := by
  apply Group.eq_of_sub_eq_zero
  calc
    (t₁ + t₂ - t₃ - t₁ * t₂ * t₃) ^ 2 -
        4 * t₁ * t₂ * (1 + t₃) ^ 2 =
      (t₁ + t₂ + t₃ - t₁ * t₂ * t₃) ^ 2 -
        4 * (t₁ * t₂ + t₁ * t₃ + t₂ * t₃ +
          2 * t₁ * t₂ * t₃) := by ring1
    _ = 0 := by rw [tripleTwist]; ring1

end Purelib.Geometry.Trigonometry.Twist.Triple

end

end
