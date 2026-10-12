module
public import Purelib.Algebra.Group.Basic
public import Purelib.Data.Nat.Order
public import Purelib.Algebra.Group.Negation
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Geometry.Trigonometry.QuadTriple.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Data.Rat.Fraction.Field
public import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

section
open Purelib.Algebra
open Purelib.Data

-- These owned adapters retain the complete original operation dictionaries.
attribute [local instance 2000] Group.Negation.subNegZeroMonoid
  Nat.successorNeZero Nat.successorAtLeastTwo

open Purelib.Data.Rat

open Purelib.Geometry.Trigonometry

section
public section

/-!
# Divine Proportions, Exercise 5.13

The source's maximum claim is stated without a supremum or completed real
object.  For every requested third quadrance, quadrea is bounded above by
`4 Q₁ Q₂`; equality holds exactly at the Pythagorean value.  The geometric
form then identifies equality with perpendicularity at the third vertex.
-/

namespace Purelib.Geometry.Trigonometry.QuadTriple.RationalBounds.ExerciseFiveThirteen

section

/-- The finite scalar content of Exercise 5.13: with `q₁` and `q₂` fixed, every requested `q₃` gives quadrea at most
`4q₁q₂`, and equality holds exactly when `q₁+q₂=q₃`. -/
theorem exercise_5_13_scalar (q₁ q₂
  q₃ : Fraction.Rational) :
    QuadTriple.Basic.archimedesFunction q₁ q₂ q₃ ≤ 4 * q₁ * q₂ ∧
      (QuadTriple.Basic.archimedesFunction q₁ q₂ q₃ = 4 * q₁ * q₂ ↔
        q₁ + q₂ = q₃) := by
  have upperBound : QuadTriple.Basic.archimedesFunction q₁ q₂ q₃ ≤ 4 * q₁ * q₂ := by
    apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
    calc
      0 ≤ (q₁ + q₂ - q₃) ^ 2 :=
        Fraction.Order.Arithmetic.sq_nonneg_direct _
      _ = 4 * q₁ * q₂ - QuadTriple.Basic.archimedesFunction q₁ q₂ q₃ := by
        unfold QuadTriple.Basic.archimedesFunction
        ring1
  refine ⟨upperBound, ?_⟩
  constructor
  · intro maximal
    have squareZero : (q₁ + q₂ - q₃) ^ 2 = 0 := by
      calc
        (q₁ + q₂ - q₃) ^ 2 =
            4 * q₁ * q₂ - QuadTriple.Basic.archimedesFunction q₁ q₂ q₃ := by
              unfold QuadTriple.Basic.archimedesFunction
              ring1
        _ = 0 := by rw [maximal]; ring1
    have differenceZero :=
      (Fraction.Order.Arithmetic.sq_eq_zero_direct
        (q₁ + q₂ - q₃)).1 squareZero
    exact Group.eq_of_sub_eq_zero differenceZero
  · intro pythagoras
    unfold QuadTriple.Basic.archimedesFunction
    rw [← pythagoras]
    ring1
end

end Purelib.Geometry.Trigonometry.QuadTriple.RationalBounds.ExerciseFiveThirteen

end

end
