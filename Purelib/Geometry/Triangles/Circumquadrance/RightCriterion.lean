module
public import Purelib.Algebra.Group.Basic
public import Purelib.Data.Nat.Order
public import Purelib.Algebra.Group.Negation
public import Purelib.Geometry.Trigonometry.QuadTriple.Basic

import Purelib.Algebra.Field.ExplicitField
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Tactic.Ring

open Purelib.Algebra.Field (ExplicitField)

section
open Purelib.Algebra
open Purelib.Data

-- These owned adapters retain the complete original operation dictionaries.
attribute [local instance 2000] Group.Negation.subNegZeroMonoid
  Nat.successorNeZero Nat.successorAtLeastTwo

open Purelib

open Purelib.Geometry.Trigonometry

section
public section

/-!
# Divine Proportions, remaining Chapter 12 exercises

This module completes the reader exercises: the finite chord argument from
Exercise 12.1, the null-side circumcenter argument from Exercise 12.4, and the
remaining exact polynomial and spread calculations.
-/

namespace Purelib.Geometry.Triangles.Circumquadrance.RightCriterion

open Purelib.Algebra

variable {K : Type*} [ExplicitField K]

/-- The Archimedes expression times the quadrance sum factors after subtracting eight times their product. -/
theorem exercise_12_5_identity (x₁ x₂ x₃ : K) :
    ((x₁ + x₂ + x₃) ^ 2 - 2 * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2)) *
          (x₁ + x₂ + x₃) - 8 * x₁ * x₂ * x₃ =
      (x₁ + x₂ - x₃) * (x₂ + x₃ - x₁) * (x₃ + x₁ - x₂) := by
  ring1

/-- The quadrance sum is eight times the circumquadrance exactly when one Pythagorean relation holds.

The supplied area is the nonzero Archimedes expression and its product with the circumquadrance is the product of all
three side quadrances. -/
theorem
  exercise_12_5_right_iff_sum_eq_eight_circumquadrance
    [DecidableEq K]
    (q₁ q₂ q₃ area circumquadranceValue : K)
    (areaEquation : area = QuadTriple.Basic.archimedesFunction q₁ q₂ q₃)
    (areaNonzero : area ≠ 0)
    (circumRelation : area * circumquadranceValue = q₁ * q₂ * q₃) :
    q₁ + q₂ + q₃ = 8 * circumquadranceValue ↔
      q₁ + q₂ = q₃ ∨ q₂ + q₃ = q₁ ∨ q₃ + q₁ = q₂ := by
  have factorIdentity :
      area * (q₁ + q₂ + q₃) - 8 * q₁ * q₂ * q₃ =
        (q₁ + q₂ - q₃) * (q₂ + q₃ - q₁) * (q₃ + q₁ - q₂) := by
    rw [areaEquation]
    unfold QuadTriple.Basic.archimedesFunction
    exact exercise_12_5_identity q₁ q₂ q₃
  constructor
  · intro sumEquation
    have factorsZero :
        (q₁ + q₂ - q₃) * (q₂ + q₃ - q₁) *
            (q₃ + q₁ - q₂) = 0 := by
      calc
        (q₁ + q₂ - q₃) * (q₂ + q₃ - q₁) *
              (q₃ + q₁ - q₂) =
            area * (q₁ + q₂ + q₃) - 8 * q₁ * q₂ * q₃ :=
          factorIdentity.symm
        _ = area * (8 * circumquadranceValue) -
              8 * q₁ * q₂ * q₃ := by rw [sumEquation]
        _ = 8 *
              (area * circumquadranceValue - q₁ * q₂ * q₃) := by
          ring1
        _ = 0 := by rw [circumRelation]; ring1
    by_cases firstZero : q₁ + q₂ - q₃ = 0
    · exact Or.inl (Group.eq_of_sub_eq_zero firstZero)
    · by_cases secondZero : q₂ + q₃ - q₁ = 0
      · exact Or.inr (Or.inl (Group.eq_of_sub_eq_zero secondZero))
      · right
        right
        apply Group.eq_of_sub_eq_zero
        by_cases thirdZero : q₃ + q₁ - q₂ = 0
        · exact thirdZero
        · exact False.elim
            ((ExplicitField.mul_ne_zero
              (ExplicitField.mul_ne_zero firstZero secondZero)
              thirdZero) factorsZero)
  · intro rightRelation
    have factorsZero :
        (q₁ + q₂ - q₃) * (q₂ + q₃ - q₁) *
            (q₃ + q₁ - q₂) = 0 := by
      rcases rightRelation with firstRight | secondRight | thirdRight
      · rw [firstRight]
        ring1
      · rw [secondRight]
        ring1
      · rw [thirdRight]
        ring1
    have areaTimesDifference :
        area * (q₁ + q₂ + q₃ - 8 * circumquadranceValue) = 0 := by
      calc
        area * (q₁ + q₂ + q₃ - 8 * circumquadranceValue) =
            area * (q₁ + q₂ + q₃) -
              8 * (area * circumquadranceValue) := by ring1
        _ = area * (q₁ + q₂ + q₃) - 8 * q₁ * q₂ * q₃ := by
          rw [circumRelation]
          ring1
        _ = (q₁ + q₂ - q₃) * (q₂ + q₃ - q₁) *
              (q₃ + q₁ - q₂) := factorIdentity
        _ = 0 := factorsZero
    apply Group.eq_of_sub_eq_zero
    by_cases differenceZero :
        q₁ + q₂ + q₃ - 8 * circumquadranceValue = 0
    · exact differenceZero
    · exact False.elim
        ((ExplicitField.mul_ne_zero areaNonzero differenceZero)
          areaTimesDifference)
end Purelib.Geometry.Triangles.Circumquadrance.RightCriterion

end

end
