module
public import Purelib.Algebra.Group.Basic
public import Purelib.Data.Nat.Order
public import Purelib.Algebra.Group.Negation

public import Purelib.Geometry.Trigonometry.Spread.Triple
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

open Purelib.Geometry.Trigonometry.Spread.Triple

section
public section

/-!
# Divine Proportions, remaining Chapter 12 exercises

This module completes the reader exercises: the finite chord argument from
Exercise 12.1, the null-side circumcenter argument from Exercise 12.4, and the
remaining exact polynomial and spread calculations.
-/

namespace Purelib.Geometry.Trigonometry.Spread.Triple.AlternateRoot

open Purelib.Algebra

variable {K : Type*} [ExplicitField K]

/-- Two distinct roots of the same Triple-spread quadratic have the displayed sum. This is the finite “other root”
calculation used in Exercise 12.7. -/
theorem alternate_spread_root_sum
    [DecidableEq K]
    (firstRoot secondRoot fixedFirst fixedSecond : K)
    (firstTriple : TripleSpread.SpreadTriple firstRoot fixedFirst fixedSecond)
    (secondTriple : TripleSpread.SpreadTriple secondRoot fixedFirst fixedSecond)
    (rootsDistinct : secondRoot ≠ firstRoot) :
    secondRoot + firstRoot =
      2 * (fixedFirst + fixedSecond - 2 * fixedFirst * fixedSecond) := by
  have differenceNonzero : secondRoot - firstRoot ≠ 0 := by
    intro differenceZero
    apply rootsDistinct
    exact Group.eq_of_sub_eq_zero differenceZero
  have productZero :
      (secondRoot - firstRoot) *
        (secondRoot + firstRoot -
          2 * (fixedFirst + fixedSecond -
            2 * fixedFirst * fixedSecond)) = 0 := by
    calc
      (secondRoot - firstRoot) *
          (secondRoot + firstRoot -
            2 * (fixedFirst + fixedSecond -
              2 * fixedFirst * fixedSecond)) =
        -(TripleSpread.tripleSpreadFunction secondRoot fixedFirst fixedSecond -
          TripleSpread.tripleSpreadFunction firstRoot fixedFirst fixedSecond) := by
            unfold TripleSpread.tripleSpreadFunction
            ring1
      _ = 0 := by
        unfold TripleSpread.SpreadTriple at firstTriple secondTriple
        rw [firstTriple, secondTriple]
        ring1
  apply Group.eq_of_sub_eq_zero
  by_cases sumDifferenceZero :
      secondRoot + firstRoot -
        2 * (fixedFirst + fixedSecond -
          2 * fixedFirst * fixedSecond) = 0
  · exact sumDifferenceZero
  · exact False.elim
      ((ExplicitField.mul_ne_zero differenceNonzero sumDifferenceZero)
        productZero)

/-- Exercise 12.7. The two Triple-spread certificates say that `u₁` and `r₁` are the two branches obtained from the same
other two line spreads; the explicit inequality selects the other branch. -/
theorem exercise_12_7
    [DecidableEq K]
    (u₁ u₂ u₃ r₁ : K) (twoNonzero : (2 : K) ≠ 0)
    (firstTriple : TripleSpread.SpreadTriple u₁ u₂ (1 - u₃))
    (secondTriple : TripleSpread.SpreadTriple r₁ u₂ (1 - u₃))
    (otherBranch : r₁ ≠ u₁)
    (firstNotHalf : u₁ ≠ (1 : K) / 2) :
    r₁ =
      (u₁ - 2 * u₂ - 2 * u₃ + 2 * u₂ ^ 2 + 2 * u₃ ^ 2) /
        (2 * u₁ - 1) := by
  have rootSum := alternate_spread_root_sum u₁ r₁ u₂ (1 - u₃)
    firstTriple secondTriple otherBranch
  have rootEquation :
      r₁ = 2 * (u₂ + (1 - u₃) - 2 * u₂ * (1 - u₃)) - u₁ := by
    calc
      r₁ = (r₁ + u₁) - u₁ := by ring1
      _ = 2 * (u₂ + (1 - u₃) - 2 * u₂ * (1 - u₃)) - u₁ := by
        rw [rootSum]
  have denominatorNonzero : 2 * u₁ - 1 ≠ 0 := by
    intro denominatorZero
    apply firstNotHalf
    have twiceFirst : 2 * u₁ = 1 := Group.eq_of_sub_eq_zero denominatorZero
    have twoCancel : (2 : K) * (2 : K)⁻¹ = 1 :=
      ExplicitField.mul_inv_cancel 2 twoNonzero
    simp only [ExplicitField.div_eq_mul_inv]
    calc
      u₁ = u₁ * 1 := by ring1
      _ = u₁ * ((2 : K) * (2 : K)⁻¹) := by rw [twoCancel]
      _ = (2 * u₁) * (2 : K)⁻¹ := by ring1
      _ = 1 * (2 : K)⁻¹ := by rw [twiceFirst]
  let numerator :=
    u₁ - 2 * u₂ - 2 * u₃ + 2 * u₂ ^ 2 + 2 * u₃ ^ 2
  have cleared : (2 * u₁ - 1) * r₁ = numerator := by
    apply Group.eq_of_sub_eq_zero
    calc
      (2 * u₁ - 1) * r₁ - numerator =
          (2 * u₁ - 1) *
              (2 * (u₂ + (1 - u₃) - 2 * u₂ * (1 - u₃)) - u₁) -
            numerator := by rw [rootEquation]
      _ = 2 * TripleSpread.tripleSpreadFunction u₁ u₂ (1 - u₃) := by
        unfold numerator TripleSpread.tripleSpreadFunction
        ring1
      _ = 0 := by
        unfold TripleSpread.SpreadTriple at firstTriple
        rw [firstTriple]
        ring1
  have denominatorCancel :
      (2 * u₁ - 1) * (2 * u₁ - 1)⁻¹ = (1 : K) :=
    ExplicitField.mul_inv_cancel _ denominatorNonzero
  unfold numerator at cleared
  simp only [ExplicitField.div_eq_mul_inv]
  calc
    r₁ = r₁ * 1 := by ring1
    _ = r₁ * ((2 * u₁ - 1) * (2 * u₁ - 1)⁻¹) := by
      rw [denominatorCancel]
    _ = ((2 * u₁ - 1) * r₁) * (2 * u₁ - 1)⁻¹ := by ring1
    _ = (u₁ - 2 * u₂ - 2 * u₃ + 2 * u₂ ^ 2 + 2 * u₃ ^ 2) *
          (2 * u₁ - 1)⁻¹ := by rw [cleared]
end Purelib.Geometry.Trigonometry.Spread.Triple.AlternateRoot

end

end
