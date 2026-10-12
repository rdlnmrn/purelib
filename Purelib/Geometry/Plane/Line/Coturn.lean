module
public import Purelib.Data.Nat.Order
public import Purelib.Algebra.Group.Negation
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Geometry.Plane.Line.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Purelib.Tactic.Ring

open Purelib.Algebra.Field (ExplicitField)

section
open Purelib.Algebra
open Purelib.Data

-- These owned adapters retain the complete original operation dictionaries.
attribute [local instance 2000] Group.Negation.subNegZeroMonoid
  Nat.successorNeZero Nat.successorAtLeastTwo

open Purelib

open Purelib.Geometry.Plane

section
public section

/-!
# Divine Proportions, Chapter 9: the triple coturn formula

Exercise 9.1 reverses the numerator and denominator in the turn quotient.
Its cyclic identity is first proved as a direct polynomial equation in the
six displayed line coefficients; the three nonparallel certificates are used
only to recover the source's quotients.
-/

namespace Purelib.Geometry.Plane.Line.Coturn

variable {K : Type*} [ExplicitField K]

/-- Coturn of an ordered pair of nonparallel lines. -/
@[expose] def coturn (first second : Plane.Line K)
    (_notParallel : ¬ first.Parallel second) : K :=
  (first.a * second.a + first.b * second.b) /
    (first.a * second.b - second.a * first.b)

/-- Reversing the ordered line pair negates its coturn. -/
theorem coturn_reverse
    (first second : Plane.Line K)
    (firstSecondNotParallel : ¬ first.Parallel second)
    (secondFirstNotParallel : ¬ second.Parallel first) :
    coturn second first secondFirstNotParallel =
      -coturn first second firstSecondNotParallel := by
  unfold coturn
  simp only [ExplicitField.div_eq_mul_inv]
  have inverseNegative := ExplicitField.inv_neg
    (first.a * second.b - second.a * first.b)
  rw [show second.a * first.b - first.a * second.b =
      -(first.a * second.b - second.a * first.b) by ring1,
    inverseNegative]
  ring1

/-- Denominator-free core of the Triple coturn formula. -/
theorem triple_coturn_formula_cleared
    (first second third : Plane.Line K) :
    (second.a * third.a + second.b * third.b) *
          (third.a * first.a + third.b * first.b) *
          (first.a * second.b - second.a * first.b) +
        (third.a * first.a + third.b * first.b) *
          (first.a * second.a + first.b * second.b) *
          (second.a * third.b - third.a * second.b) +
        (first.a * second.a + first.b * second.b) *
          (second.a * third.a + second.b * third.b) *
          (third.a * first.b - first.a * third.b) =
      (second.a * third.b - third.a * second.b) *
        (third.a * first.b - first.a * third.b) *
        (first.a * second.b - second.a * first.b) := by
  ring1

/-- The sum of the three pairwise products of cyclic coturns is one.

Each consecutive pair of displayed lines is nonparallel, so the three determinant denominators are nonzero. -/
theorem exercise_9_1
    (first second third : Plane.Line K)
    (firstSecondNotParallel : ¬ first.Parallel second)
    (secondThirdNotParallel : ¬ second.Parallel third)
    (thirdFirstNotParallel : ¬ third.Parallel first) :
    let o₁ := coturn second third secondThirdNotParallel
    let o₂ := coturn third first thirdFirstNotParallel
    let o₃ := coturn first second firstSecondNotParallel
    o₁ * o₂ + o₂ * o₃ + o₃ * o₁ = 1 := by
  dsimp only
  let firstNumerator := second.a * third.a + second.b * third.b
  let secondNumerator := third.a * first.a + third.b * first.b
  let thirdNumerator := first.a * second.a + first.b * second.b
  let firstDenominator := second.a * third.b - third.a * second.b
  let secondDenominator := third.a * first.b - first.a * third.b
  let thirdDenominator := first.a * second.b - second.a * first.b
  let denominator := firstDenominator * secondDenominator * thirdDenominator
  have firstDenominatorNonzero : firstDenominator ≠ 0 :=
    secondThirdNotParallel
  have secondDenominatorNonzero : secondDenominator ≠ 0 :=
    thirdFirstNotParallel
  have thirdDenominatorNonzero : thirdDenominator ≠ 0 :=
    firstSecondNotParallel
  have denominatorNonzero : denominator ≠ 0 :=
    ExplicitField.mul_ne_zero
      (ExplicitField.mul_ne_zero firstDenominatorNonzero
        secondDenominatorNonzero)
      thirdDenominatorNonzero
  have firstCancel :
      firstNumerator / firstDenominator * firstDenominator =
        firstNumerator :=
    ExplicitField.div_mul_cancel _ firstDenominatorNonzero
  have secondCancel :
      secondNumerator / secondDenominator * secondDenominator =
        secondNumerator :=
    ExplicitField.div_mul_cancel _ secondDenominatorNonzero
  have thirdCancel :
      thirdNumerator / thirdDenominator * thirdDenominator =
        thirdNumerator :=
    ExplicitField.div_mul_cancel _ thirdDenominatorNonzero
  have clearedIdentity :
      firstNumerator * secondNumerator * thirdDenominator +
          secondNumerator * thirdNumerator * firstDenominator +
          thirdNumerator * firstNumerator * secondDenominator =
        firstDenominator * secondDenominator * thirdDenominator := by
    exact triple_coturn_formula_cleared first second third
  unfold coturn
  change
    firstNumerator / firstDenominator *
          (secondNumerator / secondDenominator) +
        secondNumerator / secondDenominator *
          (thirdNumerator / thirdDenominator) +
        thirdNumerator / thirdDenominator *
          (firstNumerator / firstDenominator) = 1
  apply ExplicitField.eq_of_mul_eq_mul_right denominatorNonzero
  calc
    (firstNumerator / firstDenominator *
            (secondNumerator / secondDenominator) +
          secondNumerator / secondDenominator *
            (thirdNumerator / thirdDenominator) +
          thirdNumerator / thirdDenominator *
            (firstNumerator / firstDenominator)) * denominator =
        (firstNumerator / firstDenominator * firstDenominator) *
            (secondNumerator / secondDenominator * secondDenominator) *
            thirdDenominator +
          (secondNumerator / secondDenominator * secondDenominator) *
            (thirdNumerator / thirdDenominator * thirdDenominator) *
            firstDenominator +
          (thirdNumerator / thirdDenominator * thirdDenominator) *
            (firstNumerator / firstDenominator * firstDenominator) *
            secondDenominator := by
      unfold denominator
      ring1
    _ = firstNumerator * secondNumerator * thirdDenominator +
          secondNumerator * thirdNumerator * firstDenominator +
          thirdNumerator * firstNumerator * secondDenominator := by
      rw [firstCancel, secondCancel, thirdCancel]
    _ = firstDenominator * secondDenominator * thirdDenominator :=
      clearedIdentity
    _ = 1 * denominator := by unfold denominator; ring1

end Purelib.Geometry.Plane.Line.Coturn

end

end
