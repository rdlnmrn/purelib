module
public import Purelib.Algebra.Group.Basic
public import Purelib.Data.Nat.Order
public import Purelib.Algebra.Group.Negation
import Purelib.Algebra.Field.Cancellation
import Purelib.Algebra.Field.ExplicitField
import Purelib.Geometry.Plane.Line.Basic
public import Purelib.Geometry.Plane.Line.Turn.Basic
import Purelib.Geometry.Plane.Line.Turn.Triple
public import Purelib.Geometry.Trigonometry.Turn.Composition
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

open Purelib.Geometry.Plane

open Purelib.Geometry.Plane.Line

open Purelib.Geometry.Plane.Line.Basic

open Purelib.Geometry.Plane.Line.Turn

open Purelib.Geometry.Trigonometry.Turn

section
public section

/-!
# Divine Proportions, §§7.3 and 9.2: turns and the triple twist formula

The oriented turn is retained as the explicit determinant/dot quotient.  Its
cyclic three-line identity is linear; squaring that finite identity gives the
book's Triple twist formula without separating null and non-null cases.
-/

namespace Purelib.Geometry.Plane.Line.Turn.Composition

variable {K : Type*} [ExplicitField K]

/-- Exercise 9.2: two successive finite turns compose by the rational addition law. The displayed premise records the
source's tacit exceptional case `1-u*v = 0`; over fields admitting null directions it does not follow merely from the
three pairwise turns being defined. -/
theorem exercise_9_2
    (first second third : Plane.Line K)
    (firstSecondNotPerpendicular : ¬ first.Perpendicular second)
    (secondThirdNotPerpendicular : ¬ second.Perpendicular third)
    (firstThirdNotPerpendicular : ¬ first.Perpendicular third)
    (compositionDenominatorNonzero :
      1 - Turn.Basic.turn first second firstSecondNotPerpendicular *
        Turn.Basic.turn second third secondThirdNotPerpendicular ≠ 0) :
    Turn.Basic.turn first third firstThirdNotPerpendicular =
      Composition.turnComposition
        (Turn.Basic.turn first second firstSecondNotPerpendicular)
        (Turn.Basic.turn second third secondThirdNotPerpendicular) := by
  have thirdFirstNotPerpendicular : ¬ third.Perpendicular first := by
    intro perpendicular
    exact firstThirdNotPerpendicular (Plane.Line.perpendicular_symm perpendicular)
  let u := Turn.Basic.turn first second firstSecondNotPerpendicular
  let v := Turn.Basic.turn second third secondThirdNotPerpendicular
  let w := Turn.Basic.turn first third firstThirdNotPerpendicular
  have reverseTurn :
      Turn.Basic.turn third first thirdFirstNotPerpendicular = -w := by
    exact Turn.Basic.turn_reverse first third firstThirdNotPerpendicular
      thirdFirstNotPerpendicular
  have cyclicEquation :=
    Triple.triple_turn_formula first second third firstSecondNotPerpendicular
      secondThirdNotPerpendicular thirdFirstNotPerpendicular
  change v + Turn.Basic.turn third first thirdFirstNotPerpendicular + u =
      v * Turn.Basic.turn third first thirdFirstNotPerpendicular * u at cyclicEquation
  rw [reverseTurn] at cyclicEquation
  change 1 - u * v ≠ 0 at compositionDenominatorNonzero
  have clearedComposition : w * (1 - u * v) = u + v := by
    have differenceZero : w * (1 - u * v) - (u + v) = 0 := by
      calc
        w * (1 - u * v) - (u + v) =
            -((v + -w + u) - v * (-w) * u) := by ring1
        _ = 0 := by rw [cyclicEquation]; ring1
    exact Group.eq_of_sub_eq_zero differenceZero
  change w = Composition.turnComposition u v
  unfold Composition.turnComposition
  apply ExplicitField.eq_of_mul_eq_mul_right compositionDenominatorNonzero
  calc
    w * (1 - u * v) = u + v := clearedComposition
    _ = ((u + v) / (1 - u * v)) * (1 - u * v) :=
      (ExplicitField.div_mul_cancel (u + v)
        compositionDenominatorNonzero).symm

/-- Exercise 9.2's equal-successive-turn specialization. -/
theorem exercise_9_2_equal_turns
    (first second third : Plane.Line K)
    (firstSecondNotPerpendicular : ¬ first.Perpendicular second)
    (secondThirdNotPerpendicular : ¬ second.Perpendicular third)
    (firstThirdNotPerpendicular : ¬ first.Perpendicular third)
    (turnsEqual :
      Turn.Basic.turn first second firstSecondNotPerpendicular =
        Turn.Basic.turn second third secondThirdNotPerpendicular)
    (compositionDenominatorNonzero :
      1 - Turn.Basic.turn first second firstSecondNotPerpendicular *
        Turn.Basic.turn second third secondThirdNotPerpendicular ≠ 0) :
    Turn.Basic.turn first third firstThirdNotPerpendicular =
      (2 * Turn.Basic.turn first second firstSecondNotPerpendicular) /
        (1 - Turn.Basic.turn first second firstSecondNotPerpendicular ^ 2) := by
  calc
    Turn.Basic.turn first third firstThirdNotPerpendicular =
        Composition.turnComposition
          (Turn.Basic.turn first second firstSecondNotPerpendicular)
          (Turn.Basic.turn second third secondThirdNotPerpendicular) :=
      exercise_9_2 first second third firstSecondNotPerpendicular
        secondThirdNotPerpendicular firstThirdNotPerpendicular
        compositionDenominatorNonzero
    _ = (2 * Turn.Basic.turn first second firstSecondNotPerpendicular) /
        (1 - Turn.Basic.turn first second firstSecondNotPerpendicular ^ 2) := by
      rw [← turnsEqual]
      unfold Composition.turnComposition
      congr 1 <;> ring1
end Purelib.Geometry.Plane.Line.Turn.Composition

end

end
