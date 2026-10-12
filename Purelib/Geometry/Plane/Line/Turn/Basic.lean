module
public import Purelib.Data.Nat.Order
public import Purelib.Algebra.Group.Negation
import Purelib.Algebra.Field.ExplicitField
import Purelib.Geometry.Plane.Line.Basic
public import Purelib.Geometry.Plane.Line.Twist
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
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

section
public section

/-!
# Divine Proportions, §§7.3 and 9.2: turns and the triple twist formula

The oriented turn is retained as the explicit determinant/dot quotient.  Its
cyclic three-line identity is linear; squaring that finite identity gives the
book's Triple twist formula without separating null and non-null cases.
-/

namespace Purelib.Geometry.Plane.Line.Turn.Basic

variable {K : Type*} [ExplicitField K]

/-- Turn of an ordered pair of non-perpendicular lines. -/
@[expose] def turn (first second : Plane.Line K)
    (_notPerpendicular : ¬ first.Perpendicular second) : K :=
  (first.a * second.b - second.a * first.b) /
    (first.a * second.a + first.b * second.b)

/-- Reversing the ordered pair of lines negates its turn. -/
theorem turn_reverse
    (first second : Plane.Line K)
    (firstSecondNotPerpendicular : ¬ first.Perpendicular second)
    (secondFirstNotPerpendicular : ¬ second.Perpendicular first) :
    turn second first secondFirstNotPerpendicular =
      -turn first second firstSecondNotPerpendicular := by
  have denominatorEqual :
      second.a * first.a + second.b * first.b =
        first.a * second.a + first.b * second.b := by ring1
  unfold turn
  rw [denominatorEqual]
  simp only [ExplicitField.div_eq_mul_inv]
  ring1

/-- A twist is the square of its oriented turn. -/
theorem twist_eq_turn_square
    (first second : Plane.Line K)
    (notPerpendicular : ¬ first.Perpendicular second) :
    Twist.twist first second notPerpendicular =
      turn first second notPerpendicular ^ 2 := by
  let determinant := first.a * second.b - second.a * first.b
  let dot := first.a * second.a + first.b * second.b
  have dotNonzero : dot ≠ 0 := notPerpendicular
  have dotSquareNonzero : dot ^ 2 ≠ 0 := by
    simpa [pow_two] using
      (ExplicitField.mul_ne_zero dotNonzero dotNonzero)
  unfold Twist.twist turn
  change determinant ^ 2 / dot ^ 2 = (determinant / dot) ^ 2
  apply ExplicitField.eq_of_mul_eq_mul_right dotSquareNonzero
  calc
    (determinant ^ 2 / dot ^ 2) * dot ^ 2 = determinant ^ 2 :=
      ExplicitField.div_mul_cancel (determinant ^ 2) dotSquareNonzero
    _ = ((determinant / dot) * dot) ^ 2 := by
      rw [ExplicitField.div_mul_cancel determinant dotNonzero]
    _ = (determinant / dot) ^ 2 * dot ^ 2 := by ring1

/-- Twist is symmetric although turn is antisymmetric. -/
theorem twist_symm
    (first second : Plane.Line K)
    (firstSecondNotPerpendicular : ¬ first.Perpendicular second)
    (secondFirstNotPerpendicular : ¬ second.Perpendicular first) :
    Twist.twist first second firstSecondNotPerpendicular =
      Twist.twist second first secondFirstNotPerpendicular := by
  unfold Twist.twist
  congr 1 <;> ring1
end Purelib.Geometry.Plane.Line.Turn.Basic

end

end
