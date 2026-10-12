module
import Purelib.Algebra.Field.ExplicitField
import Purelib.Geometry.Plane.Line.Basic
import Purelib.Geometry.Plane.Line.Turn.Basic
import Purelib.Geometry.Plane.Line.Turn.Triple
public import Purelib.Geometry.Plane.Line.Twist
import Purelib.Geometry.Trigonometry.Twist.Triple
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init

open Purelib.Geometry

open Purelib.Geometry.Plane

open Purelib.Geometry.Plane.Line

open Purelib.Geometry.Plane.Line.Basic

open Purelib.Geometry.Plane.Line.Turn

section
@[expose] public section

/-!
# Divine Proportions, §§7.3 and 9.2: turns and the triple twist formula

The oriented turn is retained as the explicit determinant/dot quotient.  Its
cyclic three-line identity is linear; squaring that finite identity gives the
book's Triple twist formula without separating null and non-null cases.
-/

namespace Purelib.Geometry.Plane.Line.Twist.Triple

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- Theorem 50 (Triple twist formula), valid uniformly for null and non-null lines whenever the three displayed turns
are defined. -/
theorem triple_twist_formula
    (first second third : Plane.Line K)
    (firstSecondNotPerpendicular : ¬ first.Perpendicular second)
    (firstThirdNotPerpendicular : ¬ first.Perpendicular third)
    (secondThirdNotPerpendicular : ¬ second.Perpendicular third) :
    let t₁ := Twist.twist second third secondThirdNotPerpendicular
    let t₂ := Twist.twist first third firstThirdNotPerpendicular
    let t₃ := Twist.twist first second firstSecondNotPerpendicular
    (t₁ + t₂ + t₃ - t₁ * t₂ * t₃) ^ 2 =
      4 * (t₁ * t₂ + t₁ * t₃ + t₂ * t₃ + 2 * t₁ * t₂ * t₃) := by
  dsimp only
  have thirdFirstNotPerpendicular : ¬ third.Perpendicular first := by
    intro perpendicular
    exact firstThirdNotPerpendicular (Plane.Line.perpendicular_symm perpendicular)
  let r₁ := Turn.Basic.turn second third secondThirdNotPerpendicular
  let r₂ := Turn.Basic.turn third first thirdFirstNotPerpendicular
  let r₃ := Turn.Basic.turn first second firstSecondNotPerpendicular
  have turnEquation : r₁ + r₂ + r₃ = r₁ * r₂ * r₃ :=
    Triple.triple_turn_formula first second third firstSecondNotPerpendicular
      secondThirdNotPerpendicular thirdFirstNotPerpendicular
  have twistOne :
      Twist.twist second third secondThirdNotPerpendicular = r₁ ^ 2 :=
    Turn.Basic.twist_eq_turn_square second third secondThirdNotPerpendicular
  have twistTwo :
      Twist.twist first third firstThirdNotPerpendicular = r₂ ^ 2 := by
    calc
      Twist.twist first third firstThirdNotPerpendicular =
          Twist.twist third first thirdFirstNotPerpendicular :=
        Turn.Basic.twist_symm first third firstThirdNotPerpendicular
          thirdFirstNotPerpendicular
      _ = r₂ ^ 2 := Turn.Basic.twist_eq_turn_square third first
        thirdFirstNotPerpendicular
  have twistThree :
      Twist.twist first second firstSecondNotPerpendicular = r₃ ^ 2 :=
    Turn.Basic.twist_eq_turn_square first second firstSecondNotPerpendicular
  rw [twistOne, twistTwo, twistThree]
  exact Trigonometry.Twist.Triple.exercise_7_12 r₁ r₂ r₃ turnEquation
end Purelib.Geometry.Plane.Line.Twist.Triple

end
