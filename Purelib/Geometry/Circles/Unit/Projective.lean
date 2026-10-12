module
import Purelib.Algebra.Field.Cancellation
import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.Field.Squares
import Purelib.Geometry.Circles.Projective.Basic
public import Purelib.Geometry.Circles.Projective.Parametrization
public import Purelib.Geometry.Circles.Unit.Basic
import Purelib.Geometry.Plane.Point.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Logic.Nontrivial.Defs
import Purelib.Curves.Plane.Conic.Basic
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

open Purelib.Algebra.Field (ExplicitField)

open Purelib

open Purelib.Curves.Plane (Conic)

open Purelib.Geometry

@[expose] public section

namespace Purelib.Curves.Plane.Conic

variable {K : Type*} [ExplicitField K]

section

/-- The source's finite transform from the projective circle to the unit circle. -/
def projectiveToUnit (point : Plane.Point K) :
  Plane.Point K :=
  ⟨2 * point.y - 1, 2 * point.x⟩

/-- Its explicit inverse when `2 ≠ 0`. -/
def unitToProjective (point : Plane.Point K) :
  Plane.Point K :=
  ⟨point.y / 2, (point.x + 1) / 2⟩

/-- The transformed unit equation is four times the projective equation. -/
theorem projectiveToUnit_equation [Nontrivial K] (point :
  Plane.Point K) :
    (projectiveToUnit point).x ^ 2 +
        (projectiveToUnit point).y ^ 2 - 1 =
      4 * (point.x ^ 2 + point.y ^ 2 - point.y) := by
  unfold projectiveToUnit
  ring1

/-- The finite transform sends every projective-circle point to the unit circle. -/
theorem projectiveToUnit_contains [Nontrivial K]
    (point : Plane.Point K) (pointOnCircle : Conic.projectiveCircle.Contains point) :
    Conic.unitCircle.Contains (projectiveToUnit point) := by
  apply (Conic.unitCircle_contains_iff _).2
  calc
    (projectiveToUnit point).x ^ 2 +
        (projectiveToUnit point).y ^ 2 - 1 =
        4 * (point.x ^ 2 + point.y ^ 2 - point.y) :=
      projectiveToUnit_equation point
    _ = 0 := by
      rw [(Conic.projectiveCircle_contains_iff point).1 pointOnCircle]
      ring1

/-- Applying the inverse transform and then the forward transform recovers the requested point. -/
theorem projectiveToUnit_unitToProjective
    (point : Plane.Point K) (twoNonzero : (2 : K) ≠ 0) :
    projectiveToUnit (unitToProjective point) = point :=
      by
  have xCancel : ((point.x + 1) / 2) * 2 = point.x + 1 :=
    ExplicitField.div_mul_cancel (point.x + 1) twoNonzero
  have yCancel : (point.y / 2) * 2 = point.y :=
    ExplicitField.div_mul_cancel point.y twoNonzero
  apply Plane.Point.ext
  · change 2 * ((point.x + 1) / 2) - 1 = point.x
    calc
      2 * ((point.x + 1) / 2) - 1 =
          ((point.x + 1) / 2) * 2 - 1 := by ring1
      _ = point.x := by rw [xCancel]; ring1
  · change 2 * (point.y / 2) = point.y
    calc
      2 * (point.y / 2) = (point.y / 2) * 2 := by ring1
      _ = point.y := yCancel

/-- A unit-circle point maps back to the projective circle outside characteristic two. -/
theorem unitToProjective_contains [Nontrivial K]
    (point : Plane.Point K) (twoNonzero : (2 : K) ≠ 0)
    (pointOnCircle : Conic.unitCircle.Contains point) :
    Conic.projectiveCircle.Contains (unitToProjective point) := by
  have fourNonzero : (4 : K) ≠ 0 := by
    have productNonzero := ExplicitField.mul_ne_zero twoNonzero twoNonzero
    intro fourZero
    apply productNonzero
    calc
      (2 : K) * 2 = 4 := by ring1
      _ = 0 := fourZero
  let projectivePoint := unitToProjective point
  have recovered : projectiveToUnit projectivePoint = point :=
    projectiveToUnit_unitToProjective point twoNonzero
  have transformedEquation :
      (projectiveToUnit projectivePoint).x ^ 2 +
          (projectiveToUnit projectivePoint).y ^ 2 - 1 = 0 := by
    rw [recovered]
    exact (Conic.unitCircle_contains_iff point).1 pointOnCircle
  apply (Conic.projectiveCircle_contains_iff projectivePoint).2
  apply ExplicitField.eq_zero_of_mul_eq_zero_left fourNonzero
  calc
    4 * (projectivePoint.x ^ 2 + projectivePoint.y ^ 2 -
        projectivePoint.y) =
        (projectiveToUnit projectivePoint).x ^ 2 +
          (projectiveToUnit projectivePoint).y ^ 2 - 1 :=
      (projectiveToUnit_equation projectivePoint).symm
    _ = 0 := transformedEquation

/-- The projective parametrization transforms into the printed unit-circle parametrization. -/
theorem projectiveToUnit_projectiveCirclePoint
    (parameter : K) (squareNotNegativeOne : parameter ^ 2 ≠ -1) :
    projectiveToUnit (Conic.projectiveCirclePoint parameter) =
      Conic.unitCirclePoint parameter := by
  let denominator := 1 + parameter ^ 2
  have denominatorNonzero : denominator ≠ 0 :=
    (Conic.projectiveParameter_denominator_ne_zero_iff parameter).2
      squareNotNegativeOne
  have oneCancel : (1 / denominator) * denominator = (1 : K) :=
    ExplicitField.div_mul_cancel 1 denominatorNonzero
  apply Plane.Point.ext
  · change 2 * (1 / denominator) - 1 =
      (1 - parameter ^ 2) / denominator
    apply ExplicitField.eq_of_mul_eq_mul_right denominatorNonzero
    calc
      (2 * (1 / denominator) - 1) * denominator =
          2 * ((1 / denominator) * denominator) - denominator := by ring1
      _ = 2 - denominator := by rw [oneCancel]; ring1
      _ = 1 - parameter ^ 2 := by unfold denominator; ring1
      _ = ((1 - parameter ^ 2) / denominator) * denominator :=
        (ExplicitField.div_mul_cancel
          (1 - parameter ^ 2) denominatorNonzero).symm
  · change 2 * (parameter / denominator) =
      (2 * parameter) / denominator
    simp only [ExplicitField.div_eq_mul_inv]
    ring1
end

end Purelib.Curves.Plane.Conic

end
