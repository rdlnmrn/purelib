module

import Purelib.Algebra.Field.Cancellation
import Purelib.Algebra.Field.ExplicitField
import Purelib.Curves.Plane.Conic.Basic
public import Purelib.Curves.Plane.Conic.Center
import Purelib.Geometry.Plane.Line.Basic
import Purelib.Geometry.Plane.Point.Basic
import Purelib.Geometry.Plane.HalfTurn.Basic
public import Purelib.Geometry.Plane.Reflection.Point
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

open Purelib.Algebra.Field (ExplicitField)

open Purelib

open Purelib.Curves.Plane

open Purelib.Geometry

open Purelib.Geometry.Plane

open Purelib.Geometry.Plane.Reflection.Point

section
@[expose] public section

/-!
# Divine Proportions, conic axes

An axis is retained as an explicit non-null mirror together with the finite
equation-preservation identity from Exercise 15.8.  The elementary reflection
lemmas below construct the two mirrors used for quadrolas without selecting
any roots or completed geometric object.
-/

namespace Purelib.Curves.Plane.Conic

variable {K : Type*} [ExplicitField K]

section

/-- Reflection in a non-null line preserves the conic polynomial pointwise.

The predicate retains the mirror non-nullness certificate and equality of evaluations at every point; it specifies the
equation itself, including its scale. -/
def IsAxis (conic : Conic K) (axis : Plane.Line K) : Prop
  :=
  ∃ nonNull : ¬ axis.IsNull,
    ∀ point : Plane.Point K,
      conic.evaluate (Reflection.Point.reflectPoint axis nonNull point) = conic.evaluate point

end
end Purelib.Curves.Plane.Conic

end

section
@[expose] public section

/-!
# Divine Proportions, Exercise 15.18

The two axes of a grammola are constructed from an explicit square witness
for the product of its diagonal norms.  Reflection in either normalized
vertex bisector swaps the two weighted squared line values, so it preserves
the grammola equation.  Conversely, two finite reflection probes show that
every axis satisfies the equal-spread bisector equation.
-/

namespace Purelib.Geometry.Conics.Axis

variable {K : Type*} [ExplicitField K]

/-- An equation-preserving reflection sends a conic center to a center.

With two nonzero, conjugating the center half-turn by the non-null reflection preserves the defining center equations.
-/
public theorem reflected_center_isCenter
  (displayedConic : Conic K)
    (axis : Plane.Line K) (axisNonNull : ¬ axis.IsNull)
    (equationInvariant : ∀ point : Plane.Point K,
      displayedConic.evaluate (Reflection.Point.reflectPoint axis axisNonNull point) =
        displayedConic.evaluate point)
    (center : Plane.Point K) (isCenter : displayedConic.IsCenter center)
    (twoNonzero : (2 : K) ≠ 0) :
    displayedConic.IsCenter (Reflection.Point.reflectPoint axis axisNonNull center) := by
  have centerInvariant :=
    (Conic.isCenter_iff_rotationInvariant displayedConic center twoNonzero).1
      isCenter
  apply (Conic.isCenter_iff_rotationInvariant displayedConic
    (Reflection.Point.reflectPoint axis axisNonNull center) twoNonzero).2
  intro point
  have commute :
      Reflection.Point.reflectPoint axis axisNonNull
          (HalfTurn.Basic.rotateInPoint center (Reflection.Point.reflectPoint axis axisNonNull point)) =
        HalfTurn.Basic.rotateInPoint (Reflection.Point.reflectPoint axis axisNonNull center) point := by
    calc
      Reflection.Point.reflectPoint axis axisNonNull
          (HalfTurn.Basic.rotateInPoint center (Reflection.Point.reflectPoint axis axisNonNull point)) =
        HalfTurn.Basic.rotateInPoint (Reflection.Point.reflectPoint axis axisNonNull center)
          (Reflection.Point.reflectPoint axis axisNonNull
            (Reflection.Point.reflectPoint axis axisNonNull point)) :=
              Purelib.Geometry.Plane.Reflection.Point.reflectPoint_rotateInPoint axis axisNonNull center
                (Reflection.Point.reflectPoint axis axisNonNull point)
      _ = HalfTurn.Basic.rotateInPoint (Reflection.Point.reflectPoint axis axisNonNull center) point := by
        rw [Reflection.Point.reflectPoint_involutive]
  calc
    displayedConic.evaluate
        (HalfTurn.Basic.rotateInPoint (Reflection.Point.reflectPoint axis axisNonNull center) point) =
      displayedConic.evaluate
        (Reflection.Point.reflectPoint axis axisNonNull
          (HalfTurn.Basic.rotateInPoint center (Reflection.Point.reflectPoint axis axisNonNull point))) := by
            rw [commute]
    _ = displayedConic.evaluate
        (HalfTurn.Basic.rotateInPoint center (Reflection.Point.reflectPoint axis axisNonNull point)) :=
          equationInvariant _
    _ = displayedConic.evaluate (Reflection.Point.reflectPoint axis axisNonNull point) :=
      centerInvariant _
    _ = displayedConic.evaluate point := equationInvariant _

/-- The point obtained by adding the axis tangent and normal vectors to a center. -/
private def positiveAxisProbe (center :
  Plane.Point K) (axis : Plane.Line K) : Plane.Point K :=
  ⟨center.x + axis.b + axis.a, center.y - axis.a + axis.b⟩

/-- The point obtained by adding the axis tangent and subtracting its normal at a center. -/
private def negativeAxisProbe (center :
  Plane.Point K) (axis : Plane.Line K) : Plane.Point K :=
  ⟨center.x + axis.b - axis.a, center.y - axis.a - axis.b⟩

/-- Reflection swaps the positive and negative probes based at a point on the mirror.

The mirror is non-null; the two probes differ only in the sign of its normal displacement. -/
private theorem reflectPoint_positiveAxisProbe (axis :
  Plane.Line K)
    (axisNonNull : ¬ axis.IsNull) (center : Plane.Point K)
    (centerOnAxis : axis.Contains center) :
    Reflection.Point.reflectPoint axis axisNonNull (positiveAxisProbe
      center axis) =
      negativeAxisProbe center axis := by
  have normCancel : Line.Basic.lineNorm axis * (Line.Basic.lineNorm axis)⁻¹ = (1 : K) :=
    ExplicitField.mul_inv_cancel _ axisNonNull
  rw [Reflection.Point.reflectPoint_formula]
  apply Plane.Point.ext
  · change
      (((axis.b ^ 2 - axis.a ^ 2) *
              (center.x + axis.b + axis.a) -
            2 * axis.a * axis.b * (center.y - axis.a + axis.b) -
            2 * axis.a * axis.c) /
          Line.Basic.lineNorm axis) = center.x + axis.b - axis.a
    simp only [ExplicitField.div_eq_mul_inv]
    calc
      ((axis.b ^ 2 - axis.a ^ 2) *
              (center.x + axis.b + axis.a) -
            2 * axis.a * axis.b * (center.y - axis.a + axis.b) -
            2 * axis.a * axis.c) * (Line.Basic.lineNorm axis)⁻¹ =
        (Line.Basic.lineNorm axis * (center.x + axis.b - axis.a) -
            2 * axis.a *
              (axis.a * center.x + axis.b * center.y + axis.c)) *
          (Line.Basic.lineNorm axis)⁻¹ := by unfold Line.Basic.lineNorm; ring1
      _ = (Line.Basic.lineNorm axis * (center.x + axis.b - axis.a)) *
          (Line.Basic.lineNorm axis)⁻¹ := by
            unfold Plane.Line.Contains at centerOnAxis
            rw [centerOnAxis]
            ring1
      _ = (center.x + axis.b - axis.a) *
          (Line.Basic.lineNorm axis * (Line.Basic.lineNorm axis)⁻¹) := by ring1
      _ = center.x + axis.b - axis.a := by rw [normCancel]; ring1
  · change
      ((-2 * axis.a * axis.b * (center.x + axis.b + axis.a) +
            (axis.a ^ 2 - axis.b ^ 2) *
              (center.y - axis.a + axis.b) -
            2 * axis.b * axis.c) /
          Line.Basic.lineNorm axis) = center.y - axis.a - axis.b
    simp only [ExplicitField.div_eq_mul_inv]
    calc
      (-2 * axis.a * axis.b * (center.x + axis.b + axis.a) +
              (axis.a ^ 2 - axis.b ^ 2) *
                (center.y - axis.a + axis.b) -
              2 * axis.b * axis.c) * (Line.Basic.lineNorm axis)⁻¹ =
        (Line.Basic.lineNorm axis * (center.y - axis.a - axis.b) -
            2 * axis.b *
              (axis.a * center.x + axis.b * center.y + axis.c)) *
          (Line.Basic.lineNorm axis)⁻¹ := by unfold Line.Basic.lineNorm; ring1
      _ = (Line.Basic.lineNorm axis * (center.y - axis.a - axis.b)) *
          (Line.Basic.lineNorm axis)⁻¹ := by
            unfold Plane.Line.Contains at centerOnAxis
            rw [centerOnAxis]
            ring1
      _ = (center.y - axis.a - axis.b) *
          (Line.Basic.lineNorm axis * (Line.Basic.lineNorm axis)⁻¹) := by ring1
      _ = center.y - axis.a - axis.b := by rw [normCancel]; ring1

/-- The mixed quadratic coefficient measured along a mirror direction and its normal.

The expression uses only the conic quadratic coefficients and the mirror normal; its vanishing is necessary for an axis
through a center. -/
public def axisCrossForm (displayedConic :
  Conic K) (axis : Plane.Line K) : K :=
  2 * (displayedConic.d - displayedConic.f) * axis.a * axis.b +
    displayedConic.e * (axis.b ^ 2 - axis.a ^ 2)

/-- An equation-preserving mirror through a center has zero quadratic cross form.

Comparing the two reflected probes gives the claim when the mirror and two are nonzero. -/
public theorem axisCrossForm_eq_zero_of_axis
    (displayedConic : Conic K) (axis : Plane.Line K)
    (axisNonNull : ¬ axis.IsNull)
    (equationInvariant : ∀ point : Plane.Point K,
      displayedConic.evaluate (Reflection.Point.reflectPoint axis axisNonNull point) =
        displayedConic.evaluate point)
    (center : Plane.Point K) (isCenter : displayedConic.IsCenter center)
    (centerOnAxis : axis.Contains center)
    (twoNonzero : (2 : K) ≠ 0) :
    axisCrossForm displayedConic axis = 0 := by
  have reflectedProbe := reflectPoint_positiveAxisProbe axis
    axisNonNull center
    centerOnAxis
  have evaluationsEqual :
      displayedConic.evaluate (negativeAxisProbe center axis) =
        displayedConic.evaluate (positiveAxisProbe center axis) := by
    rw [← reflectedProbe]
    exact equationInvariant _
  have twiceFormZero : 2 * axisCrossForm displayedConic axis = 0 := by
    calc
      2 * axisCrossForm displayedConic axis =
        displayedConic.evaluate (positiveAxisProbe center axis) -
          displayedConic.evaluate (negativeAxisProbe center axis) -
          2 * (axis.a *
              (2 * displayedConic.d * center.x +
                displayedConic.e * center.y + displayedConic.a) +
            axis.b *
              (displayedConic.e * center.x +
                2 * displayedConic.f * center.y + displayedConic.b)) := by
                  unfold axisCrossForm Conic.evaluate
                    positiveAxisProbe
                    negativeAxisProbe
                  ring1
      _ = 0 := by rw [isCenter.1, isCenter.2, evaluationsEqual]; ring1
  exact ExplicitField.eq_zero_of_mul_eq_zero_left twoNonzero twiceFormZero

/-- Exactly two axes means two inequivalent displayed mirrors which exhaust all equation-preserving mirrors up to line
equivalence. -/
def HasExactlyTwoAxes (displayedConic : Conic K) : Prop :=
  ∃ firstAxis secondAxis : Plane.Line K,
    displayedConic.IsAxis firstAxis ∧
      displayedConic.IsAxis secondAxis ∧
      ¬ firstAxis.Equivalent secondAxis ∧
      ∀ axis : Plane.Line K, displayedConic.IsAxis axis →
        axis.Equivalent firstAxis ∨ axis.Equivalent secondAxis

end Purelib.Geometry.Conics.Axis

end
