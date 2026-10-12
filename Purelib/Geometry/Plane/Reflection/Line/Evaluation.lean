module

public import Purelib.Geometry.Plane.Line.VertexBisector.Construction
import Purelib.Algebra.Field.ExplicitField
import Purelib.Geometry.Plane.Line.Basic
import Purelib.Geometry.Plane.Point.Basic
public import Purelib.Geometry.Plane.Reflection.Line
import Purelib.Geometry.Plane.Reflection.Point
import Mathlib.Algebra.Group.Basic
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

open Purelib.Geometry.Plane.Reflection

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

namespace Purelib.Geometry.Plane.Reflection.Line.Evaluation.Grammola

section

variable {K : Type*} [ExplicitField K]

/-- Reflection changes a displayed line value by the usual finite projection formula. This denominator-cleared identity
is reused for both axes. -/
theorem lineValue_reflectPoint (mirror target :
  Plane.Line K)
    (mirrorNonNull : ¬ mirror.IsNull) (point : Plane.Point K) :
    Line.Basic.lineValue target (Reflection.Point.reflectPoint mirror mirrorNonNull point) =
      (Line.Basic.lineNorm mirror * Line.Basic.lineValue target point -
          2 * (target.a * mirror.a + target.b * mirror.b) *
            Line.Basic.lineValue mirror point) /
        Line.Basic.lineNorm mirror := by
  have normCancel : Line.Basic.lineNorm mirror * (Line.Basic.lineNorm mirror)⁻¹ = (1 : K) :=
    ExplicitField.mul_inv_cancel _ mirrorNonNull
  rw [Reflection.Point.reflectPoint_formula]
  change
    target.a *
          (((mirror.b ^ 2 - mirror.a ^ 2) * point.x -
              2 * mirror.a * mirror.b * point.y -
              2 * mirror.a * mirror.c) /
            Line.Basic.lineNorm mirror) +
        target.b *
          ((-2 * mirror.a * mirror.b * point.x +
              (mirror.a ^ 2 - mirror.b ^ 2) * point.y -
              2 * mirror.b * mirror.c) /
            Line.Basic.lineNorm mirror) + target.c =
      (Line.Basic.lineNorm mirror *
            (target.a * point.x + target.b * point.y + target.c) -
          2 * (target.a * mirror.a + target.b * mirror.b) *
            (mirror.a * point.x + mirror.b * point.y + mirror.c)) /
        Line.Basic.lineNorm mirror
  simp only [ExplicitField.div_eq_mul_inv]
  calc
    target.a *
          (((mirror.b ^ 2 - mirror.a ^ 2) * point.x -
              2 * mirror.a * mirror.b * point.y -
              2 * mirror.a * mirror.c) * (Line.Basic.lineNorm mirror)⁻¹) +
        target.b *
          ((-2 * mirror.a * mirror.b * point.x +
              (mirror.a ^ 2 - mirror.b ^ 2) * point.y -
              2 * mirror.b * mirror.c) * (Line.Basic.lineNorm mirror)⁻¹) +
        target.c =
      (Line.Basic.lineNorm mirror * Line.Basic.lineValue target point -
          2 * (target.a * mirror.a + target.b * mirror.b) *
            Line.Basic.lineValue mirror point) * (Line.Basic.lineNorm mirror)⁻¹ +
        target.c *
          (1 - Line.Basic.lineNorm mirror * (Line.Basic.lineNorm mirror)⁻¹) := by
            unfold Line.Basic.lineValue Line.Basic.lineNorm
            ring1
    _ = (Line.Basic.lineNorm mirror * Line.Basic.lineValue target point -
          2 * (target.a * mirror.a + target.b * mirror.b) *
            Line.Basic.lineValue mirror point) * (Line.Basic.lineNorm mirror)⁻¹ := by
      rw [normCancel]
      ring1
end

end Purelib.Geometry.Plane.Reflection.Line.Evaluation.Grammola

end

section
@[expose] public section

/-!
# Divine Proportions, Exercises 15.8 and 15.9

This module constructs a parabola's axis from its focus and directrix, proves
that equation preservation characterizes that axis up to the project's
quotient-free line equivalence, and constructs the unique vertex as the
midpoint of the focus and its altitude foot on the directrix.
-/

namespace Purelib.Curves.Plane.Conic

variable {K : Type*} [ExplicitField K]

section

/-- The reflected-line polynomial at a reflected point is the original line polynomial multiplied by the negative mirror
norm. -/
theorem reflectLine_lineValue_reflectPoint [DecidableEq K]
    (mirror target : Plane.Line K) (mirrorNonNull : ¬ mirror.IsNull)
    (point : Plane.Point K) :
    Conic.lineValue (Line.reflectLine mirror target mirrorNonNull)
        (Reflection.Point.reflectPoint mirror mirrorNonNull point) =
      -Line.Basic.lineNorm mirror * Conic.lineValue target point := by
  have normCancel : Line.Basic.lineNorm mirror * (Line.Basic.lineNorm mirror)⁻¹ = (1 : K) :=
    ExplicitField.mul_inv_cancel _ mirrorNonNull
  rw [Reflection.Point.reflectPoint_formula]
  unfold Conic.lineValue Line.reflectLine
  change
    Line.reflectedLineA mirror target *
          (((mirror.b ^ 2 - mirror.a ^ 2) * point.x -
            2 * mirror.a * mirror.b * point.y -
            2 * mirror.a * mirror.c) / Line.Basic.lineNorm mirror) +
        Line.reflectedLineB mirror target *
          ((-2 * mirror.a * mirror.b * point.x +
            (mirror.a ^ 2 - mirror.b ^ 2) * point.y -
            2 * mirror.b * mirror.c) / Line.Basic.lineNorm mirror) +
        Line.reflectedLineC mirror target =
      -Line.Basic.lineNorm mirror *
        (target.a * point.x + target.b * point.y + target.c)
  simp only [ExplicitField.div_eq_mul_inv]
  calc
    Line.reflectedLineA mirror target *
          (((mirror.b ^ 2 - mirror.a ^ 2) * point.x -
            2 * mirror.a * mirror.b * point.y -
            2 * mirror.a * mirror.c) * (Line.Basic.lineNorm mirror)⁻¹) +
        Line.reflectedLineB mirror target *
          ((-2 * mirror.a * mirror.b * point.x +
            (mirror.a ^ 2 - mirror.b ^ 2) * point.y -
            2 * mirror.b * mirror.c) * (Line.Basic.lineNorm mirror)⁻¹) +
        Line.reflectedLineC mirror target =
      -Line.Basic.lineNorm mirror * (target.a * point.x + target.b * point.y) *
          (Line.Basic.lineNorm mirror * (Line.Basic.lineNorm mirror)⁻¹) +
        2 * mirror.c *
          (mirror.a * target.a + mirror.b * target.b) *
          (1 - Line.Basic.lineNorm mirror * (Line.Basic.lineNorm mirror)⁻¹) -
        Line.Basic.lineNorm mirror * target.c := by
          unfold Line.reflectedLineA Line.reflectedLineB Line.reflectedLineC Line.Basic.lineNorm
          ring1
    _ = -Line.Basic.lineNorm mirror *
        (target.a * point.x + target.b * point.y + target.c) := by
      rw [normCancel]
      ring1

/-- Reflecting in a line perpendicular to a target preserves the target's affine line polynomial exactly. -/
theorem lineValue_reflectPoint_of_perpendicular
    (mirror target : Plane.Line K) (mirrorNonNull : ¬ mirror.IsNull)
    (perpendicular : mirror.Perpendicular target) (point : Plane.Point K) :
    Conic.lineValue target (Reflection.Point.reflectPoint mirror mirrorNonNull point) =
      Conic.lineValue target point := by
  have normCancel : Line.Basic.lineNorm mirror * (Line.Basic.lineNorm mirror)⁻¹ = (1 : K) :=
    ExplicitField.mul_inv_cancel _ mirrorNonNull
  rw [Reflection.Point.reflectPoint_formula]
  unfold Conic.lineValue Point.reflectionFormula
  simp only [ExplicitField.div_eq_mul_inv]
  calc
    target.a *
          (((mirror.b ^ 2 - mirror.a ^ 2) * point.x -
            2 * mirror.a * mirror.b * point.y -
            2 * mirror.a * mirror.c) * (Line.Basic.lineNorm mirror)⁻¹) +
        target.b *
          ((-2 * mirror.a * mirror.b * point.x +
            (mirror.a ^ 2 - mirror.b ^ 2) * point.y -
            2 * mirror.b * mirror.c) * (Line.Basic.lineNorm mirror)⁻¹) +
        target.c =
      (target.a * point.x + target.b * point.y + target.c) *
          (Line.Basic.lineNorm mirror * (Line.Basic.lineNorm mirror)⁻¹) -
        2 * (mirror.a * target.a + mirror.b * target.b) *
          (mirror.a * point.x + mirror.b * point.y + mirror.c) *
          (Line.Basic.lineNorm mirror)⁻¹ +
        target.c * (1 - Line.Basic.lineNorm mirror * (Line.Basic.lineNorm mirror)⁻¹) := by
          unfold Line.Basic.lineNorm
          ring1
    _ = target.a * point.x + target.b * point.y + target.c := by
      unfold Plane.Line.Perpendicular at perpendicular
      rw [normCancel, perpendicular]
      ring1
end

end Purelib.Curves.Plane.Conic

end

section
variable {K : Type*} [ExplicitField K]
namespace Purelib.Geometry.Plane.Line.VertexBisector.Construction
/-- Reflection in the positive bisector exchanges the first line value with a scaled negative second value.

The root certifies the product of the two non-null diagonal norms; nonparallel diagonals and nonzero two make the
bisector reflection defined. -/
public theorem
  positive_reflection_swaps_first
  [DecidableEq K]
    (firstDiagonal secondDiagonal : Line K) (root : K)
    (firstNonNull : ¬ firstDiagonal.IsNull)
    (secondNonNull : ¬ secondDiagonal.IsNull)
    (notParallel : ¬ firstDiagonal.Parallel secondDiagonal)
    (twoNonzero : (2 : K) ≠ 0)
    (rootEquation :
      root ^ 2 = Purelib.Geometry.Plane.Line.Basic.lineNorm firstDiagonal * Purelib.Geometry.Plane.Line.Basic.lineNorm
        secondDiagonal)
    (point : Point K) :
    let axis := Purelib.Geometry.Plane.Line.VertexBisector.Construction.positiveVertexBisector firstDiagonal
      secondDiagonal root
      firstNonNull notParallel
    let axisNonNull := Purelib.Geometry.Plane.Line.VertexBisector.Construction.positiveVertexBisector_nonNull
      firstDiagonal
      secondDiagonal root firstNonNull secondNonNull notParallel twoNonzero
      rootEquation
    root * Purelib.Geometry.Plane.Line.Basic.lineValue firstDiagonal
      (Purelib.Geometry.Plane.Reflection.Point.reflectPoint axis axisNonNull point) =
      -Purelib.Geometry.Plane.Line.Basic.lineNorm firstDiagonal * Purelib.Geometry.Plane.Line.Basic.lineValue
        secondDiagonal point := by
  dsimp only
  let axis := Purelib.Geometry.Plane.Line.VertexBisector.Construction.positiveVertexBisector firstDiagonal
    secondDiagonal root
    firstNonNull notParallel
  have axisNonNull := Purelib.Geometry.Plane.Line.VertexBisector.Construction.positiveVertexBisector_nonNull
    firstDiagonal
    secondDiagonal root firstNonNull secondNonNull notParallel twoNonzero
    rootEquation
  have axisNorm := Purelib.Geometry.Plane.Line.VertexBisector.Construction.positiveVertexBisector_norm firstDiagonal
    secondDiagonal
    root firstNonNull notParallel rootEquation
  have normCancel : Purelib.Geometry.Plane.Line.Basic.lineNorm axis * (Purelib.Geometry.Plane.Line.Basic.lineNorm
    axis)⁻¹ = (1 : K) :=
    ExplicitField.mul_inv_cancel _ axisNonNull
  have firstDotAxis :
      firstDiagonal.a * axis.a + firstDiagonal.b * axis.b =
        Purelib.Geometry.Plane.Line.Basic.lineNorm firstDiagonal *
          (root + (firstDiagonal.a * secondDiagonal.a +
            firstDiagonal.b * secondDiagonal.b)) := by
    change
      firstDiagonal.a *
            (root * firstDiagonal.a +
              Purelib.Geometry.Plane.Line.Basic.lineNorm firstDiagonal * secondDiagonal.a) +
          firstDiagonal.b *
            (root * firstDiagonal.b +
              Purelib.Geometry.Plane.Line.Basic.lineNorm firstDiagonal * secondDiagonal.b) = _
    unfold Purelib.Geometry.Plane.Line.Basic.lineNorm
    ring1
  have axisValue : Purelib.Geometry.Plane.Line.Basic.lineValue axis point =
      root * Purelib.Geometry.Plane.Line.Basic.lineValue firstDiagonal point +
        Purelib.Geometry.Plane.Line.Basic.lineNorm firstDiagonal * Purelib.Geometry.Plane.Line.Basic.lineValue
          secondDiagonal point := by
    change
      (root * firstDiagonal.a +
            Purelib.Geometry.Plane.Line.Basic.lineNorm firstDiagonal * secondDiagonal.a) * point.x +
          (root * firstDiagonal.b +
            Purelib.Geometry.Plane.Line.Basic.lineNorm firstDiagonal * secondDiagonal.b) * point.y +
          (root * firstDiagonal.c +
            Purelib.Geometry.Plane.Line.Basic.lineNorm firstDiagonal * secondDiagonal.c) = _
    unfold Purelib.Geometry.Plane.Line.Basic.lineValue
    ring1
  rw [Purelib.Geometry.Plane.Reflection.Line.Evaluation.Grammola.lineValue_reflectPoint axis firstDiagonal axisNonNull
    point]
  simp only [ExplicitField.div_eq_mul_inv]
  calc
    root *
        ((Purelib.Geometry.Plane.Line.Basic.lineNorm axis * Purelib.Geometry.Plane.Line.Basic.lineValue firstDiagonal
          point -
            2 *
                (firstDiagonal.a * axis.a + firstDiagonal.b * axis.b) *
              Purelib.Geometry.Plane.Line.Basic.lineValue axis point) *
          (Purelib.Geometry.Plane.Line.Basic.lineNorm axis)⁻¹) =
      root *
        ((Purelib.Geometry.Plane.Line.Basic.lineNorm axis * Purelib.Geometry.Plane.Line.Basic.lineValue firstDiagonal
          point -
            2 *
                (Purelib.Geometry.Plane.Line.Basic.lineNorm firstDiagonal *
                  (root + (firstDiagonal.a * secondDiagonal.a +
                    firstDiagonal.b * secondDiagonal.b))) *
              (root * Purelib.Geometry.Plane.Line.Basic.lineValue firstDiagonal point +
                Purelib.Geometry.Plane.Line.Basic.lineNorm firstDiagonal * Purelib.Geometry.Plane.Line.Basic.lineValue
                  secondDiagonal point)) *
          (Purelib.Geometry.Plane.Line.Basic.lineNorm axis)⁻¹) := by rw [firstDotAxis, axisValue]
    _ =
      (-Purelib.Geometry.Plane.Line.Basic.lineNorm firstDiagonal * Purelib.Geometry.Plane.Line.Basic.lineValue
        secondDiagonal point) *
        (Purelib.Geometry.Plane.Line.Basic.lineNorm axis * (Purelib.Geometry.Plane.Line.Basic.lineNorm axis)⁻¹) := by
          rw [axisNorm]
          ring1
    _ = -Purelib.Geometry.Plane.Line.Basic.lineNorm firstDiagonal * Purelib.Geometry.Plane.Line.Basic.lineValue
      secondDiagonal point := by
      rw [normCancel]
      ring1

/-- Reflection in the positive bisector exchanges the second line value with a scaled negative first value.

The identity retains the first diagonal norm and the supplied square root as its two scaling factors. -/
public theorem
  positive_reflection_swaps_second
  [DecidableEq K]
    (firstDiagonal secondDiagonal : Line K) (root : K)
    (firstNonNull : ¬ firstDiagonal.IsNull)
    (secondNonNull : ¬ secondDiagonal.IsNull)
    (notParallel : ¬ firstDiagonal.Parallel secondDiagonal)
    (twoNonzero : (2 : K) ≠ 0)
    (rootEquation :
      root ^ 2 = Purelib.Geometry.Plane.Line.Basic.lineNorm firstDiagonal * Purelib.Geometry.Plane.Line.Basic.lineNorm
        secondDiagonal)
    (point : Point K) :
    let axis := Purelib.Geometry.Plane.Line.VertexBisector.Construction.positiveVertexBisector firstDiagonal
      secondDiagonal root
      firstNonNull notParallel
    let axisNonNull := Purelib.Geometry.Plane.Line.VertexBisector.Construction.positiveVertexBisector_nonNull
      firstDiagonal
      secondDiagonal root firstNonNull secondNonNull notParallel twoNonzero
      rootEquation
    Purelib.Geometry.Plane.Line.Basic.lineNorm firstDiagonal *
        Purelib.Geometry.Plane.Line.Basic.lineValue secondDiagonal (Purelib.Geometry.Plane.Reflection.Point.reflectPoint
          axis axisNonNull point) =
      -root * Purelib.Geometry.Plane.Line.Basic.lineValue firstDiagonal point := by
  dsimp only
  let axis := Purelib.Geometry.Plane.Line.VertexBisector.Construction.positiveVertexBisector firstDiagonal
    secondDiagonal root
    firstNonNull notParallel
  have axisNonNull := Purelib.Geometry.Plane.Line.VertexBisector.Construction.positiveVertexBisector_nonNull
    firstDiagonal
    secondDiagonal root firstNonNull secondNonNull notParallel twoNonzero
    rootEquation
  have axisNorm := Purelib.Geometry.Plane.Line.VertexBisector.Construction.positiveVertexBisector_norm firstDiagonal
    secondDiagonal
    root firstNonNull notParallel rootEquation
  have normCancel : Purelib.Geometry.Plane.Line.Basic.lineNorm axis * (Purelib.Geometry.Plane.Line.Basic.lineNorm
    axis)⁻¹ = (1 : K) :=
    ExplicitField.mul_inv_cancel _ axisNonNull
  have secondDotAxis :
      secondDiagonal.a * axis.a + secondDiagonal.b * axis.b =
        root * (firstDiagonal.a * secondDiagonal.a +
            firstDiagonal.b * secondDiagonal.b) +
          Purelib.Geometry.Plane.Line.Basic.lineNorm firstDiagonal * Purelib.Geometry.Plane.Line.Basic.lineNorm
            secondDiagonal := by
    change
      secondDiagonal.a *
            (root * firstDiagonal.a +
              Purelib.Geometry.Plane.Line.Basic.lineNorm firstDiagonal * secondDiagonal.a) +
          secondDiagonal.b *
            (root * firstDiagonal.b +
              Purelib.Geometry.Plane.Line.Basic.lineNorm firstDiagonal * secondDiagonal.b) = _
    unfold Purelib.Geometry.Plane.Line.Basic.lineNorm
    ring1
  have axisValue : Purelib.Geometry.Plane.Line.Basic.lineValue axis point =
      root * Purelib.Geometry.Plane.Line.Basic.lineValue firstDiagonal point +
        Purelib.Geometry.Plane.Line.Basic.lineNorm firstDiagonal * Purelib.Geometry.Plane.Line.Basic.lineValue
          secondDiagonal point := by
    change
      (root * firstDiagonal.a +
            Purelib.Geometry.Plane.Line.Basic.lineNorm firstDiagonal * secondDiagonal.a) * point.x +
          (root * firstDiagonal.b +
            Purelib.Geometry.Plane.Line.Basic.lineNorm firstDiagonal * secondDiagonal.b) * point.y +
          (root * firstDiagonal.c +
            Purelib.Geometry.Plane.Line.Basic.lineNorm firstDiagonal * secondDiagonal.c) = _
    unfold Purelib.Geometry.Plane.Line.Basic.lineValue
    ring1
  rw [Purelib.Geometry.Plane.Reflection.Line.Evaluation.Grammola.lineValue_reflectPoint axis secondDiagonal axisNonNull
    point]
  simp only [ExplicitField.div_eq_mul_inv]
  calc
    Purelib.Geometry.Plane.Line.Basic.lineNorm firstDiagonal *
        ((Purelib.Geometry.Plane.Line.Basic.lineNorm axis * Purelib.Geometry.Plane.Line.Basic.lineValue secondDiagonal
          point -
            2 *
                (secondDiagonal.a * axis.a + secondDiagonal.b * axis.b) *
              Purelib.Geometry.Plane.Line.Basic.lineValue axis point) *
          (Purelib.Geometry.Plane.Line.Basic.lineNorm axis)⁻¹) =
      Purelib.Geometry.Plane.Line.Basic.lineNorm firstDiagonal *
        ((Purelib.Geometry.Plane.Line.Basic.lineNorm axis * Purelib.Geometry.Plane.Line.Basic.lineValue secondDiagonal
          point -
            2 *
                (root * (firstDiagonal.a * secondDiagonal.a +
                    firstDiagonal.b * secondDiagonal.b) +
                  Purelib.Geometry.Plane.Line.Basic.lineNorm firstDiagonal * Purelib.Geometry.Plane.Line.Basic.lineNorm
                    secondDiagonal) *
              (root * Purelib.Geometry.Plane.Line.Basic.lineValue firstDiagonal point +
                Purelib.Geometry.Plane.Line.Basic.lineNorm firstDiagonal * Purelib.Geometry.Plane.Line.Basic.lineValue
                  secondDiagonal point)) *
          (Purelib.Geometry.Plane.Line.Basic.lineNorm axis)⁻¹) := by rw [secondDotAxis, axisValue]
    _ =
      (-root * Purelib.Geometry.Plane.Line.Basic.lineValue firstDiagonal point) *
        (Purelib.Geometry.Plane.Line.Basic.lineNorm axis * (Purelib.Geometry.Plane.Line.Basic.lineNorm axis)⁻¹) := by
          rw [axisNorm]
          rw [← rootEquation]
          ring1
    _ = -root * Purelib.Geometry.Plane.Line.Basic.lineValue firstDiagonal point := by
      rw [normCancel]
      ring1

/-- Reflection in the negative bisector exchanges the first line value with a scaled second value.

The root certifies the product of the two non-null diagonal norms; nonparallel diagonals and nonzero two make the
bisector reflection defined. -/
public theorem
  negative_reflection_swaps_first
  [DecidableEq K]
    (firstDiagonal secondDiagonal : Line K) (root : K)
    (firstNonNull : ¬ firstDiagonal.IsNull)
    (secondNonNull : ¬ secondDiagonal.IsNull)
    (notParallel : ¬ firstDiagonal.Parallel secondDiagonal)
    (twoNonzero : (2 : K) ≠ 0)
    (rootEquation :
      root ^ 2 = Purelib.Geometry.Plane.Line.Basic.lineNorm firstDiagonal * Purelib.Geometry.Plane.Line.Basic.lineNorm
        secondDiagonal)
    (point : Point K) :
    let axis := Purelib.Geometry.Plane.Line.VertexBisector.Construction.negativeVertexBisector firstDiagonal
      secondDiagonal root
      firstNonNull notParallel
    let axisNonNull := Purelib.Geometry.Plane.Line.VertexBisector.Construction.negativeVertexBisector_nonNull
      firstDiagonal
      secondDiagonal root firstNonNull secondNonNull notParallel twoNonzero
      rootEquation
    root * Purelib.Geometry.Plane.Line.Basic.lineValue firstDiagonal
      (Purelib.Geometry.Plane.Reflection.Point.reflectPoint axis axisNonNull point) =
      Purelib.Geometry.Plane.Line.Basic.lineNorm firstDiagonal * Purelib.Geometry.Plane.Line.Basic.lineValue
        secondDiagonal point := by
  dsimp only
  let axis := Purelib.Geometry.Plane.Line.VertexBisector.Construction.negativeVertexBisector firstDiagonal
    secondDiagonal root
    firstNonNull notParallel
  have axisNonNull := Purelib.Geometry.Plane.Line.VertexBisector.Construction.negativeVertexBisector_nonNull
    firstDiagonal
    secondDiagonal root firstNonNull secondNonNull notParallel twoNonzero
    rootEquation
  have axisNorm := Purelib.Geometry.Plane.Line.VertexBisector.Construction.negativeVertexBisector_norm firstDiagonal
    secondDiagonal
    root firstNonNull notParallel rootEquation
  have normCancel : Purelib.Geometry.Plane.Line.Basic.lineNorm axis * (Purelib.Geometry.Plane.Line.Basic.lineNorm
    axis)⁻¹ = (1 : K) :=
    ExplicitField.mul_inv_cancel _ axisNonNull
  have firstDotAxis :
      firstDiagonal.a * axis.a + firstDiagonal.b * axis.b =
        Purelib.Geometry.Plane.Line.Basic.lineNorm firstDiagonal *
          (root - (firstDiagonal.a * secondDiagonal.a +
            firstDiagonal.b * secondDiagonal.b)) := by
    change
      firstDiagonal.a *
            (root * firstDiagonal.a -
              Purelib.Geometry.Plane.Line.Basic.lineNorm firstDiagonal * secondDiagonal.a) +
          firstDiagonal.b *
            (root * firstDiagonal.b -
              Purelib.Geometry.Plane.Line.Basic.lineNorm firstDiagonal * secondDiagonal.b) = _
    unfold Purelib.Geometry.Plane.Line.Basic.lineNorm
    ring1
  have axisValue : Purelib.Geometry.Plane.Line.Basic.lineValue axis point =
      root * Purelib.Geometry.Plane.Line.Basic.lineValue firstDiagonal point -
        Purelib.Geometry.Plane.Line.Basic.lineNorm firstDiagonal * Purelib.Geometry.Plane.Line.Basic.lineValue
          secondDiagonal point := by
    change
      (root * firstDiagonal.a -
            Purelib.Geometry.Plane.Line.Basic.lineNorm firstDiagonal * secondDiagonal.a) * point.x +
          (root * firstDiagonal.b -
            Purelib.Geometry.Plane.Line.Basic.lineNorm firstDiagonal * secondDiagonal.b) * point.y +
          (root * firstDiagonal.c -
            Purelib.Geometry.Plane.Line.Basic.lineNorm firstDiagonal * secondDiagonal.c) = _
    unfold Purelib.Geometry.Plane.Line.Basic.lineValue
    ring1
  rw [Purelib.Geometry.Plane.Reflection.Line.Evaluation.Grammola.lineValue_reflectPoint axis firstDiagonal axisNonNull
    point]
  simp only [ExplicitField.div_eq_mul_inv]
  calc
    root *
        ((Purelib.Geometry.Plane.Line.Basic.lineNorm axis * Purelib.Geometry.Plane.Line.Basic.lineValue firstDiagonal
          point -
            2 *
                (firstDiagonal.a * axis.a + firstDiagonal.b * axis.b) *
              Purelib.Geometry.Plane.Line.Basic.lineValue axis point) *
          (Purelib.Geometry.Plane.Line.Basic.lineNorm axis)⁻¹) =
      root *
        ((Purelib.Geometry.Plane.Line.Basic.lineNorm axis * Purelib.Geometry.Plane.Line.Basic.lineValue firstDiagonal
          point -
            2 *
                (Purelib.Geometry.Plane.Line.Basic.lineNorm firstDiagonal *
                  (root - (firstDiagonal.a * secondDiagonal.a +
                    firstDiagonal.b * secondDiagonal.b))) *
              (root * Purelib.Geometry.Plane.Line.Basic.lineValue firstDiagonal point -
                Purelib.Geometry.Plane.Line.Basic.lineNorm firstDiagonal * Purelib.Geometry.Plane.Line.Basic.lineValue
                  secondDiagonal point)) *
          (Purelib.Geometry.Plane.Line.Basic.lineNorm axis)⁻¹) := by rw [firstDotAxis, axisValue]
    _ =
      (Purelib.Geometry.Plane.Line.Basic.lineNorm firstDiagonal * Purelib.Geometry.Plane.Line.Basic.lineValue
        secondDiagonal point) *
        (Purelib.Geometry.Plane.Line.Basic.lineNorm axis * (Purelib.Geometry.Plane.Line.Basic.lineNorm axis)⁻¹) := by
          rw [axisNorm]
          ring1
    _ = Purelib.Geometry.Plane.Line.Basic.lineNorm firstDiagonal * Purelib.Geometry.Plane.Line.Basic.lineValue
      secondDiagonal point := by
      rw [normCancel]
      ring1

/-- Reflection in the negative bisector exchanges the second line value with a scaled first value.

The identity retains the first diagonal norm and the supplied square root as its two scaling factors. -/
public theorem
  negative_reflection_swaps_second
  [DecidableEq K]
    (firstDiagonal secondDiagonal : Line K) (root : K)
    (firstNonNull : ¬ firstDiagonal.IsNull)
    (secondNonNull : ¬ secondDiagonal.IsNull)
    (notParallel : ¬ firstDiagonal.Parallel secondDiagonal)
    (twoNonzero : (2 : K) ≠ 0)
    (rootEquation :
      root ^ 2 = Purelib.Geometry.Plane.Line.Basic.lineNorm firstDiagonal * Purelib.Geometry.Plane.Line.Basic.lineNorm
        secondDiagonal)
    (point : Point K) :
    let axis := Purelib.Geometry.Plane.Line.VertexBisector.Construction.negativeVertexBisector firstDiagonal
      secondDiagonal root
      firstNonNull notParallel
    let axisNonNull := Purelib.Geometry.Plane.Line.VertexBisector.Construction.negativeVertexBisector_nonNull
      firstDiagonal
      secondDiagonal root firstNonNull secondNonNull notParallel twoNonzero
      rootEquation
    Purelib.Geometry.Plane.Line.Basic.lineNorm firstDiagonal *
        Purelib.Geometry.Plane.Line.Basic.lineValue secondDiagonal (Purelib.Geometry.Plane.Reflection.Point.reflectPoint
          axis axisNonNull point) =
      root * Purelib.Geometry.Plane.Line.Basic.lineValue firstDiagonal point := by
  dsimp only
  let axis := Purelib.Geometry.Plane.Line.VertexBisector.Construction.negativeVertexBisector firstDiagonal
    secondDiagonal root
    firstNonNull notParallel
  have axisNonNull := Purelib.Geometry.Plane.Line.VertexBisector.Construction.negativeVertexBisector_nonNull
    firstDiagonal
    secondDiagonal root firstNonNull secondNonNull notParallel twoNonzero
    rootEquation
  have axisNorm := Purelib.Geometry.Plane.Line.VertexBisector.Construction.negativeVertexBisector_norm firstDiagonal
    secondDiagonal
    root firstNonNull notParallel rootEquation
  have normCancel : Purelib.Geometry.Plane.Line.Basic.lineNorm axis * (Purelib.Geometry.Plane.Line.Basic.lineNorm
    axis)⁻¹ = (1 : K) :=
    ExplicitField.mul_inv_cancel _ axisNonNull
  have secondDotAxis :
      secondDiagonal.a * axis.a + secondDiagonal.b * axis.b =
        root * (firstDiagonal.a * secondDiagonal.a +
            firstDiagonal.b * secondDiagonal.b) -
          Purelib.Geometry.Plane.Line.Basic.lineNorm firstDiagonal * Purelib.Geometry.Plane.Line.Basic.lineNorm
            secondDiagonal := by
    change
      secondDiagonal.a *
            (root * firstDiagonal.a -
              Purelib.Geometry.Plane.Line.Basic.lineNorm firstDiagonal * secondDiagonal.a) +
          secondDiagonal.b *
            (root * firstDiagonal.b -
              Purelib.Geometry.Plane.Line.Basic.lineNorm firstDiagonal * secondDiagonal.b) = _
    unfold Purelib.Geometry.Plane.Line.Basic.lineNorm
    ring1
  have axisValue : Purelib.Geometry.Plane.Line.Basic.lineValue axis point =
      root * Purelib.Geometry.Plane.Line.Basic.lineValue firstDiagonal point -
        Purelib.Geometry.Plane.Line.Basic.lineNorm firstDiagonal * Purelib.Geometry.Plane.Line.Basic.lineValue
          secondDiagonal point := by
    change
      (root * firstDiagonal.a -
            Purelib.Geometry.Plane.Line.Basic.lineNorm firstDiagonal * secondDiagonal.a) * point.x +
          (root * firstDiagonal.b -
            Purelib.Geometry.Plane.Line.Basic.lineNorm firstDiagonal * secondDiagonal.b) * point.y +
          (root * firstDiagonal.c -
            Purelib.Geometry.Plane.Line.Basic.lineNorm firstDiagonal * secondDiagonal.c) = _
    unfold Purelib.Geometry.Plane.Line.Basic.lineValue
    ring1
  rw [Purelib.Geometry.Plane.Reflection.Line.Evaluation.Grammola.lineValue_reflectPoint axis secondDiagonal axisNonNull
    point]
  simp only [ExplicitField.div_eq_mul_inv]
  calc
    Purelib.Geometry.Plane.Line.Basic.lineNorm firstDiagonal *
        ((Purelib.Geometry.Plane.Line.Basic.lineNorm axis * Purelib.Geometry.Plane.Line.Basic.lineValue secondDiagonal
          point -
            2 *
                (secondDiagonal.a * axis.a + secondDiagonal.b * axis.b) *
              Purelib.Geometry.Plane.Line.Basic.lineValue axis point) *
          (Purelib.Geometry.Plane.Line.Basic.lineNorm axis)⁻¹) =
      Purelib.Geometry.Plane.Line.Basic.lineNorm firstDiagonal *
        ((Purelib.Geometry.Plane.Line.Basic.lineNorm axis * Purelib.Geometry.Plane.Line.Basic.lineValue secondDiagonal
          point -
            2 *
                (root * (firstDiagonal.a * secondDiagonal.a +
                    firstDiagonal.b * secondDiagonal.b) -
                  Purelib.Geometry.Plane.Line.Basic.lineNorm firstDiagonal * Purelib.Geometry.Plane.Line.Basic.lineNorm
                    secondDiagonal) *
              (root * Purelib.Geometry.Plane.Line.Basic.lineValue firstDiagonal point -
                Purelib.Geometry.Plane.Line.Basic.lineNorm firstDiagonal * Purelib.Geometry.Plane.Line.Basic.lineValue
                  secondDiagonal point)) *
          (Purelib.Geometry.Plane.Line.Basic.lineNorm axis)⁻¹) := by rw [secondDotAxis, axisValue]
    _ =
      (root * Purelib.Geometry.Plane.Line.Basic.lineValue firstDiagonal point) *
        (Purelib.Geometry.Plane.Line.Basic.lineNorm axis * (Purelib.Geometry.Plane.Line.Basic.lineNorm axis)⁻¹) := by
          rw [axisNorm]
          rw [← rootEquation]
          ring1
    _ = root * Purelib.Geometry.Plane.Line.Basic.lineValue firstDiagonal point := by
      rw [normCancel]
      ring1
end Purelib.Geometry.Plane.Line.VertexBisector.Construction
end
