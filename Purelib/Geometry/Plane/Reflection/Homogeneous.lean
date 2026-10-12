module
import Purelib.Geometry.Plane.Line.Basic
import Purelib.Geometry.Plane.Point.Basic
public import Purelib.Geometry.Plane.Reflection.Line
import Purelib.Geometry.Plane.Reflection.Point
public import Purelib.Geometry.Projective.Plane.AffineChart
import Purelib.LinearAlgebra.Coordinates3.Vector
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Algebra.Field.ExplicitField
import Purelib.Tactic.Ring

open Purelib.Algebra.Field (ExplicitField)

open Purelib

open Purelib.Geometry

open Purelib.Geometry.Plane

open Purelib.Geometry.Plane.Reflection

open Purelib.Geometry.Projective.Plane

open Purelib.LinearAlgebra

@[expose] public section
namespace Purelib.Geometry.Plane.Reflection.Homogeneous
variable {K : Type*} [ExplicitField K]

/-- Polynomial homogeneous action corresponding to reflection in `line`. -/
def reflectHomogeneous (line : Plane.Line K) (point :
  Coordinates3.Vector K) :
    Coordinates3.Vector K :=
  ⟨(line.b ^ 2 - line.a ^ 2) * point.t -
      2 * line.a * line.b * point.r - 2 * line.a * line.c * point.s,
    -2 * line.a * line.b * point.t +
      (line.a ^ 2 - line.b ^ 2) * point.r - 2 * line.b * line.c * point.s,
    Line.Basic.lineNorm line * point.s⟩
end Purelib.Geometry.Plane.Reflection.Homogeneous
end

@[expose] public section
namespace Purelib.Geometry.Plane.Reflection.Homogeneous
variable {K : Type*} [ExplicitField K]

/-- Homogeneous reflection agrees with affine point reflection.

A non-null mirror and a nonzero homogeneous chart coordinate justify both divisions in the affine formula. -/
theorem affineChart_reflectHomogeneous (line : Plane.Line K)
    (lineNonNull : ¬ line.IsNull) (point : Coordinates3.Vector K)
    (zNonzero : point.s ≠ 0) :
    (AffineChart.affineChart (reflectHomogeneous line point)) =
      Reflection.Point.reflectionFormula line (AffineChart.affineChart point) := by
  have normNonzero : Line.Basic.lineNorm line ≠ 0 := lineNonNull
  have zCancel : point.s * point.s⁻¹ = (1 : K) :=
    ExplicitField.mul_inv_cancel point.s zNonzero
  have productInverse :
      (Line.Basic.lineNorm line * point.s)⁻¹ = point.s⁻¹ * (Line.Basic.lineNorm line)⁻¹ := by
    have normCancel : Line.Basic.lineNorm line * (Line.Basic.lineNorm line)⁻¹ = (1 : K) :=
      ExplicitField.mul_inv_cancel _ normNonzero
    have candidateCancel :
        (Line.Basic.lineNorm line * point.s) *
            (point.s⁻¹ * (Line.Basic.lineNorm line)⁻¹) = (1 : K) := by
      calc
        _ = (Line.Basic.lineNorm line * (Line.Basic.lineNorm line)⁻¹) *
            (point.s * point.s⁻¹) := by ring1
        _ = 1 := by rw [normCancel, zCancel]; exact one_mul 1
    have canonicalCancel :
        (Line.Basic.lineNorm line * point.s) *
            (Line.Basic.lineNorm line * point.s)⁻¹ = (1 : K) :=
      ExplicitField.mul_inv_cancel _
        (ExplicitField.mul_ne_zero normNonzero zNonzero)
    calc
      (Line.Basic.lineNorm line * point.s)⁻¹ =
          (Line.Basic.lineNorm line * point.s)⁻¹ * 1 := by rw [mul_one]
      _ = (Line.Basic.lineNorm line * point.s)⁻¹ *
          ((Line.Basic.lineNorm line * point.s) *
            (point.s⁻¹ * (Line.Basic.lineNorm line)⁻¹)) := by rw [candidateCancel]
      _ = ((Line.Basic.lineNorm line * point.s) *
            (Line.Basic.lineNorm line * point.s)⁻¹) *
          (point.s⁻¹ * (Line.Basic.lineNorm line)⁻¹) := by ring1
      _ = point.s⁻¹ * (Line.Basic.lineNorm line)⁻¹ := by
        rw [canonicalCancel]
        exact one_mul _
  apply Plane.Point.ext
  · change
      ((line.b ^ 2 - line.a ^ 2) * point.t -
          2 * line.a * line.b * point.r - 2 * line.a * line.c * point.s) /
          (Line.Basic.lineNorm line * point.s) =
        ((line.b ^ 2 - line.a ^ 2) * (point.t / point.s) -
          2 * line.a * line.b * (point.r / point.s) -
          2 * line.a * line.c) / Line.Basic.lineNorm line
    simp only [ExplicitField.div_eq_mul_inv, productInverse]
    calc
      ((line.b ^ 2 - line.a ^ 2) * point.t -
            2 * line.a * line.b * point.r -
            2 * line.a * line.c * point.s) *
          (point.s⁻¹ * (Line.Basic.lineNorm line)⁻¹) =
        ((line.b ^ 2 - line.a ^ 2) * (point.t * point.s⁻¹) -
            2 * line.a * line.b * (point.r * point.s⁻¹) -
            2 * line.a * line.c * (point.s * point.s⁻¹)) *
          (Line.Basic.lineNorm line)⁻¹ := by ring1
      _ = ((line.b ^ 2 - line.a ^ 2) * (point.t * point.s⁻¹) -
            2 * line.a * line.b * (point.r * point.s⁻¹) -
            2 * line.a * line.c) * (Line.Basic.lineNorm line)⁻¹ := by rw [zCancel]; ring1
  · change
      (-2 * line.a * line.b * point.t +
          (line.a ^ 2 - line.b ^ 2) * point.r -
          2 * line.b * line.c * point.s) /
          (Line.Basic.lineNorm line * point.s) =
        (-2 * line.a * line.b * (point.t / point.s) +
          (line.a ^ 2 - line.b ^ 2) * (point.r / point.s) -
          2 * line.b * line.c) / Line.Basic.lineNorm line
    simp only [ExplicitField.div_eq_mul_inv, productInverse]
    calc
      (-2 * line.a * line.b * point.t +
            (line.a ^ 2 - line.b ^ 2) * point.r -
            2 * line.b * line.c * point.s) *
          (point.s⁻¹ * (Line.Basic.lineNorm line)⁻¹) =
        (-2 * line.a * line.b * (point.t * point.s⁻¹) +
            (line.a ^ 2 - line.b ^ 2) * (point.r * point.s⁻¹) -
            2 * line.b * line.c * (point.s * point.s⁻¹)) *
          (Line.Basic.lineNorm line)⁻¹ := by ring1
      _ = (-2 * line.a * line.b * (point.t * point.s⁻¹) +
            (line.a ^ 2 - line.b ^ 2) * (point.r * point.s⁻¹) -
            2 * line.b * line.c) * (Line.Basic.lineNorm line)⁻¹ := by rw [zCancel]; ring1
end Purelib.Geometry.Plane.Reflection.Homogeneous
end

@[expose] public section
namespace Purelib.Geometry.Plane.Reflection.Homogeneous
variable {K : Type*} [ExplicitField K]

/-- Conjugating homogeneous reflections reflects the mirror, up to a square norm factor.

The polynomial identity retains the second mirror norm squared as the common scale and requires that mirror to be
non-null. -/
theorem reflectHomogeneous_conjugation [DecidableEq K]
    (firstMirror secondMirror : Plane.Line K)
    (secondNonNull : ¬ secondMirror.IsNull)
    (point : Coordinates3.Vector K) :
    reflectHomogeneous
        (Line.reflectLine secondMirror firstMirror secondNonNull)
        (reflectHomogeneous secondMirror point) =
      Coordinates3.Vector.scale (Line.Basic.lineNorm secondMirror ^ 2)
        (reflectHomogeneous secondMirror
          (reflectHomogeneous firstMirror point)) := by
  apply Coordinates3.Vector.ext <;>
    unfold reflectHomogeneous Coordinates3.Vector.scale Line.reflectLine
      Line.reflectedLineA Line.reflectedLineB Line.reflectedLineC Line.Basic.lineNorm <;>
    ring1
end Purelib.Geometry.Plane.Reflection.Homogeneous
end
