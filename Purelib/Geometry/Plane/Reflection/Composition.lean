module
import Purelib.Algebra.Field.ExplicitField
import Purelib.Geometry.Plane.HalfTurn.Basic
import Purelib.Geometry.Plane.Line.Altitude
import Purelib.Geometry.Plane.Line.Basic
import Purelib.Geometry.Plane.Line.Construction
import Purelib.Geometry.Plane.Line.Relations
import Purelib.Geometry.Plane.Point.Basic
import Purelib.Geometry.Plane.Reflection.Homogeneous
public import Purelib.Geometry.Plane.Reflection.Line
import Purelib.Geometry.Plane.Reflection.Point
import Purelib.Geometry.Projective.Plane.AffineChart
import Purelib.Tactic.QuotientFreeOmega

import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Logic.Nontrivial.Defs
import Purelib.Tactic.Ring

open Purelib.Algebra.Field (ExplicitField)

open Purelib

open Purelib.Geometry

open Purelib.Geometry.Plane

open Purelib.Geometry.Plane.Line

open Purelib.Geometry.Plane.Reflection

open Purelib.Geometry.Projective.Plane

section
section
@[expose] public section
namespace Purelib.Geometry.Plane.Reflection.Composition
variable {K : Type*} [ExplicitField K]

/-- Reflecting successively in a central line and its perpendicular altitude is rotation in their common point. -/
theorem reflectPoint_altitude_comp_eq_rotate
    (line : Plane.Line K) (lineNonNull : ¬ line.IsNull)
    (center : Plane.Point K) (centerContains : line.Contains center)
    (point : Plane.Point K) :
    Reflection.Point.reflectPoint (Construction.altitudeThrough center line)
        (Altitude.altitudeThrough_nonNull center line lineNonNull)
        (Reflection.Point.reflectPoint line lineNonNull point) =
      HalfTurn.Basic.rotateInPoint center point := by
  have normCancel : Basic.lineNorm line * (Basic.lineNorm line)⁻¹ = (1 : K) :=
    ExplicitField.mul_inv_cancel _ lineNonNull
  have altitudeNorm : Basic.lineNorm (Construction.altitudeThrough center line) = Basic.lineNorm line := by
    unfold Basic.lineNorm Construction.altitudeThrough
    ring1
  have constantFormula : line.c = -line.a * center.x - line.b * center.y := by
    unfold Plane.Line.Contains at centerContains
    calc
      line.c =
          (line.a * center.x + line.b * center.y + line.c) -
            line.a * center.x - line.b * center.y := by ring1
      _ = -line.a * center.x - line.b * center.y := by
        rw [centerContains]
        ring1
  rw [Reflection.Point.reflectPoint_formula, Reflection.Point.reflectPoint_formula]
  apply Plane.Point.ext
  · unfold Point.reflectionFormula HalfTurn.Basic.rotateInPoint
    rw [altitudeNorm]
    simp only [Construction.altitudeThrough]
    simp only [ExplicitField.div_eq_mul_inv]
    rw [constantFormula]
    calc
      _ =
        (2 * center.x - point.x) *
          (Basic.lineNorm line * (Basic.lineNorm line)⁻¹) ^ 2 +
          2 * line.b *
            (line.b * center.x - line.a * center.y) *
            (Basic.lineNorm line)⁻¹ *
            (1 - Basic.lineNorm line * (Basic.lineNorm line)⁻¹) := by
              unfold Basic.lineNorm
              ring1
      _ = 2 * center.x - point.x := by rw [normCancel]; ring1
  · unfold Point.reflectionFormula HalfTurn.Basic.rotateInPoint
    rw [altitudeNorm]
    simp only [Construction.altitudeThrough]
    simp only [ExplicitField.div_eq_mul_inv]
    rw [constantFormula]
    calc
      _ =
        (2 * center.y - point.y) *
          (Basic.lineNorm line * (Basic.lineNorm line)⁻¹) ^ 2 +
          2 * line.a *
            (line.a * center.y - line.b * center.x) *
            (Basic.lineNorm line)⁻¹ *
            (1 - Basic.lineNorm line * (Basic.lineNorm line)⁻¹) := by
              unfold Basic.lineNorm
              ring1
      _ = 2 * center.y - point.y := by rw [normCancel]; ring1
end Purelib.Geometry.Plane.Reflection.Composition
end

end

section
section
@[expose] public section
namespace Purelib.Geometry.Plane.Reflection.Composition
variable {K : Type*} [ExplicitField K]

/-- Composition of reflections in any two perpendicular non-null lines through a common point is rotation in that point.
-/
theorem reflectPoint_perpendicular_comp_eq_rotate [DecidableEq K]
    (first second : Plane.Line K)
    (firstNonNull : ¬ first.IsNull) (secondNonNull : ¬ second.IsNull)
    (perpendicular : first.Perpendicular second)
    (center : Plane.Point K) (firstContains : first.Contains center)
    (secondContains : second.Contains center) (point : Plane.Point K) :
    Reflection.Point.reflectPoint second secondNonNull
        (Reflection.Point.reflectPoint first firstNonNull point) =
      HalfTurn.Basic.rotateInPoint center point := by
  have secondParallelAltitude :
      second.Parallel (Construction.altitudeThrough center first) := by
    unfold Plane.Line.Parallel Construction.altitudeThrough
    unfold Plane.Line.Perpendicular at perpendicular
    calc
      second.a * first.a - (-first.b) * second.b =
          first.a * second.a + first.b * second.b := by ring1
      _ = 0 := perpendicular
  have secondEquivalentAltitude :=
    Relations.line_equivalent_of_parallel_and_common_point second
      (Construction.altitudeThrough center first) center secondParallelAltitude
      secondContains (Construction.altitudeThrough_contains center first)
  calc
    Reflection.Point.reflectPoint second secondNonNull
        (Reflection.Point.reflectPoint first firstNonNull point) =
      Reflection.Point.reflectPoint (Construction.altitudeThrough center first)
        (Altitude.altitudeThrough_nonNull center first firstNonNull)
        (Reflection.Point.reflectPoint first firstNonNull point) :=
      Reflection.Point.reflectPoint_eq_of_equivalent second (Construction.altitudeThrough center first)
        secondNonNull
        (Altitude.altitudeThrough_nonNull center first firstNonNull)
        secondEquivalentAltitude (Reflection.Point.reflectPoint first firstNonNull point)
    _ = HalfTurn.Basic.rotateInPoint center point :=
      reflectPoint_altitude_comp_eq_rotate first firstNonNull center
        firstContains point

end Purelib.Geometry.Plane.Reflection.Composition
end

end

section
@[expose] public section
namespace Purelib.Geometry.Plane.Reflection.Composition
variable {K : Type*} [ExplicitField K]

/-- Theorem 16 (Reflection): conjugating a reflection by another reflection reflects its mirror line. -/
theorem reflection_composition [Nontrivial K] [DecidableEq K]
    (firstMirror secondMirror : Plane.Line K)
    (firstNonNull : ¬ firstMirror.IsNull)
    (secondNonNull : ¬ secondMirror.IsNull)
    (point : Plane.Point K) :
    Reflection.Point.reflectPoint secondMirror secondNonNull
        (Reflection.Point.reflectPoint firstMirror firstNonNull point) =
      Reflection.Point.reflectPoint (Line.reflectLine secondMirror firstMirror secondNonNull)
        (Line.reflectLine_nonNull secondMirror firstMirror secondNonNull firstNonNull)
        (Reflection.Point.reflectPoint secondMirror secondNonNull point) := by
  let source := AffineChart.ofPoint point
  let reflectedMirror := Line.reflectLine secondMirror firstMirror secondNonNull
  let reflectedMirrorNonNull :=
    Line.reflectLine_nonNull secondMirror firstMirror secondNonNull firstNonNull
  have sourceZ : source.s ≠ 0 := one_ne_zero
  have firstZ : (Homogeneous.reflectHomogeneous firstMirror source).s ≠ 0 := by
    change Line.Basic.lineNorm firstMirror * 1 ≠ 0
    exact ExplicitField.mul_ne_zero firstNonNull one_ne_zero
  have secondZ : (Homogeneous.reflectHomogeneous secondMirror source).s ≠ 0 := by
    change Line.Basic.lineNorm secondMirror * 1 ≠ 0
    exact ExplicitField.mul_ne_zero secondNonNull one_ne_zero
  have secondAfterFirstZ :
      (Homogeneous.reflectHomogeneous secondMirror
        (Homogeneous.reflectHomogeneous firstMirror source)).s ≠ 0 := by
    change Line.Basic.lineNorm secondMirror * (Line.Basic.lineNorm firstMirror * 1) ≠ 0
    exact ExplicitField.mul_ne_zero secondNonNull firstZ
  have scaleNonzero : Line.Basic.lineNorm secondMirror ^ 2 ≠ 0 := by
    intro squareZero
    apply (ExplicitField.mul_ne_zero secondNonNull secondNonNull)
    calc
      Line.Basic.lineNorm secondMirror * Line.Basic.lineNorm secondMirror =
          Line.Basic.lineNorm secondMirror ^ 2 := by ring1
      _ = 0 := squareZero
  have polynomialIdentity :=
    Homogeneous.reflectHomogeneous_conjugation firstMirror secondMirror secondNonNull source
  have chartIdentity := congrArg AffineChart.affineChart polynomialIdentity
  rw [AffineChart.affineChart_scale _ _ scaleNonzero secondAfterFirstZ]
    at chartIdentity
  have leftChart :
      (AffineChart.affineChart (Homogeneous.reflectHomogeneous secondMirror
        (Homogeneous.reflectHomogeneous firstMirror source))) =
      Reflection.Point.reflectionFormula secondMirror (Reflection.Point.reflectionFormula firstMirror point) := by
    rw [Homogeneous.affineChart_reflectHomogeneous secondMirror secondNonNull _ firstZ,
      Homogeneous.affineChart_reflectHomogeneous firstMirror firstNonNull source sourceZ,
      AffineChart.affineChart_ofPoint]
  have rightChart :
      (AffineChart.affineChart (Homogeneous.reflectHomogeneous reflectedMirror
        (Homogeneous.reflectHomogeneous secondMirror source))) =
      Reflection.Point.reflectionFormula reflectedMirror (Reflection.Point.reflectionFormula secondMirror point) := by
    rw [Homogeneous.affineChart_reflectHomogeneous reflectedMirror reflectedMirrorNonNull _ secondZ,
      Homogeneous.affineChart_reflectHomogeneous secondMirror secondNonNull source sourceZ,
      AffineChart.affineChart_ofPoint]
  rw [rightChart, leftChart] at chartIdentity
  rw [Reflection.Point.reflectPoint_formula, Reflection.Point.reflectPoint_formula,
    Reflection.Point.reflectPoint_formula,
    Reflection.Point.reflectPoint_formula]
  exact chartIdentity.symm

end Purelib.Geometry.Plane.Reflection.Composition
end

end
