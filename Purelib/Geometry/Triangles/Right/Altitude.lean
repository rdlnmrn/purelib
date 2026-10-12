module
import Purelib.Geometry.Triangles.Quadrance.Basic
import Purelib.Geometry.Triangles.NonNull.Basic
import Purelib.Algebra.Field.Cancellation
import Purelib.Algebra.Field.ExplicitField
import Purelib.Geometry.Plane.Line.Altitude
import Purelib.Geometry.Plane.Line.Basic
import Purelib.Geometry.Plane.Line.Construction
import Purelib.Geometry.Plane.Line.Incidence
import Purelib.Geometry.Plane.Line.Quadrance
import Purelib.Geometry.Plane.Line.Relations
import Purelib.Geometry.Plane.Point.Quadrance
public import Purelib.Geometry.Triangles.Altitude.Foot
import Purelib.Geometry.Triangles.Quadrea.Basic
import Purelib.Geometry.Triangles.Right.Quadrance
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.LinearAlgebra.Coordinates3.Vector
import Purelib.Tactic.Ring

open Purelib.Algebra.Field (ExplicitField)

open Purelib

open Purelib.Geometry.Plane

open Purelib.Geometry.Plane.Line

open Purelib.Geometry.Plane.Line.Basic

open Purelib.Geometry.Plane.Point

open Purelib.Geometry.Triangles

open Purelib.Geometry.Triangles.Altitude.Foot

section
@[expose] public section

/-!
# Divine Proportions, Chapter 10 further exercises

This module contains the equilateral centroid calculations, the unit-
quadrance existence criterion, and the corrected right-altitude formulas.
-/

namespace Purelib.Geometry.Triangles.Right.Altitude

variable {K : Type*} [ExplicitField K]

/-- Exercise 10.6, corrected. Under the source convention `Q₁=Q(A₂,A₃)`, `Q₂=Q(A₁,A₃)`, the printed first two numerators
are interchanged: `Q(A₁,F)=Q₂²/Q₃` and `Q(A₂,F)=Q₁²/Q₃`. -/
theorem quadrance_formulas [DecidableEq K]
    (triangle : NonNull.Basic.NonNullTriangle K) (twoNonzero : (2 : K) ≠ 0)
    (rightAtThird :
      (Incidence.lineThrough triangle.first triangle.third
          triangle.firstThirdDistinct).Perpendicular
        (Incidence.lineThrough triangle.second triangle.third
          triangle.secondThirdDistinct)) :
    Quadrance.quadrance triangle.first (NonNullTriangle.thirdAltitudeFoot triangle) =
        triangle.quadrances.r ^ 2 / triangle.quadrances.s ∧
      Quadrance.quadrance triangle.second (NonNullTriangle.thirdAltitudeFoot triangle) =
        triangle.quadrances.t ^ 2 / triangle.quadrances.s ∧
      Quadrance.quadrance triangle.third (NonNullTriangle.thirdAltitudeFoot triangle) =
        triangle.quadrances.t * triangle.quadrances.r /
          triangle.quadrances.s := by
  let base := Incidence.lineThrough triangle.first triangle.second
    triangle.firstSecondDistinct
  let foot := NonNullTriangle.thirdAltitudeFoot triangle
  have baseContainsFirst : base.Contains triangle.first := by
    unfold base
    exact Incidence.lineThrough_contains_first triangle.first triangle.second
      triangle.firstSecondDistinct
  have baseContainsSecond : base.Contains triangle.second := by
    unfold base
    exact Incidence.lineThrough_contains_second triangle.first triangle.second
      triangle.firstSecondDistinct
  have footOnBase : base.Contains foot := by
    unfold foot NonNullTriangle.thirdAltitudeFoot base
    exact Altitude.altitudeFoot_on_line triangle.third
      (Incidence.lineThrough triangle.first triangle.second
        triangle.firstSecondDistinct) triangle.firstSecondNonNull
  have footOnAltitude :
      (Construction.altitudeThrough triangle.third base).Contains foot := by
    unfold foot NonNullTriangle.thirdAltitudeFoot base
    exact Altitude.altitudeFoot_on_altitude triangle.third
      (Incidence.lineThrough triangle.first triangle.second
        triangle.firstSecondDistinct) triangle.firstSecondNonNull
  have thirdFootDistinct : triangle.third ≠ foot := by
    intro equalPoints
    apply triangle.notCollinear
    refine ⟨base, baseContainsFirst, baseContainsSecond, ?_⟩
    rw [equalPoints]
    exact footOnBase
  have cevianParallelAltitude :
      (Incidence.lineThrough triangle.third foot thirdFootDistinct).Parallel
        (Construction.altitudeThrough triangle.third base) :=
    Incidence.lineThrough_parallel_of_contains (Construction.altitudeThrough triangle.third base)
      triangle.third foot thirdFootDistinct
      (Construction.altitudeThrough_contains triangle.third base) footOnAltitude
  have firstPythagoras :
      Quadrance.quadrance triangle.third foot + Quadrance.quadrance triangle.first foot =
        Quadrance.quadrance triangle.first triangle.third := by
    by_cases footIsFirst : foot = triangle.first
    · rw [footIsFirst, Quadrance.quadrance_self, add_zero,
        Quadrance.quadrance_symm triangle.third triangle.first]
    · have firstFootDistinct : triangle.first ≠ foot := by
        intro equalPoints
        exact footIsFirst equalPoints.symm
      have firstFootParallel :
          (Incidence.lineThrough triangle.first foot firstFootDistinct).Parallel base :=
        Incidence.lineThrough_parallel_of_contains base triangle.first foot
          firstFootDistinct baseContainsFirst footOnBase
      have firstFootPerpendicularAltitude :
          (Incidence.lineThrough triangle.first foot firstFootDistinct).Perpendicular
            (Construction.altitudeThrough triangle.third base) :=
        Relations.perpendicular_of_parallel_left base
          (Incidence.lineThrough triangle.first foot firstFootDistinct)
          (Construction.altitudeThrough triangle.third base)
          (Geometry.Plane.Line.parallel_symm firstFootParallel)
          (Geometry.Plane.Line.perpendicular_symm
            (Construction.altitudeThrough_perpendicular triangle.third base))
      have cevianPerpendicularFirstFoot :
          (Incidence.lineThrough triangle.third foot thirdFootDistinct).Perpendicular
            (Incidence.lineThrough triangle.first foot firstFootDistinct) :=
        Relations.perpendicular_of_parallel_left (Construction.altitudeThrough triangle.third base)
          (Incidence.lineThrough triangle.third foot thirdFootDistinct)
          (Incidence.lineThrough triangle.first foot firstFootDistinct)
          (Geometry.Plane.Line.parallel_symm cevianParallelAltitude)
          (Geometry.Plane.Line.perpendicular_symm firstFootPerpendicularAltitude)
      exact (Right.Quadrance.pythagoras_iff_perpendicular triangle.first triangle.third foot
        firstFootDistinct thirdFootDistinct twoNonzero).2
          (Geometry.Plane.Line.perpendicular_symm cevianPerpendicularFirstFoot)
  have secondPythagoras :
      Quadrance.quadrance triangle.third foot + Quadrance.quadrance triangle.second foot =
        Quadrance.quadrance triangle.second triangle.third := by
    by_cases footIsSecond : foot = triangle.second
    · rw [footIsSecond, Quadrance.quadrance_self, add_zero,
        Quadrance.quadrance_symm triangle.third triangle.second]
    · have secondFootDistinct : triangle.second ≠ foot := by
        intro equalPoints
        exact footIsSecond equalPoints.symm
      have secondFootParallel :
          (Incidence.lineThrough triangle.second foot secondFootDistinct).Parallel base :=
        Incidence.lineThrough_parallel_of_contains base triangle.second foot
          secondFootDistinct baseContainsSecond footOnBase
      have secondFootPerpendicularAltitude :
          (Incidence.lineThrough triangle.second foot secondFootDistinct).Perpendicular
            (Construction.altitudeThrough triangle.third base) :=
        Relations.perpendicular_of_parallel_left base
          (Incidence.lineThrough triangle.second foot secondFootDistinct)
          (Construction.altitudeThrough triangle.third base)
          (Geometry.Plane.Line.parallel_symm secondFootParallel)
          (Geometry.Plane.Line.perpendicular_symm
            (Construction.altitudeThrough_perpendicular triangle.third base))
      have cevianPerpendicularSecondFoot :
          (Incidence.lineThrough triangle.third foot thirdFootDistinct).Perpendicular
            (Incidence.lineThrough triangle.second foot secondFootDistinct) :=
        Relations.perpendicular_of_parallel_left (Construction.altitudeThrough triangle.third base)
          (Incidence.lineThrough triangle.third foot thirdFootDistinct)
          (Incidence.lineThrough triangle.second foot secondFootDistinct)
          (Geometry.Plane.Line.parallel_symm cevianParallelAltitude)
          (Geometry.Plane.Line.perpendicular_symm secondFootPerpendicularAltitude)
      exact (Right.Quadrance.pythagoras_iff_perpendicular triangle.second triangle.third foot
        secondFootDistinct thirdFootDistinct twoNonzero).2
          (Geometry.Plane.Line.perpendicular_symm cevianPerpendicularSecondFoot)
  have fourNonzero : (4 : K) ≠ 0 := by
    have squareNonzero :=
      ExplicitField.mul_ne_zero twoNonzero twoNonzero
    simpa only [show (4 : K) = 2 * 2 by ring1] using squareNonzero
  have rightArea := Right.Quadrance.right_triangle_quadrea triangle.first triangle.second
    triangle.third triangle.firstThirdDistinct
    triangle.secondThirdDistinct twoNonzero rightAtThird
  have coordinateArea :=
    Quadrea.Basic.quadrea_coordinate_formula triangle.first triangle.second triangle.third
  have determinantSquare :
      Incidence.pointDeterminant triangle.first triangle.second triangle.third ^ 2 =
        triangle.quadrances.t * triangle.quadrances.r := by
    apply ExplicitField.eq_of_mul_eq_mul_left fourNonzero
    calc
      4 * Incidence.pointDeterminant triangle.first triangle.second triangle.third ^ 2 =
          Quadrea.Basic.quadrea triangle.first triangle.second triangle.third :=
        coordinateArea.symm
      _ = 4 * Quadrance.quadrance triangle.second triangle.third *
          Quadrance.quadrance triangle.first triangle.third := rightArea
      _ = 4 *
          (triangle.quadrances.t * triangle.quadrances.r) := by
        unfold NonNull.Basic.NonNullTriangle.quadrances Quadrance.Basic.triangleQuadrances
        ring1
  have lineValueSquare :
      (base.a * triangle.third.x + base.b * triangle.third.y + base.c) ^ 2 =
        Incidence.pointDeterminant triangle.first triangle.second triangle.third ^ 2 := by
    unfold base Incidence.lineThrough Incidence.pointDeterminant
    ring1
  have heightFormula :
      Quadrance.quadrance triangle.third foot =
        triangle.quadrances.t * triangle.quadrances.r /
          triangle.quadrances.s := by
    have distanceFormula :=
      Quadrance.pointLineQuadrance_formula triangle.third base
        triangle.firstSecondNonNull
    change Quadrance.quadrance triangle.third foot =
      (base.a * triangle.third.x + base.b * triangle.third.y + base.c) ^ 2 /
        Line.Basic.lineNorm base at distanceFormula
    calc
      Quadrance.quadrance triangle.third foot =
          (base.a * triangle.third.x + base.b * triangle.third.y +
            base.c) ^ 2 / Line.Basic.lineNorm base := distanceFormula
      _ = Incidence.pointDeterminant triangle.first triangle.second triangle.third ^ 2 /
          triangle.quadrances.s := by
        rw [lineValueSquare]
        unfold base NonNull.Basic.NonNullTriangle.quadrances Quadrance.Basic.triangleQuadrances
        rw [Quadrance.lineThrough_norm_eq_quadrance]
      _ = triangle.quadrances.t * triangle.quadrances.r /
          triangle.quadrances.s := by rw [determinantSquare]
  have originalPythagoras :
      triangle.quadrances.t + triangle.quadrances.r =
        triangle.quadrances.s :=
    (Right.Quadrance.pythagoras_iff_perpendicular triangle.first triangle.second
      triangle.third triangle.firstThirdDistinct
      triangle.secondThirdDistinct twoNonzero).2 rightAtThird
  change Quadrance.quadrance triangle.third foot + Quadrance.quadrance triangle.first foot =
    triangle.quadrances.r at firstPythagoras
  change Quadrance.quadrance triangle.third foot + Quadrance.quadrance triangle.second foot =
    triangle.quadrances.t at secondPythagoras
  have firstProjection :
      Quadrance.quadrance triangle.first foot =
        triangle.quadrances.r ^ 2 / triangle.quadrances.s := by
    apply ExplicitField.eq_of_mul_eq_mul_right triangle.thirdQuadranceNonzero
    calc
      Quadrance.quadrance triangle.first foot * triangle.quadrances.s =
          (triangle.quadrances.r - Quadrance.quadrance triangle.third foot) *
            triangle.quadrances.s := by
        rw [← firstPythagoras]
        ring1
      _ = (triangle.quadrances.r -
            triangle.quadrances.t * triangle.quadrances.r /
              triangle.quadrances.s) * triangle.quadrances.s := by
        rw [heightFormula]
      _ = triangle.quadrances.r * triangle.quadrances.s -
          triangle.quadrances.t * triangle.quadrances.r := by
        calc
          (triangle.quadrances.r -
                triangle.quadrances.t * triangle.quadrances.r /
                  triangle.quadrances.s) *
              triangle.quadrances.s =
            triangle.quadrances.r * triangle.quadrances.s -
              (triangle.quadrances.t * triangle.quadrances.r /
                triangle.quadrances.s) *
                triangle.quadrances.s := by ring1
          _ = triangle.quadrances.r * triangle.quadrances.s -
              triangle.quadrances.t * triangle.quadrances.r := by
            rw [ExplicitField.div_mul_cancel _
              triangle.thirdQuadranceNonzero]
      _ = triangle.quadrances.r ^ 2 := by
        rw [← originalPythagoras]
        ring1
      _ = (triangle.quadrances.r ^ 2 /
          triangle.quadrances.s) * triangle.quadrances.s :=
        (ExplicitField.div_mul_cancel _
          triangle.thirdQuadranceNonzero).symm
  have secondProjection :
      Quadrance.quadrance triangle.second foot =
        triangle.quadrances.t ^ 2 / triangle.quadrances.s := by
    apply ExplicitField.eq_of_mul_eq_mul_right triangle.thirdQuadranceNonzero
    calc
      Quadrance.quadrance triangle.second foot * triangle.quadrances.s =
          (triangle.quadrances.t - Quadrance.quadrance triangle.third foot) *
            triangle.quadrances.s := by
        rw [← secondPythagoras]
        ring1
      _ = (triangle.quadrances.t -
            triangle.quadrances.t * triangle.quadrances.r /
              triangle.quadrances.s) * triangle.quadrances.s := by
        rw [heightFormula]
      _ = triangle.quadrances.t * triangle.quadrances.s -
          triangle.quadrances.t * triangle.quadrances.r := by
        calc
          (triangle.quadrances.t -
                triangle.quadrances.t * triangle.quadrances.r /
                  triangle.quadrances.s) *
              triangle.quadrances.s =
            triangle.quadrances.t * triangle.quadrances.s -
              (triangle.quadrances.t * triangle.quadrances.r /
                triangle.quadrances.s) *
                triangle.quadrances.s := by ring1
          _ = triangle.quadrances.t * triangle.quadrances.s -
              triangle.quadrances.t * triangle.quadrances.r := by
            rw [ExplicitField.div_mul_cancel _
              triangle.thirdQuadranceNonzero]
      _ = triangle.quadrances.t ^ 2 := by
        rw [← originalPythagoras]
        ring1
      _ = (triangle.quadrances.t ^ 2 /
          triangle.quadrances.s) * triangle.quadrances.s :=
        (ExplicitField.div_mul_cancel _
          triangle.thirdQuadranceNonzero).symm
  exact ⟨firstProjection, secondProjection, heightFormula⟩

end Purelib.Geometry.Triangles.Right.Altitude

end
