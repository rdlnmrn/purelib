module
public import Purelib.Geometry.Plane.Line.Incidence
import Purelib.Geometry.Plane.Point.Basic
public import Purelib.Geometry.Plane.Point.Quadrance

import Purelib.Algebra.Field.ExplicitField
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Purelib.Geometry.Plane.Line.Basic
import Purelib.Tactic.Ring

open Purelib.Geometry

open Purelib.Geometry.Plane.Line

open Purelib.Geometry.Plane.Point

@[expose] public section

/-!
# Divine Proportions, Chapter 11: Stewart's theorem

The proof below is stronger than the source's two-case spread argument.  After
writing the base as two collinear displacement vectors, a finite two-dimensional
dot/determinant identity proves the formula uniformly, including the source's
`R₃ = 0` case.
-/

namespace Purelib.Geometry.Triangles.Stewart

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- Stewart's polynomial relation for a point on the line through a triangle's base.

The base endpoints are distinct and the point carries an incidence proof; no division or non-null quadrance assumption
is required. -/
theorem stewart [DecidableEq K]
    (first second vertex point : Plane.Point K)
    (firstSecondDistinct : first ≠ second)
    (pointOnBase :
      (Incidence.lineThrough first second firstSecondDistinct).Contains point) :
    Quadrance.quadrance second point *
        (Quadrance.quadrance vertex point + Quadrance.quadrance first point -
          Quadrance.quadrance first vertex) ^ 2 =
      Quadrance.quadrance first point *
        (Quadrance.quadrance vertex point + Quadrance.quadrance second point -
          Quadrance.quadrance second vertex) ^ 2 := by
  let a := point.x - first.x
  let b := point.y - first.y
  let c := second.x - point.x
  let d := second.y - point.y
  let u := vertex.x - point.x
  let v := vertex.y - point.y
  let firstDot := u * a + v * b
  let secondDot := u * c + v * d
  let determinant := a * d - b * c
  have pointOnBaseExpanded :
      (first.y - second.y) * point.x +
          (second.x - first.x) * point.y +
          (first.x * second.y - second.x * first.y) = 0 :=
    pointOnBase
  have determinantZero : determinant = 0 := by
    unfold determinant a b c d
    calc
      (point.x - first.x) * (second.y - point.y) -
          (point.y - first.y) * (second.x - point.x) =
        -((first.y - second.y) * point.x +
          (second.x - first.x) * point.y +
          (first.x * second.y - second.x * first.y)) := by ring1
      _ = 0 := by rw [pointOnBaseExpanded]; ring1
  have firstMetricIdentity :
      Quadrance.quadrance vertex point + Quadrance.quadrance first point -
          Quadrance.quadrance first vertex = -2 * firstDot := by
    unfold Quadrance.quadrance firstDot u v a b
    ring1
  have secondMetricIdentity :
      Quadrance.quadrance vertex point + Quadrance.quadrance second point -
          Quadrance.quadrance second vertex = 2 * secondDot := by
    unfold Quadrance.quadrance secondDot u v c d
    ring1
  have dotNormDifferenceZero :
      Quadrance.quadrance second point * firstDot ^ 2 -
        Quadrance.quadrance first point * secondDot ^ 2 = 0 := by
    calc
      Quadrance.quadrance second point * firstDot ^ 2 -
          Quadrance.quadrance first point * secondDot ^ 2 =
        determinant *
          ((a * d + b * c) * (u ^ 2 - v ^ 2) +
            2 * u * v * (b * d - a * c)) := by
        unfold Quadrance.quadrance firstDot secondDot determinant a b c d u v
        ring1
      _ = 0 := by rw [determinantZero]; ring1
  have dotNormEquality :
      Quadrance.quadrance second point * firstDot ^ 2 =
        Quadrance.quadrance first point * secondDot ^ 2 := by
    calc
      Quadrance.quadrance second point * firstDot ^ 2 =
          (Quadrance.quadrance second point * firstDot ^ 2 -
            Quadrance.quadrance first point * secondDot ^ 2) +
              Quadrance.quadrance first point * secondDot ^ 2 := by ring1
      _ = Quadrance.quadrance first point * secondDot ^ 2 := by
        rw [dotNormDifferenceZero]
        ring1
  rw [firstMetricIdentity, secondMetricIdentity]
  calc
    Quadrance.quadrance second point * (-2 * firstDot) ^ 2 =
        4 * (Quadrance.quadrance second point * firstDot ^ 2) := by ring1
    _ = 4 * (Quadrance.quadrance first point * secondDot ^ 2) := by
      rw [dotNormEquality]
    _ = Quadrance.quadrance first point * (2 * secondDot) ^ 2 := by ring1

end Purelib.Geometry.Triangles.Stewart

end
