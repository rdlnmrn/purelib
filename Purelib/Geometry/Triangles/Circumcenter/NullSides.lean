module
public import Purelib.Algebra.Group.Basic
public import Purelib.Data.Nat.Order
public import Purelib.Algebra.Group.Negation
import Purelib.Geometry.Plane.Line.Incidence
import Purelib.Geometry.Plane.Line.Quadrance
import Purelib.Geometry.Plane.Point.Basic
import Purelib.Geometry.Plane.Point.Quadrance

import Purelib.Algebra.Field.ExplicitField
public import Purelib.Geometry.Triangles.Circumcenter.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Logic.Nontrivial.Defs
import Purelib.Geometry.Plane.Line.Basic
import Purelib.Tactic.Ring

open Purelib.Algebra.Field (ExplicitField)

section
open Purelib.Algebra
open Purelib.Data

-- These owned adapters retain the complete original operation dictionaries.
attribute [local instance 2000] Group.Negation.subNegZeroMonoid
  Nat.successorNeZero Nat.successorAtLeastTwo

open Purelib

open Purelib.Geometry

open Purelib.Geometry.Plane.Line

open Purelib.Geometry.Plane.Point

open Purelib.Geometry.Triangles

section
public section

/-!
# Divine Proportions, remaining Chapter 12 exercises

This module completes the reader exercises: the finite chord argument from
Exercise 12.1, the null-side circumcenter argument from Exercise 12.4, and the
remaining exact polynomial and spread calculations.
-/

namespace Purelib.Geometry.Triangles.Circumcenter.NullSides

open Purelib.Algebra

variable {K : Type*} [ExplicitField K]

/-- The finite metric core of Exercise 12.4. A point equidistant from the ends of a null segment lies on that segment's
line. -/
theorem equal_quadrance_center_collinear_of_null
    [Nontrivial K] [DecidableEq K]
    (first second center : Geometry.Plane.Point K) (twoNonzero : (2 : K) ≠ 0)
    (sideNull : Quadrance.quadrance first second = 0)
    (equalRadii : Quadrance.quadrance center first = Quadrance.quadrance center second) :
    Incidence.Collinear first second center := by
  let directionX := second.x - first.x
  let directionY := second.y - first.y
  let centerX := center.x - first.x
  let centerY := center.y - first.y
  have directionNull : directionX ^ 2 + directionY ^ 2 = 0 := by
    exact sideNull
  have twiceDot :
      2 * (directionX * centerX + directionY * centerY) = 0 := by
    calc
      2 * (directionX * centerX + directionY * centerY) =
          Quadrance.quadrance center first - Quadrance.quadrance center second +
            Quadrance.quadrance first second := by
        unfold Quadrance.quadrance directionX directionY centerX centerY
        ring1
      _ = 0 := by rw [equalRadii, sideNull]; ring1
  have dotZero : directionX * centerX + directionY * centerY = 0 := by
    by_cases zero : directionX * centerX + directionY * centerY = 0
    · exact zero
    · exact False.elim
        ((ExplicitField.mul_ne_zero twoNonzero zero) twiceDot)
  have determinantSquareZero :
      Incidence.pointDeterminant first second center ^ 2 = 0 := by
    calc
      Incidence.pointDeterminant first second center ^ 2 =
          (directionX * centerY - directionY * centerX) ^ 2 := by
        unfold Incidence.pointDeterminant directionX directionY centerX centerY
        ring1
      _ = (directionX ^ 2 + directionY ^ 2) *
            (centerX ^ 2 + centerY ^ 2) -
          (directionX * centerX + directionY * centerY) ^ 2 := by
        ring1
      _ = 0 := by rw [directionNull, dotZero]; ring1
  have determinantZero : Incidence.pointDeterminant first second center = 0 := by
    by_cases zero : Incidence.pointDeterminant first second center = 0
    · exact zero
    · have squareNonzero := ExplicitField.mul_ne_zero zero zero
      apply False.elim
      apply squareNonzero
      calc
        Incidence.pointDeterminant first second center *
            Incidence.pointDeterminant first second center =
          Incidence.pointDeterminant first second center ^ 2 := by ring1
        _ = 0 := determinantSquareZero
  exact (Incidence.collinear_iff_pointDeterminant_eq_zero first second center).2
    determinantZero

/-- Exercise 12.4, first clause: the constructed circumcenter lies on every null side. -/
theorem exercise_12_4_first
    [Nontrivial K] [DecidableEq K]
    (first second third : Geometry.Plane.Point K)
    (firstSecondDistinct : first ≠ second)
    (firstThirdDistinct : first ≠ third)
    (secondThirdDistinct : second ≠ third)
    (notCollinear : ¬ Incidence.Collinear first second third)
    (twoNonzero : (2 : K) ≠ 0)
    (secondThirdNull :
      (Incidence.lineThrough second third secondThirdDistinct).IsNull) :
    Incidence.Collinear second third
      (Circumcenter.Basic.circumcenterPoint first second third firstThirdDistinct
        secondThirdDistinct notCollinear) := by
  have centerData := Circumcenter.Basic.circumcenter first second third firstSecondDistinct
    firstThirdDistinct secondThirdDistinct notCollinear twoNonzero
  have sideQuadranceZero :=
    (Quadrance.null_line_iff_quadrance_zero second third secondThirdDistinct).1
      secondThirdNull
  exact equal_quadrance_center_collinear_of_null second third
    (Circumcenter.Basic.circumcenterPoint first second third firstThirdDistinct
      secondThirdDistinct notCollinear)
    twoNonzero sideQuadranceZero centerData.2.2.2.2

/-- Two independent null sides force the circumcenter to be their common vertex, completing Exercise 12.4. -/
theorem exercise_12_4_second
    [Nontrivial K] [DecidableEq K]
    (first second third : Geometry.Plane.Point K)
    (firstSecondDistinct : first ≠ second)
    (firstThirdDistinct : first ≠ third)
    (secondThirdDistinct : second ≠ third)
    (notCollinear : ¬ Incidence.Collinear first second third)
    (twoNonzero : (2 : K) ≠ 0)
    (firstThirdNull :
      (Incidence.lineThrough first third firstThirdDistinct).IsNull)
    (secondThirdNull :
      (Incidence.lineThrough second third secondThirdDistinct).IsNull) :
    Circumcenter.Basic.circumcenterPoint first second third firstThirdDistinct
      secondThirdDistinct notCollinear = third := by
  let center := Circumcenter.Basic.circumcenterPoint first second third firstThirdDistinct
    secondThirdDistinct notCollinear
  have centerData := Circumcenter.Basic.circumcenter first second third firstSecondDistinct
    firstThirdDistinct secondThirdDistinct notCollinear twoNonzero
  have firstThirdQuadranceZero :=
    (Quadrance.null_line_iff_quadrance_zero first third firstThirdDistinct).1
      firstThirdNull
  have secondThirdQuadranceZero :=
    (Quadrance.null_line_iff_quadrance_zero second third secondThirdDistinct).1
      secondThirdNull
  have equalFirstThird : Quadrance.quadrance center first = Quadrance.quadrance center third :=
    centerData.2.2.2.1.trans centerData.2.2.2.2
  have firstCollinear : Incidence.Collinear first third center :=
    equal_quadrance_center_collinear_of_null first third center twoNonzero
      firstThirdQuadranceZero equalFirstThird
  have secondCollinear : Incidence.Collinear second third center :=
    equal_quadrance_center_collinear_of_null second third center twoNonzero
      secondThirdQuadranceZero centerData.2.2.2.2
  have firstDeterminantZero : Incidence.pointDeterminant first third center = 0 :=
    (Incidence.collinear_iff_pointDeterminant_eq_zero first third center).1
      firstCollinear
  have secondDeterminantZero : Incidence.pointDeterminant second third center = 0 :=
    (Incidence.collinear_iff_pointDeterminant_eq_zero second third center).1
      secondCollinear
  have triangleDeterminantNonzero :
      Incidence.pointDeterminant first second third ≠ 0 := by
    intro determinantZero
    apply notCollinear
    exact (Incidence.collinear_iff_pointDeterminant_eq_zero first second third).2
      determinantZero
  have xProductZero :
      Incidence.pointDeterminant first second third * (center.x - third.x) = 0 := by
    calc
      Incidence.pointDeterminant first second third * (center.x - third.x) =
          (first.x - third.x) *
              Incidence.pointDeterminant second third center -
            (second.x - third.x) *
              Incidence.pointDeterminant first third center := by
        unfold Incidence.pointDeterminant
        ring1
      _ = 0 := by
        rw [firstDeterminantZero, secondDeterminantZero]
        ring1
  have yProductZero :
      Incidence.pointDeterminant first second third * (center.y - third.y) = 0 := by
    calc
      Incidence.pointDeterminant first second third * (center.y - third.y) =
          (first.y - third.y) *
              Incidence.pointDeterminant second third center -
            (second.y - third.y) *
              Incidence.pointDeterminant first third center := by
        unfold Incidence.pointDeterminant
        ring1
      _ = 0 := by
        rw [firstDeterminantZero, secondDeterminantZero]
        ring1
  have xDifferenceZero : center.x - third.x = 0 := by
    by_cases zero : center.x - third.x = 0
    · exact zero
    · exact False.elim
        ((ExplicitField.mul_ne_zero triangleDeterminantNonzero zero)
          xProductZero)
  have yDifferenceZero : center.y - third.y = 0 := by
    by_cases zero : center.y - third.y = 0
    · exact zero
    · exact False.elim
        ((ExplicitField.mul_ne_zero triangleDeterminantNonzero zero)
          yProductZero)
  apply Geometry.Plane.Point.ext
  · exact Group.eq_of_sub_eq_zero xDifferenceZero
  · exact Group.eq_of_sub_eq_zero yDifferenceZero
end Purelib.Geometry.Triangles.Circumcenter.NullSides

end

end
