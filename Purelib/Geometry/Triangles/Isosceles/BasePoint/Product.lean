module
public import Purelib.Algebra.Group.Basic
public import Purelib.Data.Nat.Order
public import Purelib.Algebra.Group.Negation
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Geometry.Plane.Line.Incidence
import Purelib.Geometry.Plane.Point.Affine
import Purelib.Geometry.Plane.Point.Affine.Quadrance
import Purelib.Geometry.Plane.Point.Basic
public import Purelib.Geometry.Plane.Point.Quadrance
import Purelib.Geometry.Triangles.Median.Quadrance
import Purelib.Geometry.Triangles.Stewart
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
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

open Purelib.Geometry.Plane.Point.Affine

open Purelib.Geometry.Triangles

section
public section

/-!
# Divine Proportions, Chapter 11 exercises

This module begins the reader problems following the Two-struts theorem.  All
normalizations are retained as finite polynomial equalities.  In particular,
Example 11.1 is checked by scaling the two quad triples by the displayed
factor `256`; no quadratic formula or selected root is used.
-/

namespace Purelib.Geometry.Triangles.Isosceles.BasePoint.Product

variable {K : Type*} [ExplicitField K]

/-- Exercise 11.5, strengthened to the exact geometric hypotheses used by the proof. A point on the non-null base of an
isosceles triangle satisfies the printed product identity. -/
theorem exercise_11_5 [DecidableEq K]
    (first second vertex point : Geometry.Plane.Point K)
    (firstSecondDistinct : first ≠ second)
    (twoNonzero : (2 : K) ≠ 0)
    (baseNonNull :
      ¬ (Incidence.lineThrough first second firstSecondDistinct).IsNull)
    (pointOnBase :
      (Incidence.lineThrough first second firstSecondDistinct).Contains point)
    (equalLegs :
      Quadrance.quadrance first vertex = Quadrance.quadrance second vertex) :
    (Quadrance.quadrance first vertex - Quadrance.quadrance vertex point) ^ 2 =
      Quadrance.quadrance first point * Quadrance.quadrance second point := by
  let firstPart := Quadrance.quadrance first point
  let secondPart := Quadrance.quadrance second point
  let vertexPart := Quadrance.quadrance vertex point
  let commonLeg := Quadrance.quadrance first vertex
  have stewartIdentity := Stewart.stewart first second vertex point
    firstSecondDistinct pointOnBase
  rw [← equalLegs] at stewartIdentity
  have stewartFactored :
      (firstPart - secondPart) *
        (firstPart * secondPart - (commonLeg - vertexPart) ^ 2) = 0 := by
    calc
      (firstPart - secondPart) *
          (firstPart * secondPart - (commonLeg - vertexPart) ^ 2) =
        secondPart * (vertexPart + firstPart - commonLeg) ^ 2 -
          firstPart * (vertexPart + secondPart - commonLeg) ^ 2 := by
        unfold firstPart secondPart vertexPart commonLeg
        ring1
      _ = 0 := by
        rw [stewartIdentity]
        ring1
  by_cases unequalParts : firstPart = secondPart
  · have equalEndpointQuadrances :
        Quadrance.quadrance point first = Quadrance.quadrance point second := by
      calc
        Quadrance.quadrance point first = firstPart :=
          Quadrance.quadrance_symm point first
        _ = secondPart := unequalParts
        _ = Quadrance.quadrance point second :=
          (Quadrance.quadrance_symm point second).symm
    have pointIsMidpoint : point = Affine.midpoint first second :=
      Quadrance.midpoint_unique_of_equal_quadrance first second point
        firstSecondDistinct twoNonzero baseNonNull pointOnBase
        equalEndpointQuadrances
    have fourNonzero : (4 : K) ≠ 0 := by
      rw [show (4 : K) = 2 * 2 by ring1]
      exact ExplicitField.mul_ne_zero twoNonzero twoNonzero
    have endpointCleared : firstPart * 4 = Quadrance.quadrance first second := by
      calc
        firstPart * 4 =
            Quadrance.quadrance (Affine.midpoint first second) first * 4 := by
          unfold firstPart
          rw [pointIsMidpoint, Quadrance.quadrance_symm first (Affine.midpoint first second)]
        _ = (Quadrance.quadrance first second / 4) * 4 := by
          rw [Quadrance.midpoint_quadrance first second twoNonzero]
        _ = Quadrance.quadrance first second :=
          ExplicitField.div_mul_cancel _ fourNonzero
    have vertexCleared :
        vertexPart * 4 =
          2 * commonLeg + 2 * commonLeg - Quadrance.quadrance first second := by
      calc
        vertexPart * 4 =
            Quadrance.quadrance (Affine.midpoint first second) vertex * 4 := by
          unfold vertexPart
          rw [pointIsMidpoint,
            Quadrance.quadrance_symm vertex (Affine.midpoint first second)]
        _ = 2 * Quadrance.quadrance first vertex +
            2 * Quadrance.quadrance second vertex - Quadrance.quadrance first second :=
          Median.Quadrance.median_quadrance_cleared first second vertex twoNonzero
        _ = 2 * commonLeg + 2 * commonLeg - Quadrance.quadrance first second := by
          unfold commonLeg
          rw [← equalLegs]
    have legDifference : commonLeg - vertexPart = firstPart := by
      apply ExplicitField.eq_of_mul_eq_mul_right fourNonzero
      calc
        (commonLeg - vertexPart) * 4 =
            4 * commonLeg - vertexPart * 4 := by ring1
        _ = Quadrance.quadrance first second := by
          rw [vertexCleared]
          ring1
        _ = firstPart * 4 := endpointCleared.symm
    change (commonLeg - vertexPart) ^ 2 = firstPart * secondPart
    rw [legDifference, ← unequalParts, pow_two]
  · have secondFactorZero :
        firstPart * secondPart - (commonLeg - vertexPart) ^ 2 = 0 := by
      by_cases zero :
          firstPart * secondPart - (commonLeg - vertexPart) ^ 2 = 0
      · exact zero
      · exact False.elim
          ((ExplicitField.mul_ne_zero
              (by intro differenceZero; exact unequalParts (Group.eq_of_sub_eq_zero differenceZero)) zero)
            stewartFactored)
    change (commonLeg - vertexPart) ^ 2 = firstPart * secondPart
    exact (Group.eq_of_sub_eq_zero secondFactorZero).symm
end Purelib.Geometry.Triangles.Isosceles.BasePoint.Product

end

end
