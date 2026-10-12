module

import Purelib.Algebra.Field.Characteristic.Nonzero
import Purelib.Algebra.Field.Cancellation
import Purelib.Algebra.Field.ExplicitField
import Purelib.Geometry.Plane.Line.Incidence
import Purelib.Geometry.Plane.Point.Basic
public import Purelib.Geometry.Plane.Point.Dot
import Purelib.Geometry.Plane.Point.Quadrance
public import Purelib.Geometry.Quadrilaterals.Parallelogram.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra.Field

open Purelib.Geometry

open Purelib.Geometry.Plane.Line

open Purelib.Geometry.Plane.Point

open Purelib.Geometry.Quadrilaterals

@[expose] public section

/-!
# Divine Proportions, Chapter 5 parallelogram exercises

The source's rectangle and rhombus conditions are retained as four finite
adjacent-side dot products and one finite diagonal dot product.  Their
connection with perpendicular displayed lines is proved without quotienting
line representatives.  Exercises 5.4--5.6 then follow from the coordinate-sum
form of the Parallelogram center theorem.
-/

namespace Purelib.Geometry.Quadrilaterals.Rectangle

variable {K : Type*} [ExplicitField K]

/-- Each pair of adjacent side directions has zero dot product.

This polynomial predicate does not itself require distinct vertices or nondegeneracy. -/
def IsRectangle
    (first second third fourth : Plane.Point K) : Prop :=
  Dot.segmentDirectionDot first second second third = 0 ∧
    Dot.segmentDirectionDot second third third fourth = 0 ∧
    Dot.segmentDirectionDot third fourth fourth first = 0 ∧
    Dot.segmentDirectionDot fourth first first second = 0

/-- A nondegenerate parallelogram has equal diagonal quadrances exactly when it is a rectangle.

The characteristic is not two and the first three vertices have nonzero determinant. -/
theorem exercise_5_4 [DecidableEq K]
    (first second third fourth : Plane.Point K)
    (twoNonzero : (2 : K) ≠ 0)
    (determinantNonzero : Incidence.pointDeterminant first second third ≠ 0)
    (parallelSides : Parallelogram.Basic.ParallelogramSideConditions first second third fourth) :
    Quadrance.quadrance first third = Quadrance.quadrance second fourth ↔
      IsRectangle first second third fourth := by
  rcases Parallelogram.Basic.parallelogram_coordinate_sums first second third fourth
      twoNonzero determinantNonzero parallelSides with ⟨xSums, ySums⟩
  have fourthX : fourth.x = first.x - second.x + third.x := by
    calc
      fourth.x = first.x + third.x - second.x := by
        rw [xSums]
        ring1
      _ = first.x - second.x + third.x := by ring1
  have fourthY : fourth.y = first.y - second.y + third.y := by
    calc
      fourth.y = first.y + third.y - second.y := by
        rw [ySums]
        ring1
      _ = first.y - second.y + third.y := by ring1
  let adjacentDot := Dot.segmentDirectionDot first second second third
  have diagonalDifference :
      Quadrance.quadrance first third - Quadrance.quadrance second fourth =
        4 * adjacentDot := by
    unfold adjacentDot Dot.segmentDirectionDot Quadrance.quadrance
    rw [fourthX, fourthY]
    ring1
  have rectangleIff :
      IsRectangle first second third fourth ↔ adjacentDot = 0 := by
    unfold IsRectangle adjacentDot Dot.segmentDirectionDot
    rw [fourthX, fourthY]
    constructor
    · intro rectangle
      exact rectangle.1
    · intro dotZero
      refine ⟨dotZero, ?_, ?_, ?_⟩
      · calc
          (third.x - second.x) *
                (first.x - second.x + third.x - third.x) +
              (third.y - second.y) *
                (first.y - second.y + third.y - third.y) =
            -((second.x - first.x) * (third.x - second.x) +
              (second.y - first.y) * (third.y - second.y)) := by ring1
          _ = 0 := by rw [dotZero]; ring1
      · calc
          (first.x - second.x + third.x - third.x) *
                (first.x - (first.x - second.x + third.x)) +
              (first.y - second.y + third.y - third.y) *
                (first.y - (first.y - second.y + third.y)) =
            (second.x - first.x) * (third.x - second.x) +
              (second.y - first.y) * (third.y - second.y) := by ring1
          _ = 0 := dotZero
      · calc
          (first.x - (first.x - second.x + third.x)) *
                (second.x - first.x) +
              (first.y - (first.y - second.y + third.y)) *
                (second.y - first.y) =
            -((second.x - first.x) * (third.x - second.x) +
              (second.y - first.y) * (third.y - second.y)) := by ring1
          _ = 0 := by rw [dotZero]; ring1
  refine Iff.trans ?_ rectangleIff.symm
  constructor
  · intro diagonalsEqual
    have productZero : (4 : K) * adjacentDot = 0 := by
      rw [← diagonalDifference, diagonalsEqual]
      ring1
    by_cases dotZero : adjacentDot = 0
    · exact dotZero
    · exact False.elim
        ((ExplicitField.mul_ne_zero
          ((fun {K : Type _} [ExplicitField K] [DecidableEq K] (twoNonzero : (2 : K) ≠ 0) =>
            (Purelib.Algebra.Field.Characteristic.Nonzero.four_ne_zero (K := K) twoNonzero : (4 : K) ≠ 0)) twoNonzero)
            dotZero) productZero)
  · intro dotZero
    calc
      Quadrance.quadrance first third =
          (Quadrance.quadrance first third - Quadrance.quadrance second fourth) +
            Quadrance.quadrance second fourth := by ring1
      _ = Quadrance.quadrance second fourth := by
        rw [diagonalDifference, dotZero]
        ring1
end Purelib.Geometry.Quadrilaterals.Rectangle

end
