module
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

namespace Purelib.Geometry.Quadrilaterals.Rhombus

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- The metric part of the source's definition of a rhombus: the two diagonals of the displayed parallelogram are
perpendicular. -/
def HasPerpendicularDiagonals
    (first second third fourth : Plane.Point K) : Prop :=
  Dot.segmentDirectionDot first third second fourth = 0

/-- The source's definition of a rhombus: a parallelogram whose two diagonals are perpendicular. -/
def IsRhombus
    (first second third fourth : Plane.Point K) : Prop :=
  Parallelogram.Basic.ParallelogramSideConditions first second third fourth ∧
    HasPerpendicularDiagonals first second third fourth

/-- Exercise 5.6: all four side quadrances of a parallelogram are equal precisely when its diagonals are perpendicular,
hence precisely when it is a rhombus. -/
theorem exercise_5_6 [DecidableEq K]
    (first second third fourth : Plane.Point K)
    (twoNonzero : (2 : K) ≠ 0)
    (determinantNonzero : Incidence.pointDeterminant first second third ≠ 0)
    (parallelSides : Parallelogram.Basic.ParallelogramSideConditions first second third fourth) :
    (Quadrance.quadrance first second = Quadrance.quadrance second third ∧
      Quadrance.quadrance second third = Quadrance.quadrance third fourth ∧
      Quadrance.quadrance third fourth = Quadrance.quadrance fourth first) ↔
      IsRhombus first second third fourth := by
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
  constructor
  · intro allSidesEqual
    refine ⟨parallelSides, ?_⟩
    unfold HasPerpendicularDiagonals Dot.segmentDirectionDot
    unfold Quadrance.quadrance at allSidesEqual
    rw [fourthX, fourthY] at allSidesEqual ⊢
    calc
      (third.x - first.x) *
            (first.x - second.x + third.x - second.x) +
          (third.y - first.y) *
            (first.y - second.y + third.y - second.y) =
        ((third.x - second.x) ^ 2 +
            (third.y - second.y) ^ 2) -
          ((second.x - first.x) ^ 2 +
            (second.y - first.y) ^ 2) := by ring1
      _ = 0 := by rw [← allSidesEqual.1]; ring1
  · intro rhombus
    have diagonalsPerpendicular := rhombus.2
    unfold HasPerpendicularDiagonals Dot.segmentDirectionDot at diagonalsPerpendicular
    unfold Quadrance.quadrance
    rw [fourthX, fourthY] at diagonalsPerpendicular ⊢
    have adjacentEqual :
        (second.x - first.x) ^ 2 + (second.y - first.y) ^ 2 =
          (third.x - second.x) ^ 2 + (third.y - second.y) ^ 2 := by
      calc
        (second.x - first.x) ^ 2 + (second.y - first.y) ^ 2 =
            (third.x - second.x) ^ 2 + (third.y - second.y) ^ 2 -
              ((third.x - first.x) *
                  (first.x - second.x + third.x - second.x) +
                (third.y - first.y) *
                  (first.y - second.y + third.y - second.y)) := by ring1
        _ = (third.x - second.x) ^ 2 +
            (third.y - second.y) ^ 2 := by
              rw [diagonalsPerpendicular]
              ring1
    refine ⟨adjacentEqual, ?_, ?_⟩
    · calc
        (third.x - second.x) ^ 2 + (third.y - second.y) ^ 2 =
            (second.x - first.x) ^ 2 +
              (second.y - first.y) ^ 2 := adjacentEqual.symm
        _ = (first.x - second.x + third.x - third.x) ^ 2 +
            (first.y - second.y + third.y - third.y) ^ 2 := by ring1
    · calc
        (first.x - second.x + third.x - third.x) ^ 2 +
              (first.y - second.y + third.y - third.y) ^ 2 =
            (second.x - first.x) ^ 2 +
              (second.y - first.y) ^ 2 := by ring1
        _ = (third.x - second.x) ^ 2 +
            (third.y - second.y) ^ 2 := adjacentEqual
        _ = (first.x - (first.x - second.x + third.x)) ^ 2 +
            (first.y - (first.y - second.y + third.y)) ^ 2 := by ring1

end Purelib.Geometry.Quadrilaterals.Rhombus

end
