module
import Purelib.Algebra.Field.ExplicitField
import Purelib.Geometry.Plane.Line.Incidence
import Purelib.Geometry.Plane.Point.Basic
public import Purelib.Geometry.Plane.Point.Quadrance
public import Purelib.Geometry.Quadrilaterals.Parallelogram.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Tactic.Ring

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

namespace Purelib.Geometry.Quadrilaterals.Parallelogram.Quadrance

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- A nondegenerate parallelogram's diagonal quadrance sum is twice the sum of adjacent side quadrances.

The parallel-side certificates and nonzero two identify the opposite coordinate sums. -/
theorem exercise_5_5 [DecidableEq K]
    (first second third fourth : Plane.Point K)
    (twoNonzero : (2 : K) ≠ 0)
    (determinantNonzero : Incidence.pointDeterminant first second third ≠ 0)
    (parallelSides : Parallelogram.Basic.ParallelogramSideConditions first second third fourth) :
    Quadrance.quadrance first third + Quadrance.quadrance second fourth =
      2 * (Quadrance.quadrance first second + Quadrance.quadrance second third) := by
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
  unfold Quadrance.quadrance
  rw [fourthX, fourthY]
  ring1
end Purelib.Geometry.Quadrilaterals.Parallelogram.Quadrance

end

@[expose] public section

/-!
# Divine Proportions, Chapter 5: quadrance

Quadrance is a polynomial, so its basic geometry works uniformly over the
constructive rationals and finite fields.  The few exclusions below are
stated explicitly: midpoint and Triple-quad arguments require `2 ≠ 0`.
-/

namespace Purelib.Geometry.Quadrilaterals.Parallelogram.Quadrance

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- Theorem 21 (Parallelogram quadrance): opposite sides of a nondegenerate parallelogram have equal quadrance. -/
theorem parallelogram_quadrance [DecidableEq K]
    (first second third fourth : Plane.Point K)
    (twoNonzero : (2 : K) ≠ 0)
    (determinantNonzero : Incidence.pointDeterminant first second third ≠ 0)
    (parallelSides : Parallelogram.Basic.ParallelogramSideConditions first second third fourth) :
    Quadrance.quadrance first second = Quadrance.quadrance third fourth ∧
      Quadrance.quadrance second third = Quadrance.quadrance fourth first := by
  rcases Parallelogram.Basic.parallelogram_coordinate_sums first second third fourth
    twoNonzero determinantNonzero parallelSides
      with ⟨xSums, ySums⟩
  constructor
  · unfold Quadrance.quadrance
    calc
      (second.x - first.x) ^ 2 + (second.y - first.y) ^ 2 =
          (fourth.x - third.x) ^ 2 + (fourth.y - third.y) ^ 2 := by
            rw [show second.x - first.x = third.x - fourth.x by
              calc
                second.x - first.x = third.x - fourth.x +
                    ((second.x + fourth.x) - (first.x + third.x)) := by ring1
                _ = third.x - fourth.x := by rw [← xSums]; ring1]
            rw [show second.y - first.y = third.y - fourth.y by
              calc
                second.y - first.y = third.y - fourth.y +
                    ((second.y + fourth.y) - (first.y + third.y)) := by ring1
                _ = third.y - fourth.y := by rw [← ySums]; ring1]
            ring1
      _ = (fourth.x - third.x) ^ 2 + (fourth.y - third.y) ^ 2 := rfl
  · unfold Quadrance.quadrance
    rw [show third.x - second.x = fourth.x - first.x by
      calc
        third.x - second.x = fourth.x - first.x +
            ((first.x + third.x) - (second.x + fourth.x)) := by ring1
        _ = fourth.x - first.x := by rw [xSums]; ring1]
    rw [show third.y - second.y = fourth.y - first.y by
      calc
        third.y - second.y = fourth.y - first.y +
            ((first.y + third.y) - (second.y + fourth.y)) := by ring1
        _ = fourth.y - first.y := by rw [ySums]; ring1]
    ring1
end Purelib.Geometry.Quadrilaterals.Parallelogram.Quadrance

end
