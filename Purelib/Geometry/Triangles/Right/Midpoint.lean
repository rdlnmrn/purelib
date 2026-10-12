module
import Purelib.Algebra.Field.Cancellation
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Geometry.Plane.Line.Incidence
public import Purelib.Geometry.Plane.Point.Affine
import Purelib.Geometry.Plane.Point.Affine.Quadrance
import Purelib.Geometry.Plane.Point.Basic
public import Purelib.Geometry.Plane.Point.Quadrance
import Purelib.Geometry.Triangles.Median.Quadrance
import Purelib.Geometry.Triangles.Right.Quadrance
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Geometry.Plane.Line.Basic
import Purelib.Tactic.Ring

open Purelib.Algebra.Field (ExplicitField)

open Purelib

open Purelib.Geometry

open Purelib.Geometry.Plane.Line

open Purelib.Geometry.Plane.Point

open Purelib.Geometry.Plane.Point.Affine

open Purelib.Geometry.Triangles

section
@[expose] public section

/-!
# Divine Proportions, Chapter 10: right triangles

The midpoint characterization is proved after clearing the finite factor
four.  The intermediate median-quadrance identity is useful again for the
later Median quadrance theorem.
-/

namespace Purelib.Geometry.Triangles.Right.Midpoint

variable {K : Type*} [ExplicitField K]

/-- Theorem 70 (Right midpoint): the midpoint of `A₁A₂` is equidistant from `A₁` and `A₃` exactly when the vertex at
`A₃` is right. -/
theorem right_midpoint [DecidableEq K]
    (first second third : Plane.Point K)
    (firstThirdDistinct : first ≠ third)
    (secondThirdDistinct : second ≠ third)
    (twoNonzero : (2 : K) ≠ 0) :
    Quadrance.quadrance (Affine.midpoint first second) first =
        Quadrance.quadrance (Affine.midpoint first second) third ↔
      (Incidence.lineThrough first third firstThirdDistinct).Perpendicular
        (Incidence.lineThrough second third secondThirdDistinct) := by
  have fourNonzero : (4 : K) ≠ 0 := by
    have squareNonzero := ExplicitField.mul_ne_zero twoNonzero twoNonzero
    simpa only [show (4 : K) = 2 * 2 by ring1] using squareNonzero
  have endpointCleared :
      Quadrance.quadrance (Affine.midpoint first second) first * 4 =
        Quadrance.quadrance first second := by
    rw [Quadrance.midpoint_quadrance first second twoNonzero]
    exact ExplicitField.div_mul_cancel _ fourNonzero
  have thirdCleared := Median.Quadrance.median_quadrance_cleared first second third twoNonzero
  constructor
  · intro equalMidpointQuadrances
    have clearedEqual :
        Quadrance.quadrance first second =
          2 * Quadrance.quadrance first third + 2 * Quadrance.quadrance second third -
            Quadrance.quadrance first second := by
      calc
        Quadrance.quadrance first second =
            Quadrance.quadrance (Affine.midpoint first second) first * 4 :=
          endpointCleared.symm
        _ = Quadrance.quadrance (Affine.midpoint first second) third * 4 := by
          rw [equalMidpointQuadrances]
        _ = 2 * Quadrance.quadrance first third + 2 * Quadrance.quadrance second third -
            Quadrance.quadrance first second := thirdCleared
    have pythagoras :
        Quadrance.quadrance second third + Quadrance.quadrance first third =
          Quadrance.quadrance first second := by
      apply ExplicitField.eq_of_mul_eq_mul_left twoNonzero
      calc
        2 * (Quadrance.quadrance second third + Quadrance.quadrance first third) =
            (2 * Quadrance.quadrance first third + 2 * Quadrance.quadrance second third -
              Quadrance.quadrance first second) + Quadrance.quadrance first second := by ring1
        _ = Quadrance.quadrance first second + Quadrance.quadrance first second := by
          rw [← clearedEqual]
        _ = 2 * Quadrance.quadrance first second := by ring1
    exact (Right.Quadrance.pythagoras_iff_perpendicular first second third
      firstThirdDistinct secondThirdDistinct twoNonzero).1 pythagoras
  · intro perpendicular
    have pythagoras :=
      (Right.Quadrance.pythagoras_iff_perpendicular first second third
        firstThirdDistinct secondThirdDistinct twoNonzero).2 perpendicular
    apply ExplicitField.eq_of_mul_eq_mul_right fourNonzero
    calc
      Quadrance.quadrance (Affine.midpoint first second) first * 4 =
          Quadrance.quadrance first second := endpointCleared
      _ = 2 * Quadrance.quadrance first third + 2 * Quadrance.quadrance second third -
          Quadrance.quadrance first second := by rw [← pythagoras]; ring1
      _ = Quadrance.quadrance (Affine.midpoint first second) third * 4 := thirdCleared.symm

end Purelib.Geometry.Triangles.Right.Midpoint

end
