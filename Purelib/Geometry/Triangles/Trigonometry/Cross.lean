module
public import Purelib.Data.Nat.Order
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Geometry.Plane.Line.Cross
import Purelib.Geometry.Plane.Line.Incidence
import Purelib.Geometry.Plane.Line.Quadrance
import Purelib.Geometry.Plane.Point.Basic
import Purelib.Geometry.Plane.Point.Quadrance
import Mathlib.Algebra.Group.Defs
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

section
@[expose] public section

/-!
# Divine Proportions, §§6.4–6.7: triangle ratio theorems

The book's quotient identities are retained exactly.  Every cancellation is
backed by a displayed non-null side or a characteristic hypothesis.
-/

namespace Purelib.Geometry.Triangles.Trigonometry.Cross

variable {K : Type*} [ExplicitField K]

/-- The cross law expresses the squared quadrance difference using the cross of two sides.

Both incident sides are displayed by distinct endpoints and are non-null, making their normalized cross well-defined. -/
theorem cross_law [DecidableEq K]
    (first second third : Plane.Point K)
    (firstDistinct : first ≠ third) (secondDistinct : second ≠ third)
    (firstNonNull : ¬ (Incidence.lineThrough first third firstDistinct).IsNull)
    (secondNonNull : ¬ (Incidence.lineThrough second third secondDistinct).IsNull) :
    (Quadrance.quadrance second third + Quadrance.quadrance first third -
        Quadrance.quadrance first second) ^ 2 =
      4 * Quadrance.quadrance second third * Quadrance.quadrance first third *
        Cross.cross (Incidence.lineThrough first third firstDistinct)
          (Incidence.lineThrough second third secondDistinct)
          firstNonNull secondNonNull := by
  let dot :=
    (first.y - third.y) * (second.y - third.y) +
      (third.x - first.x) * (third.x - second.x)
  have sideOneNonzero := Trigonometry.TriangleRatios.quadrance_ne_zero_of_line_nonNull
    second third secondDistinct secondNonNull
  have sideTwoNonzero := Trigonometry.TriangleRatios.quadrance_ne_zero_of_line_nonNull
    first third firstDistinct firstNonNull
  have denominatorNonzero :
      Quadrance.quadrance first third * Quadrance.quadrance second third ≠ 0 :=
    ExplicitField.mul_ne_zero sideTwoNonzero sideOneNonzero
  have denominatorCancel :
      (Quadrance.quadrance first third * Quadrance.quadrance second third) *
        (Quadrance.quadrance first third * Quadrance.quadrance second third)⁻¹ = (1 : K) :=
    ExplicitField.mul_inv_cancel _ denominatorNonzero
  have metricIdentity :
      Quadrance.quadrance second third + Quadrance.quadrance first third -
          Quadrance.quadrance first second = 2 * dot := by
    unfold Quadrance.quadrance dot
    ring1
  rw [Cross.cross_from_points first second third firstDistinct secondDistinct
    firstNonNull secondNonNull]
  simp only [ExplicitField.div_eq_mul_inv]
  rw [metricIdentity]
  calc
    (2 * dot) ^ 2 = 4 * dot ^ 2 := by ring1
    _ = 4 * Quadrance.quadrance second third * Quadrance.quadrance first third *
        (dot ^ 2 *
          (Quadrance.quadrance first third * Quadrance.quadrance second third)⁻¹) := by
            calc
              4 * dot ^ 2 = 4 * dot ^ 2 * 1 := by ring1
              _ = 4 * dot ^ 2 *
                  ((Quadrance.quadrance first third * Quadrance.quadrance second third) *
                    (Quadrance.quadrance first third * Quadrance.quadrance second third)⁻¹) := by
                      rw [denominatorCancel]
              _ = 4 * Quadrance.quadrance second third * Quadrance.quadrance first third *
                  (dot ^ 2 *
                    (Quadrance.quadrance first third * Quadrance.quadrance second third)⁻¹) := by
                      ring1
end Purelib.Geometry.Triangles.Trigonometry.Cross

end
