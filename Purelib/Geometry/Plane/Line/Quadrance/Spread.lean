module
-- Retained public numeral and subtraction parents use their original operations.
public import Purelib.Data.Nat.Order
public import Purelib.Algebra.Group.Negation
import Purelib.Algebra.Field.Cancellation
import Purelib.Algebra.Field.ExplicitField
import Purelib.Geometry.Plane.Line.Basic
import Purelib.Geometry.Plane.Line.Incidence
public import Purelib.Geometry.Plane.Line.Quadrance
public import Purelib.Geometry.Plane.Line.Spread
import Purelib.Geometry.Plane.Point.Basic
import Purelib.Geometry.Plane.Point.Quadrance
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Purelib.Tactic.Ring

section
open Purelib
open Purelib.Geometry
open Purelib.Geometry.Plane
open Purelib.Geometry.Plane.Line
open Purelib.Geometry.Plane.Point

open scoped Purelib.Data.Nat
attribute [local instance 2000] Purelib.Data.Nat.successorNeZero
  Purelib.Data.Nat.successorAtLeastTwo
  Purelib.Algebra.Group.Negation.subNegZeroMonoid

section
public section

/-!
# Divine Proportions, Theorem 98: polygon corner triangles

The source construction uses only three successive polygon vertices and the
three finite reflections relating them.  `PolygonTriangleConfiguration`
stores precisely that finite window; no polygon indexed by all integers is
introduced.
-/

section

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

namespace Purelib.Geometry.Plane.Line.Quadrance.Spread

/-- The perpendicular quadrance from `point` to a mirror through `center` is the radial quadrance multiplied by the
spread between the radius and mirror. This is the geometric ratio used in the source proof of Isosceles reflection. -/
theorem pointLineQuadrance_eq_spread_mul_quadrance [DecidableEq K]
    (center point : Point K) (distinct : center ≠ point)
    (radialNonNull : ¬ (Incidence.lineThrough center point distinct).IsNull)
    (mirror : Line K) (mirrorNonNull : ¬ mirror.IsNull)
    (centerOnMirror : mirror.Contains center) :
    Quadrance.pointLineQuadrance point mirror mirrorNonNull =
      Spread.spread (Incidence.lineThrough center point distinct) mirror
          radialNonNull mirrorNonNull * Quadrance.quadrance center point := by
  have radialQuadranceNonzero : Quadrance.quadrance center point ≠ 0 := by
    rw [← Quadrance.lineThrough_norm_eq_quadrance center point distinct]
    exact radialNonNull
  have mirrorNormNonzero : Line.Basic.lineNorm mirror ≠ 0 := mirrorNonNull
  have denominatorNonzero :
      Quadrance.quadrance center point * Line.Basic.lineNorm mirror ≠ 0 :=
    Algebra.Field.ExplicitField.mul_ne_zero radialQuadranceNonzero mirrorNormNonzero
  have determinantNegated :
      (Incidence.lineThrough center point distinct).a * mirror.b -
          mirror.a * (Incidence.lineThrough center point distinct).b =
        -(mirror.a * point.x + mirror.b * point.y + mirror.c) := by
    unfold Contains at centerOnMirror
    simp only [Incidence.lineThrough_a, Incidence.lineThrough_b]
    calc
      (center.y - point.y) * mirror.b -
          mirror.a * (point.x - center.x) =
        (mirror.a * center.x + mirror.b * center.y + mirror.c) -
          (mirror.a * point.x + mirror.b * point.y + mirror.c) := by ring1
      _ = -(mirror.a * point.x + mirror.b * point.y + mirror.c) := by
        rw [centerOnMirror]
        ring1
  have determinantSquare :
      ((Incidence.lineThrough center point distinct).a * mirror.b -
          mirror.a * (Incidence.lineThrough center point distinct).b) ^ 2 =
        (mirror.a * point.x + mirror.b * point.y + mirror.c) ^ 2 := by
    rw [determinantNegated]
    ring1
  rw [Quadrance.pointLineQuadrance_formula]
  unfold Spread.spread
  rw [Quadrance.lineThrough_norm_eq_quadrance center point distinct,
    determinantSquare]
  apply Algebra.Field.ExplicitField.eq_of_mul_eq_mul_right mirrorNormNonzero
  calc
    ((mirror.a * point.x + mirror.b * point.y + mirror.c) ^ 2 /
          Line.Basic.lineNorm mirror) * Line.Basic.lineNorm mirror =
        (mirror.a * point.x + mirror.b * point.y + mirror.c) ^ 2 :=
      Algebra.Field.ExplicitField.div_mul_cancel _ mirrorNormNonzero
    _ = ((mirror.a * point.x + mirror.b * point.y + mirror.c) ^ 2 /
          (Quadrance.quadrance center point * Line.Basic.lineNorm mirror)) *
            (Quadrance.quadrance center point * Line.Basic.lineNorm mirror) :=
      (Algebra.Field.ExplicitField.div_mul_cancel _ denominatorNonzero).symm
    _ = ((mirror.a * point.x + mirror.b * point.y + mirror.c) ^ 2 /
          (Quadrance.quadrance center point * Line.Basic.lineNorm mirror) *
            Quadrance.quadrance center point) * Line.Basic.lineNorm mirror := by ring1

end Purelib.Geometry.Plane.Line.Quadrance.Spread

end

end

end
