module
import Purelib.Algebra.Field.ExplicitField
import Purelib.Geometry.Plane.Line.Basic
public import Purelib.Geometry.Plane.Line.Incidence
import Purelib.Geometry.Plane.Line.Quadrance
import Purelib.Geometry.Plane.Point.Basic
public import Purelib.Geometry.Plane.Point.Quadrance
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Purelib.Tactic.Ring

open Purelib

open Purelib.Geometry

open Purelib.Geometry.Plane

open Purelib.Geometry.Plane.Line

open Purelib.Geometry.Plane.Point

section
@[expose] public section

/-!
# Divine Proportions, Chapter 6: spread, cross, and twist

The ratio notions carry explicit non-null/non-perpendicular certificates for
their denominators.  They are otherwise ordinary finite field expressions.
-/

namespace Purelib.Geometry.Plane.Line.Cross

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- Cross between two displayed non-null lines. -/
def cross (first second : Plane.Line K)
    (_firstNonNull : ¬ first.IsNull) (_secondNonNull : ¬ second.IsNull) : K :=
  (first.a * second.a + first.b * second.b) ^ 2 /
    (Line.Basic.lineNorm first * Line.Basic.lineNorm second)

/-- Cross is symmetric in its two lines. -/
theorem cross_symm (first second : Plane.Line K)
    (firstNonNull : ¬ first.IsNull) (secondNonNull : ¬ second.IsNull) :
    cross first second firstNonNull secondNonNull =
      cross second first secondNonNull firstNonNull := by
  unfold cross
  congr 1 <;> ring1

/-- Theorem 44 (Cross from points), in coordinate form. -/
theorem cross_from_points [DecidableEq K]
    (first second vertex : Plane.Point K)
    (firstDistinct : first ≠ vertex) (secondDistinct : second ≠ vertex)
    (firstNonNull : ¬ (Incidence.lineThrough first vertex firstDistinct).IsNull)
    (secondNonNull : ¬ (Incidence.lineThrough second vertex secondDistinct).IsNull) :
    cross (Incidence.lineThrough first vertex firstDistinct)
        (Incidence.lineThrough second vertex secondDistinct) firstNonNull secondNonNull =
      (((first.y - vertex.y) * (second.y - vertex.y) +
        (vertex.x - first.x) * (vertex.x - second.x)) ^ 2) /
        (Quadrance.quadrance first vertex * Quadrance.quadrance second vertex) := by
  unfold cross
  rw [Quadrance.lineThrough_norm_eq_quadrance first vertex firstDistinct,
    Quadrance.lineThrough_norm_eq_quadrance second vertex secondDistinct]
  congr 1

end Purelib.Geometry.Plane.Line.Cross

end
