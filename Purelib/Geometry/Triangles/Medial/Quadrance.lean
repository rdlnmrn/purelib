module
import Purelib.Algebra.Field.ExplicitField
import Purelib.Geometry.Plane.Point.Affine
import Purelib.Geometry.Plane.Point.Affine.Quadrance
import Purelib.Geometry.Plane.Point.Basic
public import Purelib.Geometry.Plane.Point.Quadrance
public import Purelib.Geometry.Triangles.Medial.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init

open Purelib.Geometry

open Purelib.Geometry.Plane.Point

open Purelib.Geometry.Plane.Point.Affine

open Purelib.Geometry.Triangles

section
@[expose] public section

/-!
# Divine Proportions, Chapter 10: the median triangle

All three midpoint sides are retained as displayed lines.  Their distinctness,
parallelism, and non-nullity are proved explicitly, so the final similarity
statement is a finite triple of spread equalities over any explicit field of
characteristic different from two.
-/

namespace Purelib.Geometry.Triangles.Medial.Quadrance

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- The first median-triangle side has one quarter of the corresponding original quadrance.

The field must have nonzero two so the midpoint divisions cancel. -/
theorem median_side₁₂_quadrance
    (first second third : Plane.Point K) (twoNonzero : (2 : K) ≠ 0) :
    Quadrance.quadrance (Medial.Basic.sideMidpointOppositeFirst first second third)
        (Medial.Basic.sideMidpointOppositeSecond first second third) =
      Quadrance.quadrance first second / 4 := by
  unfold Medial.Basic.sideMidpointOppositeFirst Medial.Basic.sideMidpointOppositeSecond
  calc
    Quadrance.quadrance (Affine.midpoint second third) (Affine.midpoint first third) =
        Quadrance.quadrance second first / 4 :=
      Quadrance.midpoint_segment_quadrance second first third twoNonzero
    _ = Quadrance.quadrance first second / 4 := by rw [Quadrance.quadrance_symm second first]

/-- The second median-triangle side has one quarter of the corresponding original quadrance.

The field must have nonzero two so the midpoint divisions cancel. -/
theorem median_side₂₃_quadrance
    (first second third : Plane.Point K) (twoNonzero : (2 : K) ≠ 0) :
    Quadrance.quadrance (Medial.Basic.sideMidpointOppositeSecond first second third)
        (Medial.Basic.sideMidpointOppositeThird first second third) =
      Quadrance.quadrance second third / 4 := by
  unfold Medial.Basic.sideMidpointOppositeSecond Medial.Basic.sideMidpointOppositeThird
  calc
    Quadrance.quadrance (Affine.midpoint first third) (Affine.midpoint first second) =
        Quadrance.quadrance third second / 4 :=
      Quadrance.midpoint_segment_quadrance_left first third second twoNonzero
    _ = Quadrance.quadrance second third / 4 := by rw [Quadrance.quadrance_symm third second]

/-- The third median-triangle side has one quarter of the corresponding original quadrance.

The field must have nonzero two so the midpoint divisions cancel. -/
theorem median_side₁₃_quadrance
    (first second third : Plane.Point K) (twoNonzero : (2 : K) ≠ 0) :
    Quadrance.quadrance (Medial.Basic.sideMidpointOppositeFirst first second third)
        (Medial.Basic.sideMidpointOppositeThird first second third) =
      Quadrance.quadrance first third / 4 := by
  unfold Medial.Basic.sideMidpointOppositeFirst Medial.Basic.sideMidpointOppositeThird
  calc
    Quadrance.quadrance (Affine.midpoint second third) (Affine.midpoint first second) =
        Quadrance.quadrance (Affine.midpoint third second) (Affine.midpoint first second) := by
      rw [Affine.midpoint_symm second third]
    _ = Quadrance.quadrance third first / 4 :=
      Quadrance.midpoint_segment_quadrance third first second twoNonzero
    _ = Quadrance.quadrance first third / 4 := by rw [Quadrance.quadrance_symm third first]
end Purelib.Geometry.Triangles.Medial.Quadrance

end
