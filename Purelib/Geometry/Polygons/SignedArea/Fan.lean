module
import Purelib.Algebra.Field.ExplicitField
import Purelib.Geometry.Plane.Point.Basic
import Purelib.Geometry.Plane.Point.Determinant
public import Purelib.Geometry.Polygons.SignedArea.Basic
public import Purelib.Geometry.Triangles.SignedArea
import Init.Prelude
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Tactic.Ring

open Purelib

open Purelib.Geometry

open Purelib.Geometry.Plane.Point

open Purelib.Geometry.Polygons

/-!
# Divine Proportions, Chapter 9: finite oriented areas

An oriented polygon is represented by a finite `List` of points.  The
denominator-free primitive is twice its signed area; the book's signed area is
obtained by dividing that finite sum by two.  This keeps the cancellation and
characteristic assumptions visible while the core shoelace and
Bretschneider identities remain polynomial.
-/

@[expose] public section

namespace Purelib.Geometry.Polygons.SignedArea.Fan

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- Finite fan triangulation about `center`. -/
def fanDoubleSignedAreaAux (center first current :
  Plane.Point K) :
    List (Plane.Point K) → K
  | [] => Purelib.Geometry.Triangles.SignedArea.triangleDoubleSignedArea center current first
  | next :: remaining =>
      Purelib.Geometry.Triangles.SignedArea.triangleDoubleSignedArea center current next +
        fanDoubleSignedAreaAux center first next remaining

/-- Sum of the doubled signed areas of the triangles from `center` to every cyclic edge of the finite polygon. -/
def fanDoubleSignedArea (center : Plane.Point K) : List
  (Plane.Point K) → K
  | [] => 0
  | first :: remaining => fanDoubleSignedAreaAux center first first remaining

/-- The corresponding sum in the book's signed-area normalization. -/
def fanSignedArea (center : Plane.Point K) (vertices : List
  (Plane.Point K)) : K :=
  fanDoubleSignedArea center vertices / 2

/-- Denominator-cleared Theorem 62: the fan sum is independent of its center and equals the finite cyclic shoelace sum.
-/
theorem fan_double_signed_area
    (center : Plane.Point K) (vertices : List (Plane.Point K)) :
    fanDoubleSignedArea center vertices = SignedArea.Basic.polygonDoubleSignedArea
      vertices := by
  cases vertices with
  | nil => rfl
  | cons first remaining =>
      change fanDoubleSignedAreaAux center first first remaining =
        SignedArea.Basic.polygonDoubleSignedAreaAux first first remaining
      have telescopes : ∀ (current : Plane.Point K) (remaining : List (Plane.Point K)),
          fanDoubleSignedAreaAux center first current remaining =
            SignedArea.Basic.polygonDoubleSignedAreaAux first current remaining +
              Determinant.positionDeterminant center current +
                Determinant.positionDeterminant first center := by
        intro current remaining
        induction remaining generalizing current with
        | nil =>
            unfold fanDoubleSignedAreaAux SignedArea.Basic.polygonDoubleSignedAreaAux
              Triangles.SignedArea.triangleDoubleSignedArea Determinant.positionDeterminant
            ring1
        | cons next remaining inductionHypothesis =>
            unfold fanDoubleSignedAreaAux SignedArea.Basic.polygonDoubleSignedAreaAux
            rw [inductionHypothesis]
            unfold Triangles.SignedArea.triangleDoubleSignedArea Determinant.positionDeterminant
            ring1
      rw [telescopes first remaining]
      unfold Determinant.positionDeterminant
      ring1

/-- Theorem 62 (Signed area), in the book's `/2` normalization. -/
theorem signed_area (center : Plane.Point K) (vertices :
  List (Plane.Point K)) :
    fanSignedArea center vertices = SignedArea.Basic.polygonSignedArea vertices := by
  unfold fanSignedArea SignedArea.Basic.polygonSignedArea
  rw [fan_double_signed_area]

/-- The explicit independence-of-`P` statement from Theorem 62. -/
theorem fan_signed_area_independent
    (firstCenter secondCenter : Plane.Point K) (vertices : List (Plane.Point K)) :
    fanSignedArea firstCenter vertices = fanSignedArea
      secondCenter vertices := by
  rw [signed_area, signed_area]

/-- Exercise 9.5, strengthened to a fan based at any displayed point: a finite polygon's signed area is the sum of its
oriented fan triangles. -/
theorem exercise_9_5 (center : Plane.Point K) (vertices :
  List (Plane.Point K)) :
    SignedArea.Basic.polygonSignedArea vertices = fanSignedArea center vertices :=
  (signed_area center vertices).symm
end Purelib.Geometry.Polygons.SignedArea.Fan

end
