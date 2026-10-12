module
import Purelib.Algebra.Field.ExplicitField
import Purelib.Geometry.Plane.Point.Basic
public import Purelib.Geometry.Plane.Point.Determinant
-- Exposed scalar formulas retain their explicit successor certificates.
public import Purelib.Data.Nat.Order
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Tactic.Ring

open Purelib

open Purelib.Geometry
open scoped Purelib.Data.Nat

/-!
# Divine Proportions, Chapter 9: finite oriented areas

An oriented polygon is represented by a finite `List` of points.  The
denominator-free primitive is twice its signed area; the book's signed area is
obtained by dividing that finite sum by two.  This keeps the cancellation and
characteristic assumptions visible while the core shoelace and
Bretschneider identities remain polynomial.
-/

@[expose] public section

namespace Purelib.Geometry.Polygons.SignedArea.Basic

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- Shoelace recursion from `current` through the remaining vertices and back to `first`. -/
def polygonDoubleSignedAreaAux (first current :
  Plane.Point K) :
    List (Plane.Point K) → K
  | [] => Purelib.Geometry.Plane.Point.Determinant.positionDeterminant current first
  | next :: remaining =>
      Purelib.Geometry.Plane.Point.Determinant.positionDeterminant current next +
        polygonDoubleSignedAreaAux first next remaining

/-- Twice the signed area of a finite oriented polygon. -/
def polygonDoubleSignedArea : List (Plane.Point K) → K
  | [] => 0
  | first :: remaining =>
      polygonDoubleSignedAreaAux first first remaining

/-- The book's signed area of a finite oriented polygon. -/
def polygonSignedArea (vertices : List (Plane.Point K)) :
  K :=
  polygonDoubleSignedArea vertices / 2

/-- Quadrea of a finite oriented polygon in denominator-free form. -/
def polygonQuadrea (vertices : List (Plane.Point K)) : K
  :=
  4 * polygonDoubleSignedArea vertices ^ 2

/-- The finite polygon definition agrees with sixteen times squared signed area.

For an explicit field in which two is nonzero, division by two recovers signed
area from the doubled shoelace sum. Squaring this equality identifies quadrea
with the displayed scalar multiple of squared signed area. -/
theorem polygon_quadrea_eq_sixteen_signed_area_square
    (vertices : List (Plane.Point K)) (twoNonzero : (2 : K) ≠ 0) :
    polygonQuadrea vertices = 16 * polygonSignedArea vertices ^ 2 :=
      by
  have doubled : 2 * polygonSignedArea vertices =
      polygonDoubleSignedArea vertices := by
    unfold polygonSignedArea
    calc
      2 * (polygonDoubleSignedArea vertices / 2) =
          (polygonDoubleSignedArea vertices / 2) * 2 := by ring1
      _ = polygonDoubleSignedArea vertices :=
        Algebra.Field.ExplicitField.div_mul_cancel _ twoNonzero
  unfold polygonQuadrea
  rw [← doubled]
  simp only [pow_two]
  ring1
end Purelib.Geometry.Polygons.SignedArea.Basic

end
