module
public import Purelib.Data.Nat.Order
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Geometry.Plane.Isometry.Basic
import Purelib.Geometry.Plane.Point.Basic
import Purelib.Geometry.Plane.Point.Quadrance
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Tactic.Ring

open Purelib.Geometry.Plane.Isometry.Basic (PlaneIsometry)

open Purelib

open Purelib.Geometry

open Purelib.Geometry.Plane

open Purelib.Geometry.Plane.Point

/-!
# Divine Proportions, Theorem 92: specifying an isometry

The proof is the source's three finite quadrance equations.  Subtracting the
equations at the origin and the two coordinate points recovers twice each
coordinate; the explicit inverse of two then cancels that factor.
-/

@[expose] public section

namespace Purelib.Geometry.Plane.Isometry.Basic.PlaneIsometry

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]
section

/-- The coordinate rigidity calculation in the proof of Theorem 92: an isometry fixing `O`, `I₁`, and `I₂` fixes every
displayed point. -/
theorem fixingReferencePoints_eq_identity
    (isometry : Isometry.Basic.PlaneIsometry K) (twoNonzero : (2 : K) ≠ 0)
    (fixesOrigin : isometry Basic.planeOrigin = Basic.planeOrigin)
    (fixesFirstAxis : isometry Basic.firstAxisPoint = Basic.firstAxisPoint)
    (fixesSecondAxis : isometry Basic.secondAxisPoint = Basic.secondAxisPoint)
    (point : Plane.Point K) : isometry point = point := by
  have originQuadrance :
      Quadrance.quadrance (isometry point) Basic.planeOrigin = Quadrance.quadrance point Basic.planeOrigin := by
    calc
      Quadrance.quadrance (isometry point) Basic.planeOrigin =
          Quadrance.quadrance (isometry point) (isometry Basic.planeOrigin) := by
            rw [fixesOrigin]
      _ = Quadrance.quadrance point Basic.planeOrigin :=
        isometry.preservesQuadrance point Basic.planeOrigin
  have firstAxisQuadrance :
      Quadrance.quadrance (isometry point) Basic.firstAxisPoint =
        Quadrance.quadrance point Basic.firstAxisPoint := by
    calc
      Quadrance.quadrance (isometry point) Basic.firstAxisPoint =
          Quadrance.quadrance (isometry point) (isometry Basic.firstAxisPoint) := by
            rw [fixesFirstAxis]
      _ = Quadrance.quadrance point Basic.firstAxisPoint :=
        isometry.preservesQuadrance point Basic.firstAxisPoint
  have secondAxisQuadrance :
      Quadrance.quadrance (isometry point) Basic.secondAxisPoint =
        Quadrance.quadrance point Basic.secondAxisPoint := by
    calc
      Quadrance.quadrance (isometry point) Basic.secondAxisPoint =
          Quadrance.quadrance (isometry point) (isometry Basic.secondAxisPoint) := by
            rw [fixesSecondAxis]
      _ = Quadrance.quadrance point Basic.secondAxisPoint :=
        isometry.preservesQuadrance point Basic.secondAxisPoint
  have equalXDouble : (2 : K) * (isometry point).x = 2 * point.x := by
    calc
      (2 : K) * (isometry point).x =
          Quadrance.quadrance (isometry point) Basic.planeOrigin -
            Quadrance.quadrance (isometry point) Basic.firstAxisPoint + 1 := by
              unfold Quadrance.quadrance Basic.planeOrigin Basic.firstAxisPoint
              ring1
      _ = Quadrance.quadrance point Basic.planeOrigin - Quadrance.quadrance point Basic.firstAxisPoint + 1 := by
        rw [originQuadrance, firstAxisQuadrance]
      _ = 2 * point.x := by
        unfold Quadrance.quadrance Basic.planeOrigin Basic.firstAxisPoint
        ring1
  have equalYDouble : (2 : K) * (isometry point).y = 2 * point.y := by
    calc
      (2 : K) * (isometry point).y =
          Quadrance.quadrance (isometry point) Basic.planeOrigin -
            Quadrance.quadrance (isometry point) Basic.secondAxisPoint + 1 := by
              unfold Quadrance.quadrance Basic.planeOrigin Basic.secondAxisPoint
              ring1
      _ = Quadrance.quadrance point Basic.planeOrigin - Quadrance.quadrance point Basic.secondAxisPoint + 1 := by
        rw [originQuadrance, secondAxisQuadrance]
      _ = 2 * point.y := by
        unfold Quadrance.quadrance Basic.planeOrigin Basic.secondAxisPoint
        ring1
  have cancelDouble : ∀ left right : K,
      (2 : K) * left = 2 * right → left = right := by
    intro left right equalDoubles
    have twoCancel : (2 : K) * (2 : K)⁻¹ = 1 :=
      Algebra.Field.ExplicitField.mul_inv_cancel 2 twoNonzero
    calc
      left = 1 * left := by ring1
      _ = (2 * (2 : K)⁻¹) * left := by rw [twoCancel]
      _ = (2 : K)⁻¹ * (2 * left) := by ring1
      _ = (2 : K)⁻¹ * (2 * right) := by rw [equalDoubles]
      _ = (2 * (2 : K)⁻¹) * right := by ring1
      _ = right := by rw [twoCancel]; ring1
  apply Plane.Point.ext
  · exact cancelDouble (isometry point).x point.x equalXDouble
  · exact cancelDouble (isometry point).y point.y equalYDouble

/-- Theorem 92 (Specifying isometries): two isometries agreeing on `O`, `I₁`, and `I₂` agree on every point. Equality is
stated pointwise so the result records exactly the observable transformation without equating stored inverse proof data.
-/
theorem specifiedByReferencePoints
    (first second : Isometry.Basic.PlaneIsometry K) (twoNonzero : (2 : K) ≠ 0)
    (sameOrigin : first Plane.Point.Basic.planeOrigin = second Plane.Point.Basic.planeOrigin)
    (sameFirstAxis : first Plane.Point.Basic.firstAxisPoint = second Plane.Point.Basic.firstAxisPoint)
    (sameSecondAxis : first Plane.Point.Basic.secondAxisPoint = second Plane.Point.Basic.secondAxisPoint)
    (point : Plane.Point K) : first point = second point := by
  let comparison := second.inverse.comp first
  have comparisonFixesOrigin : comparison Plane.Point.Basic.planeOrigin = Plane.Point.Basic.planeOrigin := by
    unfold comparison PlaneIsometry.comp PlaneIsometry.inverse
    change second.inverseFun (first Plane.Point.Basic.planeOrigin) = Plane.Point.Basic.planeOrigin
    rw [sameOrigin, second.inverse_after]
  have comparisonFixesFirstAxis :
      comparison Plane.Point.Basic.firstAxisPoint = Plane.Point.Basic.firstAxisPoint := by
    unfold comparison PlaneIsometry.comp PlaneIsometry.inverse
    change second.inverseFun (first Plane.Point.Basic.firstAxisPoint) = Plane.Point.Basic.firstAxisPoint
    rw [sameFirstAxis, second.inverse_after]
  have comparisonFixesSecondAxis :
      comparison Plane.Point.Basic.secondAxisPoint = Plane.Point.Basic.secondAxisPoint := by
    unfold comparison PlaneIsometry.comp PlaneIsometry.inverse
    change second.inverseFun (first Plane.Point.Basic.secondAxisPoint) = Plane.Point.Basic.secondAxisPoint
    rw [sameSecondAxis, second.inverse_after]
  have comparisonFixesPoint : comparison point = point :=
    comparison.fixingReferencePoints_eq_identity twoNonzero
      comparisonFixesOrigin comparisonFixesFirstAxis comparisonFixesSecondAxis point
  have afterSecond := congrArg second comparisonFixesPoint
  calc
    first point = second (comparison point) := by
      unfold comparison PlaneIsometry.comp PlaneIsometry.inverse
      change first point = second (second.inverseFun (first point))
      rw [second.after_inverse]
    _ = second point := afterSecond

end

end Purelib.Geometry.Plane.Isometry.Basic.PlaneIsometry

end
