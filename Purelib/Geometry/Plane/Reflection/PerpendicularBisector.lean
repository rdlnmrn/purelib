module
-- Retained public numeral and subtraction parents use their original operations.
public import Purelib.Data.Nat.Order
public import Purelib.Algebra.Group.Negation
import Purelib.Algebra.Field.ExplicitField
import Purelib.Geometry.Plane.Line.Altitude
import Purelib.Geometry.Plane.Line.Basic
import Purelib.Geometry.Plane.Line.Construction
public import Purelib.Geometry.Plane.Line.PerpendicularBisector
import Purelib.Geometry.Plane.Point.Affine
import Purelib.Geometry.Plane.Point.Basic
public import Purelib.Geometry.Plane.Reflection.Point
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Tactic.Ring

section
open Purelib
open Purelib.Geometry
open Purelib.Geometry.Plane
open Purelib.Geometry.Plane.Line
open Purelib.Geometry.Plane.Point
open Purelib.Geometry.Plane.Point.Affine

open scoped Purelib.Data.Nat
attribute [local instance 2000] Purelib.Data.Nat.successorNeZero
  Purelib.Data.Nat.successorAtLeastTwo
  Purelib.Algebra.Group.Negation.subNegZeroMonoid

section
public section

/-!
# Divine Proportions, conic axes

An axis is retained as an explicit non-null mirror together with the finite
equation-preservation identity from Exercise 15.8.  The elementary reflection
lemmas below construct the two mirrors used for quadrolas without selecting
any roots or completed geometric object.
-/

section

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

section

namespace Purelib.Geometry.Plane.Reflection.PerpendicularBisector
/-- The midpoint lies on the altitude through the first endpoint to the perpendicular bisector when two is nonzero. -/
private theorem midpoint_on_perpendicularBisector_altitude [DecidableEq K]
    (first second : Point K) (distinct : first ≠ second)
    (twoNonzero : (2 : K) ≠ 0) :
    (Construction.altitudeThrough first (PerpendicularBisector.perpendicularBisector first second distinct)).Contains
      (Affine.midpoint first second) := by
  have twoCancel : (2 : K) * (2 : K)⁻¹ = 1 :=
    Algebra.Field.ExplicitField.mul_inv_cancel 2 twoNonzero
  unfold Construction.altitudeThrough PerpendicularBisector.perpendicularBisector Affine.midpoint Line.Contains
  simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
  calc
    -(first.y - second.y) *
            ((first.x + second.x) * (2 : K)⁻¹) +
          (first.x - second.x) *
            ((first.y + second.y) * (2 : K)⁻¹) +
          ((first.y - second.y) * first.x -
            (first.x - second.x) * first.y) =
        (1 - 2 * (2 : K)⁻¹) *
          ((first.y - second.y) * first.x -
            (first.x - second.x) * first.y) := by ring1
    _ = 0 := by rw [twoCancel]; ring1
end Purelib.Geometry.Plane.Reflection.PerpendicularBisector

end

namespace Purelib.Geometry.Plane.Reflection.PerpendicularBisector

/-- Reflection in the perpendicular bisector exchanges its first endpoint with the second. -/
theorem reflectPoint_perpendicularBisector_first [DecidableEq K]
    (first second : Point K) (distinct : first ≠ second)
    (twoNonzero : (2 : K) ≠ 0)
    (bisectorNonNull :
      ¬ (PerpendicularBisector.perpendicularBisector first second distinct).IsNull) :
    Reflection.Point.reflectPoint (PerpendicularBisector.perpendicularBisector first second distinct)
      bisectorNonNull first = second := by
  let bisector := PerpendicularBisector.perpendicularBisector first second distinct
  have midpointIsFoot :
      Affine.midpoint first second = Altitude.altitudeFoot first bisector bisectorNonNull := by
    apply Altitude.altitudeFoot_unique first bisector bisectorNonNull
    · exact PerpendicularBisector.perpendicularBisector_contains_midpoint first second distinct
    · exact Purelib.Geometry.Plane.Reflection.PerpendicularBisector.midpoint_on_perpendicularBisector_altitude
        first second distinct
        twoNonzero
  have twiceX := midpoint_twice_x first second twoNonzero
  have twiceY := midpoint_twice_y first second twoNonzero
  unfold Reflection.Point.reflectPoint
  rw [← midpointIsFoot]
  apply Point.ext
  · change 2 * (Affine.midpoint first second).x - first.x = second.x
    rw [twiceX]
    ring1
  · change 2 * (Affine.midpoint first second).y - first.y = second.y
    rw [twiceY]
    ring1

/-- The reverse endpoint exchange follows from involutivity of reflection. -/
theorem reflectPoint_perpendicularBisector_second [DecidableEq K]
    (first second : Point K) (distinct : first ≠ second)
    (twoNonzero : (2 : K) ≠ 0)
    (bisectorNonNull :
      ¬ (PerpendicularBisector.perpendicularBisector first second distinct).IsNull) :
    Reflection.Point.reflectPoint (PerpendicularBisector.perpendicularBisector first second distinct)
      bisectorNonNull second = first := by
  let bisector := PerpendicularBisector.perpendicularBisector first second distinct
  have firstToSecond := Geometry.Plane.Reflection.PerpendicularBisector.reflectPoint_perpendicularBisector_first first
    second
    distinct twoNonzero bisectorNonNull
  calc
    Reflection.Point.reflectPoint bisector bisectorNonNull second =
        Reflection.Point.reflectPoint bisector bisectorNonNull
          (Reflection.Point.reflectPoint bisector bisectorNonNull first) := by
            rw [firstToSecond]
    _ = first := Reflection.Point.reflectPoint_involutive bisector bisectorNonNull first

end Purelib.Geometry.Plane.Reflection.PerpendicularBisector

end

end

end
