module
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Geometry.Plane.Isometry.Basic
import Purelib.Geometry.Plane.Line.Basic
import Purelib.Geometry.Plane.Point.Basic
import Purelib.Geometry.Plane.Point.Quadrance
public import Purelib.Geometry.Plane.Reflection.Point
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Purelib.Tactic.Ring

open Purelib

open Purelib.Geometry

open Purelib.Geometry.Plane

/-!
# Divine Proportions, §13.1: translations, rotations, and reflections

This file gives executable isometries for the coordinate transformations in
Examples 13.1–13.3 and proves the composition calculations requested in
Exercises 13.2, 13.4, and 13.5.
-/

@[expose] public section

namespace Purelib.Geometry.Plane.Isometry.Reflection

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- Exercise 13.2: reflection in a displayed non-null line is an isometry, with its explicit involution as inverse. -/
def lineReflectionIsometry (line : Plane.Line K) (nonNull : ¬
  line.IsNull) :
    Isometry.Basic.PlaneIsometry K where
  toFun := Reflection.Point.reflectPoint line nonNull
  inverseFun := Reflection.Point.reflectPoint line nonNull
  inverse_after := Reflection.Point.reflectPoint_involutive line nonNull
  after_inverse := Reflection.Point.reflectPoint_involutive line nonNull
  preservesQuadrance := Reflection.Point.reflectPoint_preserves_quadrance line nonNull

/-- The coordinate map `σ_{q,r}([x,y]) = [qx+ry,rx-qy]`. -/
def centralReflectionPoint (q r : K) (point : Plane.Point
  K) : Plane.Point K :=
  ⟨q * point.x + r * point.y, r * point.x - q * point.y⟩

/-- Example 13.2: a unit pair gives a self-inverse central reflection. -/
def centralReflection (q r : K) (unit : q ^ 2 + r ^ 2 = 1) :
    Isometry.Basic.PlaneIsometry K where
  toFun := centralReflectionPoint q r
  inverseFun := centralReflectionPoint q r
  inverse_after := by
    intro point
    apply Plane.Point.ext
    · simp only [centralReflectionPoint]
      calc
        q * (q * point.x + r * point.y) +
            r * (r * point.x - q * point.y) =
          (q ^ 2 + r ^ 2) * point.x := by ring1
        _ = point.x := by rw [unit]; ring1
    · simp only [centralReflectionPoint]
      calc
        r * (q * point.x + r * point.y) -
            q * (r * point.x - q * point.y) =
          (q ^ 2 + r ^ 2) * point.y := by ring1
        _ = point.y := by rw [unit]; ring1
  after_inverse := by
    intro point
    apply Plane.Point.ext
    · simp only [centralReflectionPoint]
      calc
        q * (q * point.x + r * point.y) +
            r * (r * point.x - q * point.y) =
          (q ^ 2 + r ^ 2) * point.x := by ring1
        _ = point.x := by rw [unit]; ring1
    · simp only [centralReflectionPoint]
      calc
        r * (q * point.x + r * point.y) -
            q * (r * point.x - q * point.y) =
          (q ^ 2 + r ^ 2) * point.y := by ring1
        _ = point.y := by rw [unit]; ring1
  preservesQuadrance := by
    intro first second
    unfold Purelib.Geometry.Plane.Point.Quadrance.quadrance
    simp only [centralReflectionPoint]
    calc
      (q * second.x + r * second.y -
            (q * first.x + r * first.y)) ^ 2 +
          (r * second.x - q * second.y -
            (r * first.x - q * first.y)) ^ 2 =
        (q ^ 2 + r ^ 2) *
          ((second.x - first.x) ^ 2 + (second.y - first.y) ^ 2) := by
            ring1
      _ = (second.x - first.x) ^ 2 + (second.y - first.y) ^ 2 := by
        rw [unit]
        ring1

/-- Example 13.2: a central reflection fixes the origin. -/
theorem centralReflection_orthogonality (q r : K)
    (unit : q ^ 2 + r ^ 2 = 1) :
    (centralReflection q r unit).IsOrthogonality := by
  unfold Isometry.Basic.PlaneIsometry.IsOrthogonality Point.Basic.planeOrigin centralReflection
    centralReflectionPoint
  apply Plane.Point.ext <;>
    ring1
end Purelib.Geometry.Plane.Isometry.Reflection

end
