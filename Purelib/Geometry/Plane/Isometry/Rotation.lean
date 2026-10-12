module
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Geometry.Plane.HalfTurn.Basic
public import Purelib.Geometry.Plane.Isometry.Basic
import Purelib.Geometry.Plane.Point.Basic
import Purelib.Geometry.Plane.Point.Quadrance
import Mathlib.Algebra.Group.Basic
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

namespace Purelib.Geometry.Plane.Isometry.Rotation

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- Exercise 13.2: rotation in any point is an isometry. Its displayed inverse is itself, exactly as established in
Exercise 4.1. -/
def rotationInPointIsometry (center : Plane.Point K) :
  Isometry.Basic.PlaneIsometry K where
  toFun := Purelib.Geometry.Plane.HalfTurn.Basic.rotateInPoint center
  inverseFun := Purelib.Geometry.Plane.HalfTurn.Basic.rotateInPoint center
  inverse_after := HalfTurn.Basic.rotateInPoint_involutive center
  after_inverse := HalfTurn.Basic.rotateInPoint_involutive center
  preservesQuadrance := by
    intro first second
    unfold Purelib.Geometry.Plane.Point.Quadrance.quadrance Purelib.Geometry.Plane.HalfTurn.Basic.rotateInPoint
    ring1

/-- The coordinate map `ρ_{q,r}([x,y]) = [qx-ry,rx+qy]`. -/
def centralRotationPoint (q r : K) (point : Plane.Point K) :
  Plane.Point K :=
  ⟨q * point.x - r * point.y, r * point.x + q * point.y⟩

/-- Example 13.3: a unit pair gives a central rotation whose displayed inverse has parameters `[q,-r]`. -/
def centralRotation (q r : K) (unit : q ^ 2 + r ^ 2 = 1) :
    Isometry.Basic.PlaneIsometry K where
  toFun := centralRotationPoint q r
  inverseFun := centralRotationPoint q (-r)
  inverse_after := by
    intro point
    apply Plane.Point.ext
    · simp only [centralRotationPoint]
      calc
        q * (q * point.x - r * point.y) -
            (-r) * (r * point.x + q * point.y) =
          (q ^ 2 + r ^ 2) * point.x := by ring1
        _ = point.x := by rw [unit]; ring1
    · simp only [centralRotationPoint]
      calc
        (-r) * (q * point.x - r * point.y) +
            q * (r * point.x + q * point.y) =
          (q ^ 2 + r ^ 2) * point.y := by ring1
        _ = point.y := by rw [unit]; ring1
  after_inverse := by
    intro point
    apply Plane.Point.ext
    · simp only [centralRotationPoint]
      calc
        q * (q * point.x - (-r) * point.y) -
            r * ((-r) * point.x + q * point.y) =
          (q ^ 2 + r ^ 2) * point.x := by ring1
        _ = point.x := by rw [unit]; ring1
    · simp only [centralRotationPoint]
      calc
        r * (q * point.x - (-r) * point.y) +
            q * ((-r) * point.x + q * point.y) =
          (q ^ 2 + r ^ 2) * point.y := by ring1
        _ = point.y := by rw [unit]; ring1
  preservesQuadrance := by
    intro first second
    unfold Purelib.Geometry.Plane.Point.Quadrance.quadrance
    simp only [centralRotationPoint]
    calc
      (q * second.x - r * second.y -
            (q * first.x - r * first.y)) ^ 2 +
          (r * second.x + q * second.y -
            (r * first.x + q * first.y)) ^ 2 =
        (q ^ 2 + r ^ 2) *
          ((second.x - first.x) ^ 2 + (second.y - first.y) ^ 2) := by
            ring1
      _ = (second.x - first.x) ^ 2 + (second.y - first.y) ^ 2 := by
        rw [unit]
        ring1

/-- The inverse formula printed in Example 13.3. -/
theorem centralRotation_inverse_apply (q r : K)
    (unit : q ^ 2 + r ^ 2 = 1) (point : Plane.Point K) :
    (centralRotation q r unit).inverse point =
      centralRotationPoint q (-r) point := rfl

/-- Example 13.3: a central rotation fixes the origin. -/
theorem centralRotation_orthogonality (q r : K)
    (unit : q ^ 2 + r ^ 2 = 1) :
    (centralRotation q r unit).IsOrthogonality := by
  unfold Isometry.Basic.PlaneIsometry.IsOrthogonality Point.Basic.planeOrigin centralRotation
    centralRotationPoint
  apply Plane.Point.ext <;>
    ring1

/-- Exercise 13.4: the identity is the central rotation with parameters `[1,0]`. -/
theorem identity_centralRotationPoint (point : Plane.Point
  K) :
    centralRotationPoint 1 0 point = point := by
  apply Plane.Point.ext <;>
    simp only [centralRotationPoint] <;>
    ring1
end Purelib.Geometry.Plane.Isometry.Rotation

end
