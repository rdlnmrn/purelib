module
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Geometry.Plane.Isometry.Basic
public import Purelib.Geometry.Plane.Point.Affine
import Purelib.Geometry.Plane.Point.Basic
import Purelib.Geometry.Plane.Point.Quadrance
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Purelib.Tactic.Ring

open Purelib

open Purelib.Geometry

open Purelib.Geometry.Plane

open Purelib.Geometry.Plane.Point

/-!
# Divine Proportions, §13.1: translations, rotations, and reflections

This file gives executable isometries for the coordinate transformations in
Examples 13.1–13.3 and proves the composition calculations requested in
Exercises 13.2, 13.4, and 13.5.
-/

@[expose] public section

namespace Purelib.Geometry.Plane.Isometry.Translation

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- Example 13.1: translation by `[u,v]`, with translation by `[-u,-v]` as its displayed inverse. -/
def translation (u v : K) : Isometry.Basic.PlaneIsometry K where
  toFun := Point.Affine.translationPoint u v
  inverseFun := Point.Affine.translationPoint (-u) (-v)
  inverse_after := by
    intro point
    apply Plane.Point.ext <;>
      unfold Point.Affine.translationPoint <;>
      ring1
  after_inverse := by
    intro point
    apply Plane.Point.ext <;>
      unfold Point.Affine.translationPoint <;>
      ring1
  preservesQuadrance := by
    intro first second
    unfold Point.Quadrance.quadrance Point.Affine.translationPoint
    ring1

/-- Applying the translation is the displayed coordinate addition map. -/
@[simp] theorem translation_apply (u v : K) (point :
  Plane.Point K) :
    translation u v point = Affine.translationPoint u v point := rfl

/-- The inverse formula printed in Example 13.1. -/
theorem translation_inverse_apply (u v : K) (point :
  Plane.Point K) :
    (translation u v).inverse point =
      translation (-u) (-v) point := rfl
end Purelib.Geometry.Plane.Isometry.Translation

end
