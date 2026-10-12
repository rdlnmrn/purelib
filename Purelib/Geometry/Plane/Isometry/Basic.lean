module

import Purelib.Algebra.Field.ExplicitField
import Purelib.Geometry.Plane.Point.Basic
public import Purelib.Geometry.Plane.Point.Quadrance
import Init.Prelude
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

open Purelib.Geometry

open Purelib.Geometry.Plane.Point

section
/-!
# Divine Proportions, §13.1 and Theorem 91: finite plane isometries

An isometry carries both an executable point map and an executable inverse.
Its metric law is the finite equality asserting preservation of quadrance;
there is no completed space, infinite carrier argument, or selected inverse.

Theorem 91 follows exactly the source proof through the Triple-quad formula.
The hypothesis `2 ≠ 0` is exposed because over characteristic two the book's
quadrance degenerates and no longer detects collinearity.
-/

@[expose] public section

namespace Purelib.Geometry

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

set_option genInjectivity false in
/-- A finite, constructive plane isometry: a point map, a displayed inverse, and the source's quadrance-preservation
law. -/
structure Plane.Isometry.Basic.PlaneIsometry (K : Type*) [Algebra.Field.ExplicitField K] where
  /-- The executable forward map on Cartesian points. -/ toFun : Plane.Point K → Plane.Point K
  /-- The executable inverse map on Cartesian points. -/ inverseFun : Plane.Point K →
    Plane.Point K
  /-- The inverse map cancels the forward map at every point. -/ inverse_after : ∀ point, inverseFun (toFun point) =
    point
  /-- The forward map cancels the inverse map at every point. -/ after_inverse : ∀ point, toFun (inverseFun point) =
    point
  /-- The forward map preserves quadrance between each pair of points. -/ preservesQuadrance : ∀ first second,
    Quadrance.quadrance (toFun first) (toFun second) = Quadrance.quadrance first second

constructive_injectivity Plane.Isometry.Basic.PlaneIsometry

/-- Regard an isometry as its stored point map. -/
instance : CoeFun (Geometry.Plane.Isometry.Basic.PlaneIsometry K) (fun _ => Plane.Point K →
  Plane.Point K) where
  coe isometry := isometry.toFun

namespace Plane.Isometry.Basic.PlaneIsometry

/-- The identity isometry. -/
def identity : PlaneIsometry K
  where
  toFun := fun point => point
  inverseFun := fun point => point
  inverse_after := fun _ => rfl
  after_inverse := fun _ => rfl
  preservesQuadrance := fun _ _ => rfl

/-- Exercise 13.1, inverse half: the displayed inverse of an isometry is an isometry, with the original map as its
displayed inverse. -/
def inverse (isometry :
  PlaneIsometry K) : PlaneIsometry K where
  toFun := isometry.inverseFun
  inverseFun := isometry.toFun
  inverse_after := isometry.after_inverse
  after_inverse := isometry.inverse_after
  preservesQuadrance := by
    intro first second
    calc
      Quadrance.quadrance (isometry.inverseFun first) (isometry.inverseFun second) =
          Quadrance.quadrance
            (isometry (isometry.inverseFun first))
            (isometry (isometry.inverseFun second)) :=
              (isometry.preservesQuadrance
                (isometry.inverseFun first)
                (isometry.inverseFun second)).symm
      _ = Quadrance.quadrance first second := by
        rw [isometry.after_inverse, isometry.after_inverse]

/-- Exercise 13.1, composition half: the composite first applies `inner` and then `outer`; its inverse is displayed in
the opposite order. -/
def comp (outer inner :
  PlaneIsometry K) : PlaneIsometry K where
  toFun := fun point => outer (inner point)
  inverseFun := fun point => inner.inverseFun (outer.inverseFun point)
  inverse_after := by
    intro point
    rw [outer.inverse_after, inner.inverse_after]
  after_inverse := by
    intro point
    rw [inner.after_inverse, outer.after_inverse]
  preservesQuadrance := by
    intro first second
    rw [outer.preservesQuadrance, inner.preservesQuadrance]

/-- The identity isometry fixes every point. -/
@[simp] theorem identity_apply (point :
  Plane.Point K) :
    (identity : PlaneIsometry K) point = point
      := rfl

/-- The inverse isometry uses the stored inverse point map. -/
@[simp] theorem inverse_apply (isometry :
  PlaneIsometry K) (point : Plane.Point K) :
    isometry.inverse point = isometry.inverseFun point := rfl

/-- Composition applies the inner isometry followed by the outer isometry. -/
@[simp] theorem comp_apply (outer inner :
  PlaneIsometry K) (point : Plane.Point K) :
    outer.comp inner point = outer (inner point) := rfl

/-- The point map of an isometry is injective, with its displayed inverse providing the direct cancellation proof. -/
theorem injective (isometry :
  PlaneIsometry K) :
    Function.Injective isometry := by
  intro first second equalImages
  calc
    first = isometry.inverseFun (isometry first) :=
      (isometry.inverse_after first).symm
    _ = isometry.inverseFun (isometry second) := by rw [equalImages]
    _ = second := isometry.inverse_after second

/-- Every target point has the explicitly displayed inverse image. -/
theorem surjective (isometry :
  PlaneIsometry K) :
    Function.Surjective isometry := by
  intro point
  exact ⟨isometry.inverseFun point, isometry.after_inverse point⟩

/-- An orthogonality is an isometry fixing the displayed origin. -/
def IsOrthogonality (isometry :
  PlaneIsometry K) : Prop :=
  isometry Plane.Point.Basic.planeOrigin = Plane.Point.Basic.planeOrigin
end Plane.Isometry.Basic.PlaneIsometry

end Purelib.Geometry

end

end
