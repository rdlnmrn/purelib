module
import Purelib.Geometry.Plane.Isometry.Specification
import Purelib.Geometry.Plane.Isometry.Basic
public import Purelib.Geometry.Plane.Isometry.Reflection
public import Purelib.Geometry.Plane.Isometry.Rotation
import Purelib.Geometry.Plane.Point.Basic
import Purelib.Geometry.Plane.Point.Quadrance

import Purelib.Algebra.Field.ExplicitField
import Purelib.LinearAlgebra.Coordinates2.Orthogonal
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Logic.Nontrivial.Defs
import Purelib.Tactic.Ring

open Purelib

open Purelib.Geometry

open Purelib.Geometry.Plane

open Purelib.Geometry.Plane.Isometry

open Purelib.Geometry.Plane.Point

open Purelib.LinearAlgebra

section
@[expose] public section

/-!
# Divine Proportions, Theorem 93: orthogonalities

An orthogonality is determined by the images of the two coordinate points.
The first is a unit pair `[q,r]`; finite coordinate algebra shows the second
is exactly one of `[r,-q]` and `[-r,q]`.  Theorem 92 then identifies the whole
map with the corresponding central reflection or central rotation.
-/

namespace Purelib.Geometry.Plane.Isometry.Orthogonality.PlaneIsometry

open Purelib.Algebra

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]
section

attribute [local instance high] SubNegMonoid.toNeg in
/-- Every origin-fixing isometry is a central rotation or a central reflection on all points.

The unit parameter pair is read from the first reference-axis image. Nonzero two and decidable equality distinguish the
two orientations. -/
theorem orthogonalityClassification [Nontrivial K]
  [DecidableEq K]
    (isometry : Isometry.Basic.PlaneIsometry K) (twoNonzero : (2 : K) ≠ 0)
    (fixesOrigin : isometry.IsOrthogonality) :
    ∃ q r : K, ∃ unit : q ^ 2 + r ^ 2 = 1,
      (∀ point : Plane.Point K,
          isometry point = Rotation.centralRotation q r unit point) ∨
        (∀ point : Plane.Point K,
          isometry point = Reflection.centralReflection q r unit point) := by
  let firstImage := isometry Basic.firstAxisPoint
  let secondImage := isometry Basic.secondAxisPoint
  let q := firstImage.x
  let r := firstImage.y
  let s := secondImage.x
  let t := secondImage.y
  have firstUnit : q ^ 2 + r ^ 2 = 1 := by
    have preserved := isometry.preservesQuadrance Basic.planeOrigin Basic.firstAxisPoint
    rw [fixesOrigin] at preserved
    simp only [Quadrance.quadrance, Basic.planeOrigin, Basic.firstAxisPoint, -eq_self, -iff_self] at preserved
    change q ^ 2 + r ^ 2 = 1
    calc
      q ^ 2 + r ^ 2 = Quadrance.quadrance Basic.planeOrigin firstImage := by
        unfold q r firstImage Quadrance.quadrance Basic.planeOrigin
        ring1
      _ = Quadrance.quadrance Basic.planeOrigin Basic.firstAxisPoint := preserved
      _ = 1 := by
        unfold Quadrance.quadrance Basic.planeOrigin Basic.firstAxisPoint
        ring1
  have secondUnit : s ^ 2 + t ^ 2 = 1 := by
    have preserved := isometry.preservesQuadrance Basic.planeOrigin Basic.secondAxisPoint
    rw [fixesOrigin] at preserved
    simp only [Quadrance.quadrance, Basic.planeOrigin, Basic.secondAxisPoint, -eq_self, -iff_self] at preserved
    change s ^ 2 + t ^ 2 = 1
    calc
      s ^ 2 + t ^ 2 = Quadrance.quadrance Basic.planeOrigin secondImage := by
        unfold s t secondImage Quadrance.quadrance Basic.planeOrigin
        ring1
      _ = Quadrance.quadrance Basic.planeOrigin Basic.secondAxisPoint := preserved
      _ = 1 := by
        unfold Quadrance.quadrance Basic.planeOrigin Basic.secondAxisPoint
        ring1
  have imageDistance :
      Quadrance.quadrance firstImage secondImage = (2 : K) := by
    have preserved :=
      isometry.preservesQuadrance Basic.firstAxisPoint Basic.secondAxisPoint
    change Quadrance.quadrance firstImage secondImage = Quadrance.quadrance Basic.firstAxisPoint Basic.secondAxisPoint
      at preserved
    calc
      Quadrance.quadrance firstImage secondImage =
          Quadrance.quadrance Basic.firstAxisPoint Basic.secondAxisPoint := preserved
      _ = 2 := by unfold Quadrance.quadrance Basic.firstAxisPoint Basic.secondAxisPoint; ring1
  have twiceDotZero : (2 : K) * (q * s + r * t) = 0 := by
    calc
      (2 : K) * (q * s + r * t) =
          (q ^ 2 + r ^ 2) + (s ^ 2 + t ^ 2) -
            Quadrance.quadrance firstImage secondImage := by
              unfold Quadrance.quadrance q r s t firstImage secondImage
              ring1
      _ = 0 := by rw [firstUnit, secondUnit, imageDistance]; ring1
  have twoCancel : (2 : K) * (2 : K)⁻¹ = 1 :=
    Algebra.Field.ExplicitField.mul_inv_cancel 2 twoNonzero
  have perpendicular : q * s + r * t = 0 := by
    calc
      q * s + r * t = 1 * (q * s + r * t) := by ring1
      _ = (2 * (2 : K)⁻¹) * (q * s + r * t) := by rw [twoCancel]
      _ = (2 : K)⁻¹ * (2 * (q * s + r * t)) := by ring1
      _ = 0 := by rw [twiceDotZero]; ring1
  refine ⟨q, r, firstUnit, ?_⟩
  rcases Coordinates2.Orthogonal.perpendicularUnitPair_orientations q r s t
      firstUnit secondUnit perpendicular with
    reflectionOrientation | rotationOrientation
  · right
    intro point
    apply isometry.specifiedByReferencePoints
      (Reflection.centralReflection q r firstUnit) twoNonzero
    · calc
        isometry Basic.planeOrigin = Basic.planeOrigin := fixesOrigin
        _ = Reflection.centralReflection q r firstUnit Basic.planeOrigin :=
          (Reflection.centralReflection_orthogonality q r firstUnit).symm
    · apply Plane.Point.ext
      · simp only [firstImage, q, r, Basic.firstAxisPoint,
          Reflection.centralReflection, Reflection.centralReflectionPoint, -eq_self, -iff_self]
        change q = q * 1 + r * 0
        ring1
      · change r = r * 1 - q * 0
        ring1
    · apply Plane.Point.ext
      · change s = q * 0 + r * 1
        calc
          s = r := reflectionOrientation.1
          _ = q * 0 + r * 1 := by ring1
      · change t = r * 0 - q * 1
        calc
          t = -q := reflectionOrientation.2
          _ = r * 0 - q * 1 := by ring1
  · left
    intro point
    apply isometry.specifiedByReferencePoints
      (Rotation.centralRotation q r firstUnit) twoNonzero
    · calc
        isometry Basic.planeOrigin = Basic.planeOrigin := fixesOrigin
        _ = Rotation.centralRotation q r firstUnit Basic.planeOrigin :=
          (Rotation.centralRotation_orthogonality q r firstUnit).symm
    · apply Plane.Point.ext
      · simp only [firstImage, q, r, Basic.firstAxisPoint,
          Rotation.centralRotation, Rotation.centralRotationPoint, -eq_self, -iff_self]
        change q = q * 1 - r * 0
        ring1
      · change r = r * 1 + q * 0
        ring1
    · apply Plane.Point.ext
      · change s = q * 0 - r * 1
        calc
          s = -r := rotationOrientation.1
          _ = q * 0 - r * 1 := by ring1
      · change t = r * 0 + q * 1
        calc
          t = q := rotationOrientation.2
          _ = r * 0 + q * 1 := by ring1

end

end Purelib.Geometry.Plane.Isometry.Orthogonality.PlaneIsometry

end
