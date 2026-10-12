module
import Purelib.Geometry.Rotations.Basic
import Purelib.LinearAlgebra.Coordinates3.Matrix
import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.Field.ExplicitOrder.Basic
import Purelib.Algebra.Field.ExplicitOrder.Sign
public import Purelib.Algebra.Quaternion.Ray.Basic
import Purelib.Geometry.Rotations.Cayley.Charts
import Purelib.Geometry.Rotations.Projective.Action
public import Purelib.Geometry.Rotations.Projective.Correspondence
import Purelib.LinearAlgebra.Coordinates3.Vector
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra.Field.ExplicitOrder.Basic

open Purelib.Algebra.Field.ExplicitOrder.Sign

open Purelib.Algebra.Quaternion

open Purelib.Algebra.Quaternion.Ray.Basic

open Purelib.Geometry

open Purelib.Geometry.Rotations.Cayley

open Purelib.Geometry.Rotations.Projective.Action

open Purelib.Geometry.Rotations.Projective.Correspondence

open Purelib.LinearAlgebra

open Purelib.LinearAlgebra.Coordinates3

section
@[expose] public section

/-!
# Rational rotations, section 12.2: ray proportions and spin

Ray equivalence is kept quotient-free: equality carries a displayed positive
scale.  The ordered-field interface includes the finite sign decision and
incompatibility laws actually used to split each projective class into its
two rays.  Products, inverses, the two-to-one rotation map, and the central
ray `(-1:0)` are all represented by executable coordinates.
-/

section

variable {F : Type*} [Purelib.Algebra.Field.ExplicitOrder.Sign.RayOrderedExplicitField F]

-- Keep the original instance owner and its activation throughout this section.
with_weak_namespace _root_.Purelib.Rotations
  /-- Use the displayed ordered field's executable equality decision. -/
  local instance : DecidableEq F := OrderedExplicitField.eq_decidable

section

namespace Purelib.Algebra.Quaternion.Ray.Basic.RayProportion

/-- The rotation represented by a ray. -/
def rotation (proportion : Ray.Basic.RayProportion F) :
  Rotations.Basic.Rotation F :=
  (NonNullProportion.rotation proportion.toNonNullProportion)

/-- Positive-scale equivalent quaternion rays give equal rotation matrices. -/
theorem rotation_respects_equivalent {left right :
  Ray.Basic.RayProportion F}
    (equivalent : left.Equivalent right) :
    left.rotation.matrix = right.rotation.matrix :=
  NonNullProportion.rotationMatrix_respects_equivalent
    (RayProportion.projectivelyEquivalent_of_equivalent equivalent)

/-- Opposite rays lie over the same rotation. -/
theorem rotation_neg (proportion : Ray.Basic.RayProportion F)
  :
    proportion.neg.rotation.matrix = proportion.rotation.matrix := by
  exact NonNullProportion.rotationMatrix_scale (-1)
    RayOrderedExplicitField.neg_one_ne_zero proportion.toNonNullProportion

/-- The ray map preserves quaternion multiplication. -/
theorem rotation_mul (left right : Ray.Basic.RayProportion F)
  :
    (RayProportion.mul left right).rotation.matrix =
      Matrix3.mul left.rotation.matrix right.rotation.matrix :=
  NonNullProportion.rotationMatrix_mul left.toNonNullProportion
    right.toNonNullProportion

/-- Every stored rotation has a computed ray representative. -/
def representativeOfRotation (rotation :
  Rotations.Basic.Rotation F) : Ray.Basic.RayProportion F :=
  ⟨RotationProportion.ofRotation rotation
    RayOrderedExplicitField.two_ne_zero⟩

/-- The computed ray representative gives the original rotation matrix. -/
theorem representativeOfRotation_represents (rotation :
  Rotations.Basic.Rotation F) :
    (representativeOfRotation rotation).rotation.matrix = rotation.matrix :=
  RotationProportion.ofRotation_rotationMatrix rotation
    RayOrderedExplicitField.two_ne_zero

/-- The map from ray proportions to rotations is surjective. -/
theorem rotation_surjective (rotation :
  Rotations.Basic.Rotation F) :
    ∃ proportion : Ray.Basic.RayProportion F,
      proportion.rotation.matrix = rotation.matrix :=
  ⟨representativeOfRotation rotation,
    representativeOfRotation_represents rotation⟩

/-- Exact quotient-free two-to-one statement: equal rotations mean the same ray or the opposite ray, and either
alternative gives equal rotations. -/
theorem rotation_eq_iff_equivalent_or_neg_equivalent
    (left right : Ray.Basic.RayProportion F) :
    left.rotation.matrix = right.rotation.matrix ↔
      left.Equivalent right ∨ left.neg.Equivalent right := by
  constructor
  · intro equalRotation
    have projective := NonNullProportion.equivalent_of_rotationMatrix_eq
      left.toNonNullProportion right.toNonNullProportion
      RayOrderedExplicitField.two_ne_zero equalRotation
    exact RayProportion.equivalent_or_neg_equivalent_of_projectivelyEquivalent left right
      projective
  · rintro (sameRay | oppositeRay)
    · exact rotation_respects_equivalent sameRay
    · calc
        left.rotation.matrix = left.neg.rotation.matrix :=
          (rotation_neg left).symm
        _ = right.rotation.matrix :=
          rotation_respects_equivalent oppositeRay

/-- The two alternatives in a rotation fiber are distinct. -/
theorem rotation_fiber_has_two_distinct_rays (proportion :
  Ray.Basic.RayProportion F) :
    proportion.neg.rotation.matrix = proportion.rotation.matrix ∧
      ¬ proportion.Equivalent proportion.neg :=
  ⟨rotation_neg proportion, RayProportion.not_equivalent_neg proportion⟩

/-- The identity quaternion ray gives the identity rotation matrix. -/
theorem identity_rotation_matrix :
    (RayProportion.identity : Ray.Basic.RayProportion F).rotation.matrix =
      (Matrix3.identity : Coordinates3.Matrix3 F) := by
  let defined : Charts.reciprocalAnchorPathDenominator (1 : F) Coordinates3.Vector.zero ≠ 0 := by
    unfold Charts.reciprocalAnchorPathDenominator
    rw [Coordinates3.Vector.quadrance_zero, add_zero]
    simpa only [one_pow] using
      RayOrderedExplicitField.one_ne_zero (F := F)
  change Charts.reciprocalAnchorPath 1 Coordinates3.Vector.zero defined = Matrix3.identity
  ext <;> unfold Charts.reciprocalAnchorPath Charts.reciprocalAnchorPathDenominator
    Matrix3.add Matrix3.scale Matrix3.identity Matrix3.mul Antisymmetric.anchor
    Coordinates3.Vector.zero Coordinates3.Vector.quadrance Coordinates3.Vector.dot <;>
    simp only [Algebra.Field.ExplicitField.div_eq_mul_inv] <;> ring1

/-- The negative identity quaternion ray gives the identity rotation matrix. -/
theorem negativeIdentity_rotation_matrix :
    (RayProportion.negativeIdentity : Ray.Basic.RayProportion F).rotation.matrix =
      (Matrix3.identity : Coordinates3.Matrix3 F) := by
  calc
    (RayProportion.negativeIdentity : Ray.Basic.RayProportion F).rotation.matrix =
        (RayProportion.identity : Ray.Basic.RayProportion F).rotation.matrix :=
      rotation_neg (RayProportion.identity : Ray.Basic.RayProportion F)
    _ = Matrix3.identity := identity_rotation_matrix

end Purelib.Algebra.Quaternion.Ray.Basic.RayProportion

end

end

end
