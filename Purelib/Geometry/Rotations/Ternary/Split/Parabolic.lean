module

import Purelib.Algebra.Field.Squares
public import Purelib.Geometry.Quadratic.Ternary.RationalMinkowski
public import Purelib.Algebra.Clifford.Split.Matrix
import Purelib.LinearAlgebra.Coordinates2.Matrix
import Purelib.Data.Rat.Fraction.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Algebra.Group.Negation
import Purelib.LinearAlgebra.Coordinates3.Matrix
import Purelib.Algebra.Clifford.Ternary.Action
import Purelib.Algebra.Clifford.Ternary.Basic
import Purelib.Algebra.Quadratic.Ternary.Basic
import Purelib.Algebra.Quadratic.Ternary.Minkowski
import Purelib.Geometry.Quadratic.Ternary.Isometry
import Purelib.Geometry.Quadratic.Ternary.SplitNullConic
import all Purelib.Geometry.Quadratic.Ternary.SplitNullConic

public import Purelib.Geometry.Rotations.Orientation.Handedness
import Purelib.Geometry.Rotations.Ternary.Basic
public import Purelib.Geometry.Rotations.Ternary.Clifford
import Purelib.LinearAlgebra.Coordinates3.Vector
public import Init.Data.Function
import Init.Prelude
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Algebra.Field.ExplicitField
import Purelib.Tactic.Ring

open Purelib.Algebra.Field (ExplicitField)

open Purelib

open Purelib.Algebra.Clifford.Ternary.Basic.TernaryForm

open Purelib.Algebra.Quadratic.Ternary.Basic

open Purelib.Algebra.Quadratic.Ternary.Basic.TernaryForm

open Purelib.Algebra.Quadratic.Ternary.Basic.TernaryForm

open Purelib.Geometry.Rotations.Orientation

open Purelib.Geometry.Rotations.Ternary.Basic.TernaryForm

open Purelib.LinearAlgebra

open Purelib.LinearAlgebra.Coordinates3

section
@[expose] public section
namespace Purelib.Geometry.Rotations.Ternary.Split.Parabolic.MinkowskiClifford
variable {K : Type*} [ExplicitField K]
section

/-- Norm-one split Clifford representative attached to a null axis. -/
def parabolicRaw (oneNonzero : (1 : K) ≠ 0)
  (axis : Coordinates3.Vector K) :
    (TernaryForm.minkowski oneNonzero).EvenClifford :=
  ⟨1, axis⟩
end
end Purelib.Geometry.Rotations.Ternary.Split.Parabolic.MinkowskiClifford

end

section
@[expose] public section
namespace Purelib.Geometry.Rotations.Ternary.Split.Parabolic.MinkowskiClifford
variable {K : Type*} [ExplicitField K]
section

/-- The scalar-one Clifford representative on a Minkowski null axis has norm one. -/
theorem parabolicRaw_norm (oneNonzero : (1 :
  K) ≠ 0)
    (axis : Coordinates3.Vector K)
    (null : (TernaryForm.minkowski oneNonzero).IsNull axis) :
    (EvenClifford.norm (parabolicRaw oneNonzero axis)) = 1
      := by
  unfold parabolicRaw EvenClifford.norm
  unfold TernaryForm.IsNull at null
  rw [null]
  ring1
end
end Purelib.Geometry.Rotations.Ternary.Split.Parabolic.MinkowskiClifford

end

section
@[expose] public section
namespace Purelib.Geometry.Rotations.Ternary.Split.Parabolic.MinkowskiClifford
variable {K : Type*} [ExplicitField K]
section

/-- The total non-null representative, with norm-one certificate cached. -/
def parabolicValue (oneNonzero : (1 : K) ≠
  0) (axis : Coordinates3.Vector K)
    (null : (TernaryForm.minkowski oneNonzero).IsNull axis) :
    (TernaryForm.minkowski oneNonzero).NonNullEvenClifford where
  toEvenClifford := parabolicRaw oneNonzero axis
  normNonzero := by
    rw [parabolicRaw_norm oneNonzero axis null]
    exact oneNonzero
end
end Purelib.Geometry.Rotations.Ternary.Split.Parabolic.MinkowskiClifford

end

section
@[expose] public section
namespace Purelib.Geometry.Rotations.Ternary.Split.Parabolic.MinkowskiClifford
variable {K : Type*} [ExplicitField K]
section

set_option genInjectivity false in
/-- Cached finite invariants of one nonzero null-axis parabolic.

The original null axis determines the retained rotation and fixed-axis,
nonidentity, characteristic and handedness certificates for that same matrix. -/
structure ParabolicCertificate (oneNonzero :
  (1 : K) ≠ 0)
    (twoNonzero : (2 : K) ≠ 0) where
  /-- The retained original Minkowski null axis. -/ axis : Coordinates3.Vector K
  /-- The retained axis has zero Minkowski quadrance. -/ axisNull : (TernaryForm.minkowski oneNonzero).IsNull axis
  /-- The retained axis is a nonzero vector. -/ axisNonzero : axis ≠ Coordinates3.Vector.zero
  /-- The retained special orthogonal parabolic rotation. -/ rotation : (TernaryForm.minkowski
    oneNonzero).SpecialOrthogonal
  /-- The retained rotation is exactly the action of the scalar-one Clifford representative on the retained axis. -/
    rotation_spec :
    rotation = (NonNullEvenClifford.actionRotation
      (Geometry.Rotations.Ternary.Split.Parabolic.MinkowskiClifford.parabolicValue oneNonzero axis axisNull))
  /-- The retained rotation fixes its original null axis. -/
  fixedAxis : (Isometry.act rotation.toIsometry) axis = axis
  /-- The retained parabolic matrix differs from the identity. -/ nonidentityMatrix : rotation.matrix ≠ Matrix3.identity
  /-- The retained rotation has characteristic polynomial `(X - 1)³`. -/ characteristicUnipotent : ∀ X : K,
    Matrix3.characteristicValue rotation.matrix X = (X - 1) ^ 3
  /-- Every perpendicular transversal gives zero handedness for the retained axis and rotation. -/ handednessZero : ∀
    transversal : Coordinates3.Vector K,
    (TernaryForm.minkowski oneNonzero).Perpendicular transversal axis →
      Handedness.handednessDet axis transversal rotation.matrix = 0

constructive_injectivity ParabolicCertificate

end
end Purelib.Geometry.Rotations.Ternary.Split.Parabolic.MinkowskiClifford

end

section
@[expose] public section
namespace Purelib.Geometry.Rotations.Ternary.Split.Parabolic.MinkowskiClifford
variable {K : Type*} [ExplicitField K]
section

/-- Norm-one parabolic representative at a scalar parameter on a fixed null axis. Parameter zero is the Clifford
identity. -/
def parabolicAt (oneNonzero : (1 : K) ≠ 0)
  (axis : Coordinates3.Vector K)
    (null : (TernaryForm.minkowski oneNonzero).IsNull axis)
    (parameter : K) :
    (TernaryForm.minkowski oneNonzero).NonNullEvenClifford :=
  Geometry.Rotations.Ternary.Split.Parabolic.MinkowskiClifford.parabolicValue oneNonzero (Coordinates3.Vector.scale
    parameter axis)
    ((TernaryForm.minkowski oneNonzero).isNull_scale parameter axis null)
end
end Purelib.Geometry.Rotations.Ternary.Split.Parabolic.MinkowskiClifford

end

section
@[expose] public section
namespace Purelib.Geometry.Rotations.Ternary.Split.Parabolic.MinkowskiClifford
variable {K : Type*} [ExplicitField K]
section

/-- Conjugation negates the scalar parameter of the null-axis family. -/
theorem parabolicAt_conjugate (oneNonzero :
  (1 : K) ≠ 0)
    (axis : Coordinates3.Vector K)
    (null : (TernaryForm.minkowski oneNonzero).IsNull axis)
    (parameter : K) :
    (NonNullEvenClifford.conjugate (parabolicAt oneNonzero
      axis null parameter)) =
      parabolicAt oneNonzero axis null (-parameter) := by
  apply NonNullEvenClifford.ext
  · rfl
  · ext <;> unfold parabolicAt
      Geometry.Rotations.Ternary.Split.Parabolic.MinkowskiClifford.parabolicValue
      parabolicRaw
      NonNullEvenClifford.conjugate
      EvenClifford.conjugate Coordinates3.Vector.neg Coordinates3.Vector.scale <;> ring1
end
end Purelib.Geometry.Rotations.Ternary.Split.Parabolic.MinkowskiClifford

end

section
@[expose] public section
namespace Purelib.Geometry.Rotations.Ternary.Split.Parabolic.MinkowskiClifford
variable {K : Type*} [ExplicitField K]
section

/-- Multiplication on one null line is addition of its scalar parameters. -/
theorem parabolicAt_mul (oneNonzero : (1 :
  K) ≠ 0)
    (axis : Coordinates3.Vector K)
    (null : (TernaryForm.minkowski oneNonzero).IsNull axis)
    (left right : K) :
    NonNullEvenClifford.mul
        (parabolicAt oneNonzero axis null left)
        (parabolicAt oneNonzero axis null right) =
      parabolicAt oneNonzero axis null (left + right) := by
  let form := TernaryForm.minkowski oneNonzero
  have nullBilinear : form.bilinear axis axis = 0 := by
    exact null
  have raw :
      EvenClifford.mul
          (parabolicRaw oneNonzero
            (Coordinates3.Vector.scale left axis))
          (parabolicRaw oneNonzero
            (Coordinates3.Vector.scale right axis)) =
        parabolicRaw oneNonzero (Coordinates3.Vector.scale
          (left + right) axis) := by
    apply EvenClifford.ext
    · unfold EvenClifford.mul
        EvenClifford.productScalar parabolicRaw
      rw [form.bilinear_scale_left, form.bilinear_scale_right]
      change 1 * 1 - form.determinant *
        (left * (right * form.bilinear axis axis)) = 1
      rw [nullBilinear]
      ring1
    · unfold EvenClifford.mul
        EvenClifford.productVector parabolicRaw
      rw [form.cliffordCross_scale_left,
        form.cliffordCross_scale_right,
        form.cliffordCross_self, Coordinates3.Vector.scale_zero]
      ext <;> unfold Coordinates3.Vector.sub Coordinates3.Vector.add Coordinates3.Vector.scale Coordinates3.Vector.zero
        <;> ring1
  apply NonNullEvenClifford.ext
  · exact congrArg EvenClifford.scalar raw
  · exact congrArg EvenClifford.vector raw
end
end Purelib.Geometry.Rotations.Ternary.Split.Parabolic.MinkowskiClifford

end

section
@[expose] public section
namespace Purelib.Geometry.Rotations.Ternary.Split.Parabolic.MinkowskiClifford
variable {K : Type*} [ExplicitField K]
section

/-- The null-axis representative at parameter zero is the Clifford identity. -/
@[simp] theorem parabolicAt_zero (oneNonzero
  : (1 : K) ≠ 0)
    (axis : Coordinates3.Vector K)
    (null : (TernaryForm.minkowski oneNonzero).IsNull axis) :
    parabolicAt oneNonzero axis null 0 =
      NonNullEvenClifford.identity
        (TernaryForm.minkowski oneNonzero) := by
  apply NonNullEvenClifford.ext
  · rfl
  · exact Coordinates3.Vector.zero_scale axis
end
end Purelib.Geometry.Rotations.Ternary.Split.Parabolic.MinkowskiClifford

end

section
@[expose] public section
namespace Purelib.Geometry.Rotations.Ternary.Split.Parabolic.MinkowskiClifford
variable {K : Type*} [ExplicitField K]
section

/-- The special-orthogonal member at one scalar parameter. -/
def parabolicRotationAt (oneNonzero : (1 :
  K) ≠ 0)
    (axis : Coordinates3.Vector K)
    (null : (TernaryForm.minkowski oneNonzero).IsNull axis)
    (parameter : K) :
    (TernaryForm.minkowski oneNonzero).SpecialOrthogonal :=
  (NonNullEvenClifford.actionRotation (parabolicAt
    oneNonzero axis null parameter))
end
end Purelib.Geometry.Rotations.Ternary.Split.Parabolic.MinkowskiClifford

end

section
@[expose] public section
namespace Purelib.Geometry.Rotations.Ternary.Split.Parabolic.MinkowskiClifford
variable {K : Type*} [ExplicitField K]
section

set_option genInjectivity false in
/-- An explicit additive one-parameter subgroup on a fixed nonzero null axis.

The original fixed axis supplies every retained rotation. The zero, addition,
inversion and injectivity certificates concern the same parameterized family. -/
structure NullAxisParabolicFamily
  [DecidableEq K]
    (oneNonzero : (1 : K) ≠ 0) (twoNonzero : (2 : K) ≠ 0) where
  /-- The retained original Minkowski null axis. -/ axis : Coordinates3.Vector K
  /-- The retained axis has zero Minkowski quadrance. -/ axisNull : (TernaryForm.minkowski oneNonzero).IsNull axis
  /-- The retained axis is a nonzero vector. -/ axisNonzero : axis ≠ Coordinates3.Vector.zero
  /-- The retained special orthogonal rotation at each scalar parameter. -/ rotation : K → (TernaryForm.minkowski
    oneNonzero).SpecialOrthogonal
  /-- Every family member is exactly the stated parameterized null-axis Clifford rotation. -/ rotation_spec : ∀
    parameter : K,
    rotation parameter = parabolicRotationAt oneNonzero
      axis axisNull parameter
  /-- The family member at zero is the identity. -/ rotation_zero : rotation 0 =
    SpecialOrthogonal.identity
      (TernaryForm.minkowski oneNonzero)
  /-- Parameter addition corresponds to the row-order product of rotations. -/ rotation_add : ∀ left right : K,
    rotation (left + right) =
      SpecialOrthogonal.mul (rotation left) (rotation right)
  /-- Parameter negation corresponds to rotation inversion. -/ rotation_neg : ∀ parameter : K,
    rotation (-parameter) =
      SpecialOrthogonal.inverse (rotation parameter)
  /-- Every retained family member fixes the original null axis. -/
  fixedAxis : ∀ parameter : K, (Isometry.act (rotation
    parameter).toIsometry) axis = axis
  /-- Every parameter has characteristic polynomial `(X - 1)³`. -/ characteristicUnipotent : ∀ parameter X : K,
    Matrix3.characteristicValue (rotation parameter).matrix X = (X - 1) ^ 3
  /-- Every parameter and perpendicular transversal give zero handedness on the retained axis. -/ handednessZero : ∀
    (parameter : K) (transversal : Coordinates3.Vector K),
    (TernaryForm.minkowski oneNonzero).Perpendicular transversal axis →
      Handedness.handednessDet axis transversal (rotation parameter).matrix = 0
  /-- Every nonzero parameter gives a matrix different from the identity. -/ nonidentity : ∀ parameter : K, parameter ≠
    0 →
    (rotation parameter).matrix ≠ Matrix3.identity
  /-- The retained parameter-to-rotation map is injective. -/ injective : Function.Injective rotation

constructive_injectivity NullAxisParabolicFamily

end
end Purelib.Geometry.Rotations.Ternary.Split.Parabolic.MinkowskiClifford

end

section
@[expose] public section
namespace Purelib.Geometry.Rotations.Ternary.Split.Parabolic.MinkowskiClifford
variable {K : Type*} [ExplicitField K]
section

/-- Adding null-axis parameters gives the product of the corresponding rotations. -/
theorem parabolicRotationAt_add (oneNonzero
  : (1 : K) ≠ 0)
    (axis : Coordinates3.Vector K)
    (null : (TernaryForm.minkowski oneNonzero).IsNull axis)
    (left right : K) :
    parabolicRotationAt oneNonzero axis null (left + right)
      =
      SpecialOrthogonal.mul
        (parabolicRotationAt oneNonzero axis null left)
        (parabolicRotationAt oneNonzero axis null right) :=
          by
  unfold parabolicRotationAt
  calc
    (NonNullEvenClifford.actionRotation (parabolicAt
      oneNonzero axis null (left + right))) =
        (NonNullEvenClifford.actionRotation (NonNullEvenClifford.mul
          (parabolicAt oneNonzero axis null left)
          (parabolicAt oneNonzero axis null right))) :=
      congrArg NonNullEvenClifford.actionRotation
        (parabolicAt_mul oneNonzero axis null left
          right).symm
    _ = _ := NonNullEvenClifford.actionRotation_mul _ _
end
end Purelib.Geometry.Rotations.Ternary.Split.Parabolic.MinkowskiClifford

end

section
@[expose] public section
namespace Purelib.Geometry.Rotations.Ternary.Split.Parabolic.MinkowskiClifford
variable {K : Type*} [ExplicitField K]
section

/-- Negating the null-axis parameter gives the inverse rotation. -/
theorem parabolicRotationAt_neg (oneNonzero
  : (1 : K) ≠ 0)
    (axis : Coordinates3.Vector K)
    (null : (TernaryForm.minkowski oneNonzero).IsNull axis)
    (parameter : K) :
    parabolicRotationAt oneNonzero axis null (-parameter) =
      SpecialOrthogonal.inverse
        (parabolicRotationAt oneNonzero axis null
          parameter) := by
  unfold parabolicRotationAt
  calc
    (NonNullEvenClifford.actionRotation (parabolicAt
      oneNonzero axis null (-parameter))) =
        (NonNullEvenClifford.actionRotation (NonNullEvenClifford.conjugate
          (parabolicAt oneNonzero axis null parameter))) :=
      congrArg NonNullEvenClifford.actionRotation
        (parabolicAt_conjugate oneNonzero axis null
          parameter).symm
    _ = _ :=
      NonNullEvenClifford.actionRotation_conjugate _
end
end Purelib.Geometry.Rotations.Ternary.Split.Parabolic.MinkowskiClifford

end

section
@[expose] public section
namespace Purelib.Geometry.Rotations.Ternary.Split.Parabolic.MinkowskiClifford
variable {K : Type*} [ExplicitField K]
section

/-- The null-axis rotation at parameter zero is the identity. -/
@[simp] theorem parabolicRotationAt_zero
  (oneNonzero : (1 : K) ≠ 0)
    (axis : Coordinates3.Vector K)
    (null : (TernaryForm.minkowski oneNonzero).IsNull axis) :
    parabolicRotationAt oneNonzero axis null 0 =
      SpecialOrthogonal.identity
        (TernaryForm.minkowski oneNonzero) := by
  unfold parabolicRotationAt
  rw [parabolicAt_zero,
    NonNullEvenClifford.actionRotation_identity]
end
end Purelib.Geometry.Rotations.Ternary.Split.Parabolic.MinkowskiClifford

end

section
@[expose] public section
namespace Purelib.Geometry.Rotations.Ternary.Split.Parabolic.MinkowskiClifford
variable {K : Type*} [ExplicitField K]
section

/-- Explicit action formula for the null-axis, scalar-one family. -/
theorem parabolic_action (oneNonzero : (1 :
  K) ≠ 0)
    (axis vector : Coordinates3.Vector K)
    (null : (TernaryForm.minkowski oneNonzero).IsNull axis) :
    (NonNullEvenClifford.action (Geometry.Rotations.Ternary.Split.Parabolic.MinkowskiClifford.parabolicValue oneNonzero
      axis null)) vector =
      Coordinates3.Vector.add
        (Coordinates3.Vector.add vector
          (Coordinates3.Vector.scale
            (-2 *
              (TernaryForm.minkowski oneNonzero).bilinear vector axis)
            axis))
        (Coordinates3.Vector.scale (-2)
          ((TernaryForm.minkowski oneNonzero).cliffordCross vector axis)) := by
  have oneInverse : (1 : K)⁻¹ = 1 := by
    have cancel := ExplicitField.mul_inv_cancel (1 : K) oneNonzero
    simpa only [one_mul] using cancel
  have nullQuadrance :
      (TernaryForm.minkowski oneNonzero).quadrance axis = 0 := null
  unfold NonNullEvenClifford.action
  change
    Coordinates3.Vector.scale (EvenClifford.norm
      (parabolicRaw oneNonzero axis))⁻¹
        ((EvenClifford.actionNumerator (parabolicRaw
          oneNonzero axis)) vector) = _
  rw [parabolicRaw_norm oneNonzero axis null, oneInverse,
    Coordinates3.Vector.one_scale]
  unfold EvenClifford.actionNumerator parabolicRaw
  rw [nullQuadrance, TernaryForm.minkowski_determinant]
  ext <;> unfold Coordinates3.Vector.add Coordinates3.Vector.scale <;> ring1
end
end Purelib.Geometry.Rotations.Ternary.Split.Parabolic.MinkowskiClifford

end

section
@[expose] public section
namespace Purelib.Geometry.Rotations.Ternary.Split.Parabolic.MinkowskiClifford
variable {K : Type*} [ExplicitField K]
section

/-- Every member of the parameterized parabolic family fixes the original null axis. -/
theorem parabolicRotationAt_fixedAxis
  (oneNonzero : (1 : K) ≠ 0)
    (axis : Coordinates3.Vector K)
    (null : (TernaryForm.minkowski oneNonzero).IsNull axis)
    (parameter : K) :
    (Isometry.act
        (parabolicRotationAt oneNonzero axis null
      parameter).toIsometry) axis = axis := by
  unfold parabolicRotationAt
  rw [NonNullEvenClifford.actionRotation_act]
  unfold parabolicAt
  rw [parabolic_action]
  have nullBilinear :
      (TernaryForm.minkowski oneNonzero).bilinear axis axis = 0 := null
  rw [(TernaryForm.minkowski oneNonzero).bilinear_scale_right,
    nullBilinear, mul_zero,
    (TernaryForm.minkowski oneNonzero).cliffordCross_scale_right,
    (TernaryForm.minkowski oneNonzero).cliffordCross_self]
  ext <;> unfold Coordinates3.Vector.add Coordinates3.Vector.scale Coordinates3.Vector.zero <;> ring1
end
end Purelib.Geometry.Rotations.Ternary.Split.Parabolic.MinkowskiClifford

end

section
@[expose] public section
namespace Purelib.Geometry.Rotations.Ternary.Split.Parabolic.MinkowskiClifford
variable {K : Type*} [ExplicitField K]
section

/-- The action on the first coordinate vector exposes all three axis coordinates and is used to certify that a nonzero
null axis is nontrivial. -/
theorem parabolic_action_firstBasis
  (oneNonzero : (1 : K) ≠ 0)
    (axis : Coordinates3.Vector K)
    (null : (TernaryForm.minkowski oneNonzero).IsNull axis) :
    (NonNullEvenClifford.action (Geometry.Rotations.Ternary.Split.Parabolic.MinkowskiClifford.parabolicValue oneNonzero
      axis null))
        (⟨1, 0, 0⟩ : Coordinates3.Vector K) =
      ⟨1 - 2 * axis.t ^ 2,
        -2 * axis.t * axis.r - 2 * axis.s,
        -2 * axis.t * axis.s - 2 * axis.r⟩ := by
  rw [parabolic_action]
  ext <;> unfold TernaryForm.bilinear TernaryForm.minkowski
    TernaryForm.ofMatrix TernaryForm.cliffordCross Matrix3.adjugate
    Matrix3.rowMul Coordinates3.Vector.dot Coordinates3.Vector.cross Coordinates3.Vector.add Coordinates3.Vector.scale
      <;> ring1
end
end Purelib.Geometry.Rotations.Ternary.Split.Parabolic.MinkowskiClifford

end

section
@[expose] public section
namespace Purelib.Geometry.Rotations.Ternary.Split.Parabolic.MinkowskiClifford
variable {K : Type*} [ExplicitField K]
section

/-- The scalar-one null-axis Clifford action fixes its axis. -/
theorem parabolic_fixedAxis (oneNonzero : (1
  : K) ≠ 0)
    (axis : Coordinates3.Vector K)
    (null : (TernaryForm.minkowski oneNonzero).IsNull axis) :
    (NonNullEvenClifford.action (Geometry.Rotations.Ternary.Split.Parabolic.MinkowskiClifford.parabolicValue oneNonzero
      axis null)) axis = axis := by
  rw [parabolic_action]
  have nullQuadrance :
      (TernaryForm.minkowski oneNonzero).quadrance axis = 0 := null
  have nullBilinear :
      (TernaryForm.minkowski oneNonzero).bilinear axis axis = 0 :=
    nullQuadrance
  rw [nullBilinear,
    TernaryForm.cliffordCross_self,
    Coordinates3.Vector.scale_zero, Coordinates3.Vector.add_zero]
  ext <;> unfold Coordinates3.Vector.add Coordinates3.Vector.scale <;> ring1
end
end Purelib.Geometry.Rotations.Ternary.Split.Parabolic.MinkowskiClifford

end

section
@[expose] public section
namespace Purelib.Geometry.Rotations.Ternary.Split.Parabolic.MinkowskiClifford
variable {K : Type*} [ExplicitField K]
section

/-- Every perpendicular transversal has zero frame-handedness for the null-axis family. -/
theorem parabolic_handedness_zero
  (oneNonzero : (1 : K) ≠ 0)
    (axis transversal : Coordinates3.Vector K)
    (null : (TernaryForm.minkowski oneNonzero).IsNull axis)
    (perpendicular :
      (TernaryForm.minkowski oneNonzero).Perpendicular transversal axis) :
    Handedness.handednessDet axis transversal
      (NonNullEvenClifford.actionMatrix (Geometry.Rotations.Ternary.Split.Parabolic.MinkowskiClifford.parabolicValue
        oneNonzero axis null)) = 0 := by
  let form := TernaryForm.minkowski oneNonzero
  have crossQuadrance := form.quadrance_cliffordCross transversal axis
  have nullQuadrance : form.quadrance axis = 0 := null
  have perpendicularBilinear : form.bilinear transversal axis = 0 :=
    perpendicular
  rw [nullQuadrance, perpendicularBilinear] at crossQuadrance
  have crossQuadranceZero :
      form.quadrance (form.cliffordCross transversal axis) = 0 := by
    calc
      form.quadrance (form.cliffordCross transversal axis) =
          form.determinant *
            (form.quadrance transversal * 0 - 0 ^ 2) := crossQuadrance
      _ = 0 := by ring1
  have triple := form.bilinear_cliffordCross axis transversal
    (form.cliffordCross transversal axis)
  rw [form.cliffordCross_anticomm axis transversal,
    form.bilinear_neg_left] at triple
  unfold TernaryForm.quadrance at crossQuadranceZero
  rw [crossQuadranceZero, TernaryForm.minkowski_determinant] at triple
  rw [neg_zero] at triple
  have determinantZero :
      Coordinates3.Vector.determinant axis transversal
        (form.cliffordCross transversal axis) = 0 := by
    calc
      Coordinates3.Vector.determinant axis transversal
          (form.cliffordCross transversal axis) =
          -((-1 : K) * Coordinates3.Vector.determinant axis transversal
            (form.cliffordCross transversal axis)) := by ring1
      _ = -0 := by rw [← triple]
      _ = 0 := by ring1
  unfold Handedness.handednessDet
  rw [(NonNullEvenClifford.rowMul_actionMatrix
    (Geometry.Rotations.Ternary.Split.Parabolic.MinkowskiClifford.parabolicValue oneNonzero axis null)),
    parabolic_action]
  unfold TernaryForm.Perpendicular at perpendicular
  rw [perpendicular, mul_zero, Coordinates3.Vector.zero_scale,
    Coordinates3.Vector.add_zero, Coordinates3.Vector.determinant_add_third,
    Coordinates3.Vector.determinant_repeat_second,
    Coordinates3.Vector.determinant_scale_third, determinantZero]
  ring1
end
end Purelib.Geometry.Rotations.Ternary.Split.Parabolic.MinkowskiClifford

end

section
@[expose] public section
namespace Purelib.Geometry.Rotations.Ternary.Split.Parabolic.MinkowskiClifford
variable {K : Type*} [ExplicitField K]
section

/-- Every parameterized parabolic has zero handedness determinant on a transversal perpendicular to its null axis. -/
theorem parabolicRotationAt_handedness_zero
  [DecidableEq K]
    (oneNonzero : (1 : K) ≠ 0)
    (axis transversal : Coordinates3.Vector K)
    (null : (TernaryForm.minkowski oneNonzero).IsNull axis)
    (perpendicular :
      (TernaryForm.minkowski oneNonzero).Perpendicular transversal axis)
    (parameter : K) :
    Handedness.handednessDet axis transversal
      (parabolicRotationAt oneNonzero axis null
        parameter).matrix = 0 := by
  by_cases parameterZero : parameter = 0
  · subst parameter
    rw [parabolicRotationAt_zero]
    unfold Handedness.handednessDet SpecialOrthogonal.identity
      Isometry.identity
    rw [Matrix3.rowMul_identity, Coordinates3.Vector.determinant_repeat_second]
  · have scaledNull :=
      (TernaryForm.minkowski oneNonzero).isNull_scale parameter axis null
    have scaledPerpendicular :=
      (TernaryForm.minkowski oneNonzero).perpendicular_scale_right
        parameter transversal axis perpendicular
    have scaledZero := Geometry.Rotations.Ternary.Split.Parabolic.MinkowskiClifford.parabolic_handedness_zero oneNonzero
      (Coordinates3.Vector.scale parameter axis) transversal scaledNull scaledPerpendicular
    have factor :
        Handedness.handednessDet (Coordinates3.Vector.scale parameter axis) transversal
            (parabolicRotationAt oneNonzero axis null
              parameter).matrix =
          parameter * Handedness.handednessDet axis transversal
            (parabolicRotationAt oneNonzero axis null
              parameter).matrix := by
      unfold Handedness.handednessDet Coordinates3.Vector.determinant Coordinates3.Vector.scale
      ring1
    apply (fun {K : Type _} [ExplicitField K] {factor value : K} (factorNonzero : factor ≠ 0)
      (productZero : factor * value = 0) => (ExplicitField.eq_zero_of_mul_eq_zero_left (R := K)
      (factor := factor) (value := value) factorNonzero productZero : value = 0))
      parameterZero
    rw [← factor]
    exact scaledZero
end
end Purelib.Geometry.Rotations.Ternary.Split.Parabolic.MinkowskiClifford

end

section
@[expose] public section
namespace Purelib.Geometry.Rotations.Ternary.Split.Parabolic.MinkowskiClifford
variable {K : Type*} [ExplicitField K]
section

/-- A nonzero null axis gives a nonidentity parabolic action in characteristic different from two. -/
theorem parabolic_nonidentity [DecidableEq
  K]
    (oneNonzero : (1 : K) ≠ 0) (twoNonzero : (2 : K) ≠ 0)
    (axis : Coordinates3.Vector K)
    (null : (TernaryForm.minkowski oneNonzero).IsNull axis)
    (axisNonzero : axis ≠ Coordinates3.Vector.zero) :
    (NonNullEvenClifford.actionMatrix (Geometry.Rotations.Ternary.Split.Parabolic.MinkowskiClifford.parabolicValue
      oneNonzero axis null)) ≠
      Matrix3.identity := by
  intro identityAction
  have firstBasisFixed :
      (NonNullEvenClifford.action (Geometry.Rotations.Ternary.Split.Parabolic.MinkowskiClifford.parabolicValue
        oneNonzero axis null))
          (⟨1, 0, 0⟩ : Coordinates3.Vector K) =
        (⟨1, 0, 0⟩ : Coordinates3.Vector K) := by
    calc
      (NonNullEvenClifford.action (Geometry.Rotations.Ternary.Split.Parabolic.MinkowskiClifford.parabolicValue
        oneNonzero axis null)) ⟨1, 0, 0⟩ =
          Matrix3.rowMul (⟨1, 0, 0⟩ : Coordinates3.Vector K)
            (NonNullEvenClifford.actionMatrix
              (Geometry.Rotations.Ternary.Split.Parabolic.MinkowskiClifford.parabolicValue oneNonzero axis null)) :=
        ((NonNullEvenClifford.rowMul_actionMatrix
          (Geometry.Rotations.Ternary.Split.Parabolic.MinkowskiClifford.parabolicValue oneNonzero axis null))
          ⟨1, 0, 0⟩).symm
      _ = Matrix3.rowMul (⟨1, 0, 0⟩ : Coordinates3.Vector K)
          Matrix3.identity := by rw [identityAction]
      _ = ⟨1, 0, 0⟩ := Matrix3.rowMul_identity ⟨1, 0, 0⟩
  rw [parabolic_action_firstBasis] at firstBasisFixed
  have firstEq := congrArg Coordinates3.Vector.t firstBasisFixed
  have secondEq := congrArg Coordinates3.Vector.r firstBasisFixed
  have thirdEq := congrArg Coordinates3.Vector.s firstBasisFixed
  change 1 - 2 * axis.t ^ 2 = 1 at firstEq
  change -2 * axis.t * axis.r - 2 * axis.s = 0 at secondEq
  change -2 * axis.t * axis.s - 2 * axis.r = 0 at thirdEq
  have twiceTSquare : 2 * axis.t ^ 2 = 0 := by
    calc
      2 * axis.t ^ 2 = 1 - (1 - 2 * axis.t ^ 2) := by ring1
      _ = 0 := by rw [firstEq]; ring1
  have tSquareZero :=
    (fun {K : Type _} [ExplicitField K] {factor value : K} (factorNonzero : factor ≠ 0)
      (productZero : factor * value = 0) => (ExplicitField.eq_zero_of_mul_eq_zero_left (R := K)
      (factor := factor) (value := value) factorNonzero productZero : value = 0))
    twoNonzero twiceTSquare
  have tZero := (fun {K : Type _} [ExplicitField K] [DecidableEq K] (value : K) (squareZero :
    value ^ 2 = 0) => (Purelib.Algebra.Field.Squares.eq_zero_of_square_eq_zero (K := K) value squareZero : value = 0))
    axis.t tSquareZero
  letI : SubNegZeroMonoid K := Purelib.Algebra.Group.Negation.subNegZeroMonoid
  have twiceS : 2 * axis.s = 0 := by
    calc
      2 * axis.s = -(-2 * axis.t * axis.r - 2 * axis.s) := by
        rewrite [tZero]
        ring1
      _ = -(0 : K) := congrArg (fun value : K => -value) secondEq
      _ = 0 := neg_zero
  have twiceR : 2 * axis.r = 0 := by
    calc
      2 * axis.r = -(-2 * axis.t * axis.s - 2 * axis.r) := by
        rewrite [tZero]
        ring1
      _ = -(0 : K) := congrArg (fun value : K => -value) thirdEq
      _ = 0 := neg_zero
  have sZero :=
    (fun {K : Type _} [ExplicitField K] {factor value : K} (factorNonzero : factor ≠ 0)
      (productZero : factor * value = 0) => (ExplicitField.eq_zero_of_mul_eq_zero_left (R := K)
      (factor := factor) (value := value) factorNonzero productZero : value = 0))
    twoNonzero twiceS
  have rZero :=
    (fun {K : Type _} [ExplicitField K] {factor value : K} (factorNonzero : factor ≠ 0)
      (productZero : factor * value = 0) => (ExplicitField.eq_zero_of_mul_eq_zero_left (R := K)
      (factor := factor) (value := value) factorNonzero productZero : value = 0))
    twoNonzero twiceR
  apply axisNonzero
  apply Coordinates3.Vector.ext
  · exact tZero
  · exact rZero
  · exact sZero
end
end Purelib.Geometry.Rotations.Ternary.Split.Parabolic.MinkowskiClifford

end

section
@[expose] public section
namespace Purelib.Geometry.Rotations.Ternary.Split.Parabolic.MinkowskiClifford
variable {K : Type*} [ExplicitField K]
section

/-- A nonzero parameter on a nonzero null axis gives a nonidentity parabolic rotation. -/
theorem parabolicRotationAt_nonidentity
  [DecidableEq K]
    (oneNonzero : (1 : K) ≠ 0) (twoNonzero : (2 : K) ≠ 0)
    (axis : Coordinates3.Vector K)
    (null : (TernaryForm.minkowski oneNonzero).IsNull axis)
    (axisNonzero : axis ≠ Coordinates3.Vector.zero)
    (parameter : K) (parameterNonzero : parameter ≠ 0) :
    (parabolicRotationAt oneNonzero axis null
      parameter).matrix ≠
      Matrix3.identity := by
  apply Geometry.Rotations.Ternary.Split.Parabolic.MinkowskiClifford.parabolic_nonidentity oneNonzero twoNonzero
    (Coordinates3.Vector.scale parameter axis)
    ((TernaryForm.minkowski oneNonzero).isNull_scale parameter axis null)
  intro scaledZero
  apply axisNonzero
  apply Coordinates3.Vector.ext
  · have coordinate := congrArg Coordinates3.Vector.t scaledZero
    exact (fun {K : Type _} [ExplicitField K] {factor value : K} (factorNonzero : factor ≠ 0)
      (productZero : factor * value = 0) => (ExplicitField.eq_zero_of_mul_eq_zero_left (R := K)
      (factor := factor) (value := value) factorNonzero productZero : value = 0))
      parameterNonzero coordinate
  · have coordinate := congrArg Coordinates3.Vector.r scaledZero
    exact (fun {K : Type _} [ExplicitField K] {factor value : K} (factorNonzero : factor ≠ 0)
      (productZero : factor * value = 0) => (ExplicitField.eq_zero_of_mul_eq_zero_left (R := K)
      (factor := factor) (value := value) factorNonzero productZero : value = 0))
      parameterNonzero coordinate
  · have coordinate := congrArg Coordinates3.Vector.s scaledZero
    exact (fun {K : Type _} [ExplicitField K] {factor value : K} (factorNonzero : factor ≠ 0)
      (productZero : factor * value = 0) => (ExplicitField.eq_zero_of_mul_eq_zero_left (R := K)
      (factor := factor) (value := value) factorNonzero productZero : value = 0))
      parameterNonzero coordinate
end
end Purelib.Geometry.Rotations.Ternary.Split.Parabolic.MinkowskiClifford

end

section
@[expose] public section
namespace Purelib.Geometry.Rotations.Ternary.Split.Parabolic.MinkowskiClifford
variable {K : Type*} [ExplicitField K]
section

/-- Distinct parameters on a fixed nonzero null axis give distinct parabolic rotations when two is nonzero. -/
theorem parabolicRotationAt_injective
  [DecidableEq K]
    (oneNonzero : (1 : K) ≠ 0) (twoNonzero : (2 : K) ≠ 0)
    (axis : Coordinates3.Vector K)
    (null : (TernaryForm.minkowski oneNonzero).IsNull axis)
    (axisNonzero : axis ≠ Coordinates3.Vector.zero) :
    Function.Injective (parabolicRotationAt oneNonzero axis
      null) := by
  intro left right rotationsEqual
  by_cases parametersEqual : left = right
  · exact parametersEqual
  · have differenceNonzero : left + (-right) ≠ 0 := by
      intro differenceZero
      apply parametersEqual
      calc
        left = (left + (-right)) + right := by ring1
        _ = 0 + right := by rw [differenceZero]
        _ = right := by ring1
    have differenceIdentity :
        parabolicRotationAt oneNonzero axis null (left +
          (-right)) =
          SpecialOrthogonal.identity
            (TernaryForm.minkowski oneNonzero) := by
      calc
        parabolicRotationAt oneNonzero axis null (left +
          (-right)) =
            SpecialOrthogonal.mul
              (parabolicRotationAt oneNonzero axis null
                left)
              (parabolicRotationAt oneNonzero axis null
                (-right)) :=
          parabolicRotationAt_add oneNonzero axis null left
            (-right)
        _ = SpecialOrthogonal.mul
              (parabolicRotationAt oneNonzero axis null
                right)
              (SpecialOrthogonal.inverse
                (parabolicRotationAt oneNonzero axis null
                  right)) := by
          rw [rotationsEqual,
            parabolicRotationAt_neg oneNonzero axis null
              right]
        _ = SpecialOrthogonal.identity
              (TernaryForm.minkowski oneNonzero) :=
          SpecialOrthogonal.mul_inverse _
    have differenceMatrixIdentity := congrArg
      (fun rotation :
        (TernaryForm.minkowski oneNonzero).SpecialOrthogonal =>
          rotation.matrix)
      differenceIdentity
    exact False.elim
      ((parabolicRotationAt_nonidentity oneNonzero
        twoNonzero axis null
        axisNonzero (left + (-right)) differenceNonzero)
        differenceMatrixIdentity)
end
end Purelib.Geometry.Rotations.Ternary.Split.Parabolic.MinkowskiClifford

end

section
@[expose] public section
namespace Purelib.Geometry.Rotations.Ternary.Split.Parabolic.MinkowskiClifford
variable {K : Type*} [ExplicitField K]
section

/-- The null-axis parabolic action matrix has trace three. -/
theorem parabolic_trace (oneNonzero : (1 :
  K) ≠ 0)
    (axis : Coordinates3.Vector K)
    (null : (TernaryForm.minkowski oneNonzero).IsNull axis) :
    Matrix3.trace (NonNullEvenClifford.actionMatrix
      (Geometry.Rotations.Ternary.Split.Parabolic.MinkowskiClifford.parabolicValue oneNonzero axis null)) = 3 := by
  have oneInverse : (1 : K)⁻¹ = 1 := by
    have cancel := ExplicitField.mul_inv_cancel (1 : K) oneNonzero
    simpa only [one_mul] using cancel
  have nullQuadrance :
      (TernaryForm.minkowski oneNonzero).quadrance axis = 0 := null
  have nullBilinear :
      (TernaryForm.minkowski oneNonzero).bilinear axis axis = 0 :=
    nullQuadrance
  unfold NonNullEvenClifford.actionMatrix
  change Matrix3.trace
    (Matrix3.scale (EvenClifford.norm (parabolicRaw
      oneNonzero axis))⁻¹
      (EvenClifford.actionNumeratorMatrix (parabolicRaw
        oneNonzero axis))) = 3
  rw [parabolicRaw_norm oneNonzero axis null, oneInverse,
    Matrix3.one_scale]
  unfold EvenClifford.actionNumeratorMatrix parabolicRaw
  rw [Matrix3.trace_add, Matrix3.trace_add,
    Matrix3.trace_scale, Matrix3.trace_identity,
    Matrix3.trace_scale, Matrix3.trace_outer,
    Coordinates3.Vector.dot_comm, ← TernaryForm.bilinear_eq_dot_dual,
    Matrix3.trace_scale,
    TernaryForm.trace_actionSkew,
    nullQuadrance, nullBilinear,
    TernaryForm.minkowski_determinant]
  ring1
end
end Purelib.Geometry.Rotations.Ternary.Split.Parabolic.MinkowskiClifford

end

section
@[expose] public section
namespace Purelib.Geometry.Rotations.Ternary.Split.Parabolic.MinkowskiClifford
variable {K : Type*} [ExplicitField K]
section

/-- The null-axis family is unipotent: its displayed characteristic polynomial is `(X-1)³`. -/
theorem parabolic_characteristic (oneNonzero
  : (1 : K) ≠ 0)
    (axis : Coordinates3.Vector K)
    (null : (TernaryForm.minkowski oneNonzero).IsNull axis) (X : K) :
    Matrix3.characteristicValue
        (NonNullEvenClifford.actionMatrix (Geometry.Rotations.Ternary.Split.Parabolic.MinkowskiClifford.parabolicValue
          oneNonzero axis null)) X =
      (X - 1) ^ 3 := by
  let form := TernaryForm.minkowski oneNonzero
  let value := Geometry.Rotations.Ternary.Split.Parabolic.MinkowskiClifford.parabolicValue oneNonzero axis null
  have negNull : form.IsNull (Coordinates3.Vector.neg axis) := by
    unfold form TernaryForm.IsNull TernaryForm.quadrance
    rw [TernaryForm.bilinear_neg_left,
      TernaryForm.bilinear_neg_right]
    calc
      - -(TernaryForm.minkowski oneNonzero).bilinear axis axis =
          (TernaryForm.minkowski oneNonzero).bilinear axis axis := by
        ring1
      _ = 0 := null
  have conjugateEq :
      (NonNullEvenClifford.conjugate value) =
        Geometry.Rotations.Ternary.Split.Parabolic.MinkowskiClifford.parabolicValue oneNonzero (Coordinates3.Vector.neg
        axis) negNull := by
    apply NonNullEvenClifford.ext
    · rfl
    · rfl
  have inverseMatrixEq := congrArg
    (fun rotation : form.SpecialOrthogonal => rotation.matrix)
    (NonNullEvenClifford.actionRotation_conjugate value)
  change (NonNullEvenClifford.actionMatrix (NonNullEvenClifford.conjugate value)) =
    (NonNullEvenClifford.actionInverseMatrix value) at inverseMatrixEq
  have matrixAdjugate :
      Matrix3.mul (NonNullEvenClifford.actionMatrix value)
          (Matrix3.adjugate (NonNullEvenClifford.actionMatrix value)) = Matrix3.identity := by
    rw [Matrix3.mul_adjugate, (NonNullEvenClifford.determinant_actionMatrix value),
      Matrix3.one_scale]
  have adjugateEq :
      Matrix3.adjugate (NonNullEvenClifford.actionMatrix value) = (NonNullEvenClifford.actionInverseMatrix value) := by
    calc
      Matrix3.adjugate (NonNullEvenClifford.actionMatrix value) =
          Matrix3.mul Matrix3.identity
            (Matrix3.adjugate (NonNullEvenClifford.actionMatrix value)) :=
        (Matrix3.identity_mul (Matrix3.adjugate (NonNullEvenClifford.actionMatrix value))).symm
      _ = Matrix3.mul
          (Matrix3.mul (NonNullEvenClifford.actionInverseMatrix value) (NonNullEvenClifford.actionMatrix value))
          (Matrix3.adjugate (NonNullEvenClifford.actionMatrix value)) := by
        rw [(NonNullEvenClifford.actionInverseMatrix_mul_actionMatrix value)]
      _ = Matrix3.mul (NonNullEvenClifford.actionInverseMatrix value)
          (Matrix3.mul (NonNullEvenClifford.actionMatrix value)
            (Matrix3.adjugate (NonNullEvenClifford.actionMatrix value))) := by
        rw [Matrix3.mul_assoc]
      _ = Matrix3.mul (NonNullEvenClifford.actionInverseMatrix value) Matrix3.identity := by
        rw [matrixAdjugate]
      _ = (NonNullEvenClifford.actionInverseMatrix value) :=
        Matrix3.mul_identity (NonNullEvenClifford.actionInverseMatrix value)
  have inverseTrace : Matrix3.trace (NonNullEvenClifford.actionInverseMatrix value) = 3 := by
    calc
      Matrix3.trace (NonNullEvenClifford.actionInverseMatrix value) =
          Matrix3.trace (NonNullEvenClifford.actionMatrix (NonNullEvenClifford.conjugate value)) := by
        rw [inverseMatrixEq]
      _ = Matrix3.trace
          (NonNullEvenClifford.actionMatrix (Geometry.Rotations.Ternary.Split.Parabolic.MinkowskiClifford.parabolicValue
            oneNonzero (Coordinates3.Vector.neg axis) negNull)) := by
        rw [conjugateEq]
      _ = 3 := parabolic_trace oneNonzero
        (Coordinates3.Vector.neg axis) negNull
  rw [Matrix3.characteristicValue_expansion,
    parabolic_trace oneNonzero axis null]
  unfold Matrix3.principalTrace
  rw [adjugateEq, inverseTrace, (NonNullEvenClifford.determinant_actionMatrix value)]
  ring1
end
end Purelib.Geometry.Rotations.Ternary.Split.Parabolic.MinkowskiClifford

end

section
@[expose] public section
namespace Purelib.Geometry.Rotations.Ternary.Split.Parabolic.MinkowskiClifford
variable {K : Type*} [ExplicitField K]
section

/-- Construct the finite invariant certificate of a nonzero null-axis parabolic.

The retained rotation fixes the original axis, is nonidentity and unipotent, and has zero handedness on perpendicular
transversals. -/
def parabolicCertificate [DecidableEq K]
    (oneNonzero : (1 : K) ≠ 0) (twoNonzero : (2 : K) ≠ 0)
    (axis : Coordinates3.Vector K)
    (null : (TernaryForm.minkowski oneNonzero).IsNull axis)
    (nonzero : axis ≠ Coordinates3.Vector.zero) :
    ParabolicCertificate oneNonzero twoNonzero where
  axis := axis
  axisNull := null
  axisNonzero := nonzero
  rotation := (NonNullEvenClifford.actionRotation
    (Geometry.Rotations.Ternary.Split.Parabolic.MinkowskiClifford.parabolicValue oneNonzero axis null))
  rotation_spec := rfl
  fixedAxis := by
    rw [NonNullEvenClifford.actionRotation_act]
    exact Geometry.Rotations.Ternary.Split.Parabolic.MinkowskiClifford.parabolic_fixedAxis oneNonzero axis null
  nonidentityMatrix :=
    Geometry.Rotations.Ternary.Split.Parabolic.MinkowskiClifford.parabolic_nonidentity oneNonzero twoNonzero axis null
      nonzero
  characteristicUnipotent :=
    Geometry.Rotations.Ternary.Split.Parabolic.MinkowskiClifford.parabolic_characteristic oneNonzero axis null
  handednessZero := fun transversal perpendicular =>
    Geometry.Rotations.Ternary.Split.Parabolic.MinkowskiClifford.parabolic_handedness_zero oneNonzero axis transversal
      null perpendicular
end
end Purelib.Geometry.Rotations.Ternary.Split.Parabolic.MinkowskiClifford

end

section
@[expose] public section
namespace Purelib.Geometry.Rotations.Ternary.Split.Parabolic.MinkowskiClifford
variable {K : Type*} [ExplicitField K]
section

/-- Every null-axis family member has characteristic polynomial `(X - 1)³`. -/
theorem parabolicRotationAt_characteristic
  (oneNonzero : (1 : K) ≠ 0)
    (axis : Coordinates3.Vector K)
    (null : (TernaryForm.minkowski oneNonzero).IsNull axis)
    (parameter X : K) :
    Matrix3.characteristicValue
        (parabolicRotationAt oneNonzero axis null
          parameter).matrix X =
      (X - 1) ^ 3 :=
  Geometry.Rotations.Ternary.Split.Parabolic.MinkowskiClifford.parabolic_characteristic oneNonzero
    (Coordinates3.Vector.scale parameter axis)
    ((TernaryForm.minkowski oneNonzero).isNull_scale parameter axis null) X
end
end Purelib.Geometry.Rotations.Ternary.Split.Parabolic.MinkowskiClifford

end

section
@[expose] public section
namespace Purelib.Geometry.Rotations.Ternary.Split.Parabolic.MinkowskiClifford
variable {K : Type*} [ExplicitField K]
section

/-- Construct the certified additive rotation family on a displayed nonzero null axis.

The bundle retains the original axis, parameter formulas, group laws, fixed-axis and unipotence identities, and
injectivity when two is nonzero. -/
def nullAxisParabolicFamily [DecidableEq K]
    (oneNonzero : (1 : K) ≠ 0) (twoNonzero : (2 : K) ≠ 0)
    (axis : Coordinates3.Vector K)
    (null : (TernaryForm.minkowski oneNonzero).IsNull axis)
    (nonzero : axis ≠ Coordinates3.Vector.zero) :
    NullAxisParabolicFamily oneNonzero twoNonzero where
  axis := axis
  axisNull := null
  axisNonzero := nonzero
  rotation := parabolicRotationAt oneNonzero axis null
  rotation_spec := fun _ => rfl
  rotation_zero := parabolicRotationAt_zero oneNonzero axis
    null
  rotation_add := parabolicRotationAt_add oneNonzero axis
    null
  rotation_neg := parabolicRotationAt_neg oneNonzero axis
    null
  fixedAxis := parabolicRotationAt_fixedAxis oneNonzero
    axis null
  characteristicUnipotent :=
    parabolicRotationAt_characteristic oneNonzero axis null
  handednessZero := fun parameter transversal perpendicular =>
    parabolicRotationAt_handedness_zero oneNonzero axis
      transversal null
      perpendicular parameter
  nonidentity :=
    parabolicRotationAt_nonidentity oneNonzero twoNonzero
      axis null nonzero
  injective :=
    parabolicRotationAt_injective oneNonzero twoNonzero
      axis null nonzero
end
end Purelib.Geometry.Rotations.Ternary.Split.Parabolic.MinkowskiClifford

end

namespace Purelib.Geometry.Rotations.Ternary.Split.Parabolic.RationalMinkowski

open Purelib.Data.Rat
open Purelib.Algebra.Clifford.Ternary.Basic.TernaryForm
open Purelib.Algebra.Quadratic.Ternary.Basic
open Purelib.Algebra.Clifford.Split
open Purelib.Geometry.Quadratic.Ternary.RationalMinkowski
open Purelib.Geometry.Rotations.Orientation
open Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2
open Purelib.LinearAlgebra.Coordinates3 renaming Vector -> Vector3

set_option genInjectivity false in
/-- Retain a nonidentity unipotent rational Minkowski rotation with a fixed null axis.

The certificate keeps the original rotation, a nonzero null axis and a perpendicular
transversal. Their fixed-axis, characteristic-polynomial and zero-handedness
equalities concern that same retained rotation matrix. -/
public structure ParabolicCertificate
    (rotation : (TernaryForm.SpecialOrthogonal
      Quadratic.Ternary.RationalMinkowski.form)) where
  /-- The retained nonzero null axis fixed by the rotation. -/ axis : Vector3 Fraction.Basic.Rational
  /-- The retained vector perpendicular to the fixed null axis. -/ transversal : Vector3 Fraction.Basic.Rational
  /-- The retained axis has zero Minkowski quadrance. -/ axisNull : (TernaryForm.IsNull
    Quadratic.Ternary.RationalMinkowski.form) axis
  /-- The retained null axis is nonzero. -/ axisNonzero : axis ≠ Vector3.zero
  /-- The retained transversal is Minkowski-perpendicular to the retained axis. -/ transversalPerpendicular :
    (TernaryForm.Perpendicular
      Quadratic.Ternary.RationalMinkowski.form) transversal axis
  /-- The actual rotation matrix fixes the retained axis. -/ axisFixed : Matrix3.rowMul axis rotation.matrix = axis
  /-- The actual rotation matrix is not identity. -/ nonidentityMatrix : rotation.matrix ≠ Matrix3.identity
  /-- The characteristic polynomial of the actual rotation matrix is (X-1) cubed. -/ characteristicUnipotent : ∀ X :
    Fraction.Basic.Rational,
    Matrix3.characteristicValue rotation.matrix X = (X - 1) ^ 3
  /-- The frame determinant of the retained axis, transversal and rotation is zero. -/ handednessZero :
    Handedness.handednessDet axis transversal rotation.matrix = 0

constructive_injectivity ParabolicCertificate

/-- A rational null axis for a nonidentity unipotent transformation. -/
@[expose] public def parabolicAxis : Vector3 Fraction.Rational := ⟨0, 1, -1⟩

/-- The rational null axis (0,1,-1) is nonzero. -/
public theorem parabolicAxis_nonzero : parabolicAxis ≠ Vector3.zero := by decide

/-- The displayed axis has zero Minkowski quadrance.

The original rational Minkowski form evaluates the retained coordinates
`(0, 1, -1)` to zero, without changing the form or the axis. -/
public theorem parabolicAxis_null : (TernaryForm.IsNull
  Quadratic.Ternary.RationalMinkowski.form) parabolicAxis := by
  unfold TernaryForm.IsNull
  rw [Quadratic.Ternary.RationalMinkowski.quadrance]
  unfold parabolicAxis
  ring1

/-- The displayed rational parabolic matrix with rows (1,2,-2), (-2,-1,2), (-2,-2,3). -/
@[expose] public def parabolicDisplayed : Matrix3 Fraction.Rational :=
  ⟨1, 2, -2, -2, -1, 2, -2, -2, 3⟩

/-- The transversal (1,0,0) perpendicular to the retained null axis. -/
@[expose] public def parabolicTransversal : Vector3 Fraction.Rational := ⟨1, 0, 0⟩

/-- The retained transversal is perpendicular to the displayed rational null axis.

The equality uses the original Minkowski bilinear form on the ordered vectors
`(1, 0, 0)` and `(0, 1, -1)`. -/
public theorem parabolicTransversal_perpendicular :
    (TernaryForm.Perpendicular
      Quadratic.Ternary.RationalMinkowski.form) parabolicTransversal parabolicAxis := by
  unfold TernaryForm.Perpendicular TernaryForm.bilinear Quadratic.Ternary.RationalMinkowski.form
    TernaryForm.minkowski TernaryForm.ofMatrix Matrix3.rowMul Vector3.dot
    parabolicTransversal parabolicAxis
  ring1

/-- The rational split Clifford representative of the upper unipotent matrix.

Its scalar coordinate is one and its axis is the retained vector `(0, 1, -1)`.
The norm certificate below uses this exact representative. -/
@[expose] public def parabolicValueRaw : (TernaryForm.EvenClifford
  Quadratic.Ternary.RationalMinkowski.form) :=
  ⟨1, parabolicAxis⟩

/-- The retained rational split Clifford representative has norm one.

The Minkowski null-axis equality reduces its original Clifford norm to one.
The representative and its coordinate order are unchanged. -/
public theorem parabolicValueRaw_norm : (EvenClifford.norm parabolicValueRaw) = 1 := by
  unfold parabolicValueRaw EvenClifford.norm Quadratic.Ternary.RationalMinkowski.form
  rw [TernaryForm.minkowski_determinant,
    TernaryForm.quadrance_minkowski]
  unfold parabolicAxis
  ring1

/-- The displayed rational Clifford representative with its nonzero-norm certificate.

The retained norm-one equality proves the nonzero norm of the same scalar
and axis coordinates. This is the original parent used by the action rotation. -/
@[expose] public def parabolicValue : (TernaryForm.NonNullEvenClifford
  Quadratic.Ternary.RationalMinkowski.form) where
  toEvenClifford := parabolicValueRaw
  normNonzero := by
    rw [parabolicValueRaw_norm]
    exact Quadratic.Ternary.RationalMinkowski.oneNonzero

/-- The retained rational Clifford representative reads back as the upper unipotent matrix.

The split matrix map uses the original rational Minkowski form and its
one-nonzero certificate. Its four entries are exactly `1, 2, 0, 1`. -/
public theorem parabolicValue_matrix2 :
    Matrix.MinkowskiClifford.toMatrix Quadratic.Ternary.RationalMinkowski.oneNonzero parabolicValueRaw =
      (⟨1, 2, 0, 1⟩ : Matrix2 Fraction.Basic.Rational) := by
  apply Matrix2.ext <;> decide

/-- The retained rational Clifford action reads back the displayed parabolic matrix.

The equality identifies all nine original action entries with the retained
three-by-three matrix; it does not construct a second rotation. -/
public theorem parabolic_actionMatrix :
    (NonNullEvenClifford.actionMatrix parabolicValue) = parabolicDisplayed := by decide

/-- The retained rational action has characteristic polynomial `(X - 1)^3`.

The equality holds for every rational scalar in the original characteristic-value
formula, evaluated at the displayed action matrix. -/
public theorem parabolic_characteristic (X : Fraction.Basic.Rational) :
    Matrix3.characteristicValue (NonNullEvenClifford.actionMatrix parabolicValue) X =
      (X - 1) ^ 3 := by
  rw [parabolic_actionMatrix]
  unfold Matrix3.characteristicValue Matrix3.determinant Matrix3.sub
    Matrix3.scale Matrix3.identity parabolicDisplayed
  ring1

/-- The displayed rational parabolic action fixes its retained null axis.

The original row action on `(0, 1, -1)` returns that same vector. Both sides
use the action of the retained nonzero-norm Clifford representative. -/
public theorem parabolic_fixedAxis :
    Matrix3.rowMul parabolicAxis (NonNullEvenClifford.actionMatrix parabolicValue) =
      parabolicAxis := by
  rw [parabolic_actionMatrix]
  apply Vector3.ext <;> decide

/-- The retained axis and transversal have zero handedness for the rational action.

The determinant uses the original ordered frame and action matrix. Its
vanishing is certified for this nonidentity parabolic transformation. -/
public theorem parabolic_handedness_zero :
    Handedness.handednessDet parabolicAxis parabolicTransversal
      (NonNullEvenClifford.actionMatrix parabolicValue) = 0 := by
  rw [parabolic_actionMatrix]
  unfold Handedness.handednessDet parabolicAxis parabolicTransversal
    parabolicDisplayed Vector3.determinant Matrix3.rowMul
  ring1

/-- The displayed rational parabolic action is not the identity matrix.

The retained action reads back its nine displayed entries, which differ from
the original three-by-three identity matrix. -/
public theorem parabolic_nonidentity :
    (NonNullEvenClifford.actionMatrix parabolicValue) ≠ Matrix3.identity := by
  rw [parabolic_actionMatrix]
  decide

/-- Retain the displayed null axis, transversal and all certificates of the nonidentity unipotent action.

The same rational matrix fixes the axis and has zero handedness determinant with the retained transversal. -/
@[expose] public def parabolicCertificate : ParabolicCertificate (NonNullEvenClifford.actionRotation parabolicValue)
  where
  axis := parabolicAxis
  transversal := parabolicTransversal
  axisNull := parabolicAxis_null
  axisNonzero := parabolicAxis_nonzero
  transversalPerpendicular := parabolicTransversal_perpendicular
  axisFixed := parabolic_fixedAxis
  nonidentityMatrix := parabolic_nonidentity
  characteristicUnipotent := parabolic_characteristic
  handednessZero := parabolic_handedness_zero

end Purelib.Geometry.Rotations.Ternary.Split.Parabolic.RationalMinkowski
