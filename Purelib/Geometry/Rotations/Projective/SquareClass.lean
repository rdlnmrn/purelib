module
import Purelib.Algebra.Field.Characteristic.Nonzero
import Purelib.Geometry.Rotations.Basic
import Purelib.Geometry.Rotations.Reflection
import Purelib.LinearAlgebra.Coordinates3.Matrix
import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.Field.SquareClass.Basic
import Purelib.Algebra.Quaternion.Projective.Basic
public import Purelib.Algebra.Quaternion.Projective.SquareClass
public import Purelib.Geometry.Rotations.Cayley.Product
import Purelib.Geometry.Rotations.Projective.Action
public import Purelib.Geometry.Rotations.Projective.Correspondence
import Purelib.Geometry.Rotations.Spread
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.LinearAlgebra.Coordinates3.Vector
import Purelib.Tactic.Ring

section
public section

/-!
# Rational rotations, Theorem 61: the quadrance class

Square classes are represented quotient-free.  Equality carries an explicit
nonzero square factor, so invariance and multiplicativity remain executable
finite field calculations.
-/

namespace Purelib.Geometry.Rotations.Projective.SquareClass

open Purelib
open Purelib.Algebra
open Purelib.Algebra.Field
open Purelib.Algebra.Field.SquareClass.Basic
open Purelib.Algebra.Quaternion
open Purelib.Algebra.Quaternion.Projective.Basic
open Purelib.Algebra.Quaternion.Projective.SquareClass
open Purelib.Geometry
open Purelib.Geometry.Rotations
open Purelib.Geometry.Rotations.Projective.Action
open Purelib.Geometry.Rotations.Projective.Correspondence
open Purelib.LinearAlgebra.Coordinates3
open Purelib.LinearAlgebra.Coordinates3 renaming Vector -> Vector3

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

namespace NonNullProportion

/-- The affine closed form in Theorem 61: `[N(x,v)] = [1-halfSpread]`. -/
theorem
  quadranceClass_equivalent_one_sub_halfSpread
    (proportion : Projective.Basic.NonNullProportion K)
    (scalarNonzero : proportion.scalar ≠ 0)
    (twoNonzero : (2 : K) ≠ 0) :
    (NonNullProportion.quadranceClass proportion).Equivalent
      { value := 1 - Spread.halfSpread (NonNullProportion.rotation proportion)
        nonzero := by
          rw [NonNullProportion.one_sub_halfSpread_rotation proportion twoNonzero]
          exact Algebra.Field.ExplicitField.div_ne_zero
            ((fun {K : Type _} [Purelib.Algebra.Field.ExplicitField K] (proportion :
              Purelib.Algebra.Quaternion.Projective.Basic.NonNullProportion K) (scalarNonzero : proportion.scalar ≠ 0)
              => (Purelib.Algebra.Field.ExplicitField.square_nonzero_of_nonzero (K := K) (value := proportion.scalar)
              scalarNonzero : proportion.scalar ^ 2 ≠ 0)) proportion scalarNonzero)
            proportion.normNonzero } := by
  let factor := proportion.scalar / proportion.toProportion.norm
  have factorNonzero : factor ≠ 0 :=
    Algebra.Field.ExplicitField.div_ne_zero scalarNonzero proportion.normNonzero
  have normCancel := Algebra.Field.ExplicitField.mul_inv_cancel
    proportion.toProportion.norm proportion.normNonzero
  refine ⟨factor, factorNonzero, ?_⟩
  change 1 - Spread.halfSpread (NonNullProportion.rotation proportion) =
    factor ^ 2 * proportion.toProportion.norm
  rw [NonNullProportion.one_sub_halfSpread_rotation proportion twoNonzero]
  unfold factor
  simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
  calc
    proportion.scalar ^ 2 * proportion.toProportion.norm⁻¹ =
        (proportion.scalar * proportion.toProportion.norm⁻¹) ^ 2 *
          proportion.toProportion.norm := by
      symm
      calc
        (proportion.scalar * proportion.toProportion.norm⁻¹) ^ 2 *
            proportion.toProportion.norm =
          proportion.scalar ^ 2 * proportion.toProportion.norm⁻¹ *
            (proportion.toProportion.norm⁻¹ *
              proportion.toProportion.norm) := by ring1
        _ = proportion.scalar ^ 2 * proportion.toProportion.norm⁻¹ := by
          rw [show proportion.toProportion.norm⁻¹ *
              proportion.toProportion.norm = 1 by
            calc
              proportion.toProportion.norm⁻¹ *
                  proportion.toProportion.norm =
                proportion.toProportion.norm *
                  proportion.toProportion.norm⁻¹ := by ring1
              _ = 1 := normCancel,
            mul_one]

/-- The infinity closed form in Theorem 61: `[N(0,v)]=[Q(v)]`. -/
theorem quadranceClass_at_infinity
  (proportion : Projective.Basic.NonNullProportion K)
    (scalarZero : proportion.scalar = 0) :
    (NonNullProportion.quadranceClass proportion).value = proportion.vector.quadrance := by
  change proportion.toProportion.norm = proportion.vector.quadrance
  unfold Proportion.norm
  rw [scalarZero]
  ring1

end NonNullProportion

namespace RotationQuadranceClass

/-- Theorem 61's invariant on rotations, computed from the executable inverse representative of Theorem 58. -/
@[expose] public def ofRotation
  [DecidableEq K] (rotation : Rotations.Basic.Rotation K)
    (twoNonzero : (2 : K) ≠ 0) : SquareClass.Basic.SquareClassRepresentative K :=
  (NonNullProportion.quadranceClass (RotationProportion.ofRotation rotation twoNonzero))

/-- The stored rotation class agrees with the norm class of any retained representative of its original matrix.

Projective faithfulness preserves the exact nonzero homogeneous scale between the executable preimage and the supplied
proportion. -/
theorem ofRotation_equivalent_representative [DecidableEq K]
    (rotation : Rotations.Basic.Rotation K) (proportion : Projective.Basic.NonNullProportion K)
    (twoNonzero : (2 : K) ≠ 0) (represents : NonNullProportion.rotationMatrix proportion = rotation.matrix) :
    (ofRotation rotation twoNonzero).Equivalent
      (Quaternion.Projective.SquareClass.NonNullProportion.quadranceClass proportion) := by
  apply Quaternion.Projective.SquareClass.NonNullProportion.quadranceClass_respects_equivalent
  apply NonNullProportion.equivalent_of_rotationMatrix_eq _ _ twoNonzero
  exact (RotationProportion.ofRotation_rotationMatrix rotation twoNonzero).trans represents.symm

/-- Away from half turns, the original rotation class is represented by one minus its half spread.

The rotation's cached projective preimage has nonzero scalar coordinate, so its existing complementary-half-spread
identity supplies the retained square factor. -/
theorem ofRotation_one_sub_halfSpread [DecidableEq K] (rotation : Rotations.Basic.Rotation K)
    (twoNonzero : (2 : K) ≠ 0) (notHalfTurn : Spread.halfSpread rotation ≠ 1) :
    (ofRotation rotation twoNonzero).Equivalent
      ⟨1 - Spread.halfSpread rotation, ExplicitField.one_sub_ne_zero_of_ne_one notHalfTurn⟩ := by
  let proportion := RotationProportion.ofRotation rotation twoNonzero
  have represents : NonNullProportion.rotation proportion = rotation :=
    Rotations.Basic.Rotation.eq_of_matrix_eq _ _
      (RotationProportion.ofRotation_rotationMatrix rotation twoNonzero)
  have scalarNonzero : proportion.scalar ≠ 0 := by
    intro zero
    have halfTurn := (NonNullProportion.halfSpread_rotation_eq_one_iff proportion twoNonzero).mpr zero
    rw [represents] at halfTurn
    exact notHalfTurn halfTurn
  have classes := NonNullProportion.quadranceClass_equivalent_one_sub_halfSpread proportion scalarNonzero twoNonzero
  rcases classes with ⟨factor, factorNonzero, valueEqual⟩
  refine ⟨factor, factorNonzero, ?_⟩
  calc
    1 - Spread.halfSpread rotation = 1 - Spread.halfSpread (NonNullProportion.rotation proportion) :=
      congrArg (fun value => 1 - Spread.halfSpread value) represents.symm
    _ = factor ^ 2 * (NonNullProportion.quadranceClass proportion).value := valueEqual

/-- The original half-turn class is represented by the quadrance of its retained non-null axis. -/
theorem ofRotation_halfTurn [DecidableEq K] (axis : Vector3 K) (axisNonNull : axis.quadrance ≠ 0)
    (twoNonzero : (2 : K) ≠ 0) :
    (ofRotation (Reflection.halfTurnRotation axis axisNonNull) twoNonzero).Equivalent
      ⟨axis.quadrance, axisNonNull⟩ := by
  let proportion := Projective.Basic.NonNullProportion.ofNonNullVector axis axisNonNull
  have classes := ofRotation_equivalent_representative (Reflection.halfTurnRotation axis axisNonNull)
    proportion twoNonzero (NonNullProportion.rotationMatrix_eq_halfTurn proportion rfl)
  apply SquareClassRepresentative.equivalent_trans classes
  refine ⟨1, proportion.one_ne_zero, ?_⟩
  change axis.quadrance = 1 ^ 2 * (0 ^ 2 + axis.quadrance)
  ring1

/-- The spinor norm of an original Euclidean reflection product is the product of its retained normal quadrances.

The two pure-vector quaternion representatives act as the corresponding half turns, whose product is the original
reflection product. This covers both perpendicular and non-perpendicular normals with the same norm multiplication
certificate. -/
theorem ofRotation_reflectionProduct [DecidableEq K] (first second : Vector3 K)
    (firstNonNull : first.quadrance ≠ 0) (secondNonNull : second.quadrance ≠ 0)
    (twoNonzero : (2 : K) ≠ 0) :
    (ofRotation (Reflection.reflectionProductRotation first second firstNonNull secondNonNull)
      twoNonzero).Equivalent
      ⟨first.quadrance * second.quadrance, ExplicitField.mul_ne_zero firstNonNull secondNonNull⟩ := by
  let left := Projective.Basic.NonNullProportion.ofNonNullVector first firstNonNull
  let right := Projective.Basic.NonNullProportion.ofNonNullVector second secondNonNull
  let product := Projective.Basic.NonNullProportion.mul left right
  have represents : NonNullProportion.rotationMatrix product =
      (Reflection.reflectionProductRotation first second firstNonNull secondNonNull).matrix := by
    change NonNullProportion.rotationMatrix (Projective.Basic.NonNullProportion.mul left right) = _
    rw [NonNullProportion.rotationMatrix_mul,
      NonNullProportion.rotationMatrix_eq_halfTurn left rfl,
      NonNullProportion.rotationMatrix_eq_halfTurn right rfl,
      Reflection.halfTurn, Reflection.halfTurn, Matrix3.mul_neg_neg]
    rfl
  have classes := ofRotation_equivalent_representative
    (Reflection.reflectionProductRotation first second firstNonNull secondNonNull) product twoNonzero represents
  apply SquareClassRepresentative.equivalent_trans classes
  refine ⟨1, left.one_ne_zero, ?_⟩
  change first.quadrance * second.quadrance = 1 ^ 2 * Proportion.norm
    (Proportion.mul left.toProportion right.toProportion)
  rw [Proportion.norm_mul]
  change first.quadrance * second.quadrance =
    1 ^ 2 * ((0 ^ 2 + first.quadrance) * (0 ^ 2 + second.quadrance))
  ring1

/-- Theorem 61's homomorphism law on stored rotations. -/
theorem of_rotationProduct [DecidableEq
  K]
    (left right : Rotations.Basic.Rotation K) (twoNonzero : (2 : K) ≠ 0) :
    (Geometry.Rotations.Projective.SquareClass.RotationQuadranceClass.ofRotation (Cayley.Product.rotationProduct left
      right) twoNonzero).Equivalent
      (SquareClassRepresentative.mul
        (Geometry.Rotations.Projective.SquareClass.RotationQuadranceClass.ofRotation left twoNonzero)
          (Geometry.Rotations.Projective.SquareClass.RotationQuadranceClass.ofRotation right twoNonzero)) := by
  let leftProportion := RotationProportion.ofRotation left twoNonzero
  let rightProportion := RotationProportion.ofRotation right twoNonzero
  let productProportion := NonNullProportion.mul leftProportion rightProportion
  let canonicalProduct :=
    RotationProportion.ofRotation (Cayley.Product.rotationProduct left right) twoNonzero
  have matrixEqual : (NonNullProportion.rotationMatrix canonicalProduct) =
      (NonNullProportion.rotationMatrix productProportion) := by
    calc
      (NonNullProportion.rotationMatrix canonicalProduct) =
          (Cayley.Product.rotationProduct left right).matrix :=
        RotationProportion.ofRotation_rotationMatrix
          (Cayley.Product.rotationProduct left right) twoNonzero
      _ = Matrix3.mul left.matrix right.matrix := rfl
      _ = Matrix3.mul (NonNullProportion.rotationMatrix leftProportion)
          (NonNullProportion.rotationMatrix rightProportion) := by
        rw [RotationProportion.ofRotation_rotationMatrix left twoNonzero,
          RotationProportion.ofRotation_rotationMatrix right twoNonzero]
      _ = (NonNullProportion.rotationMatrix productProportion) :=
        (NonNullProportion.rotationMatrix_mul leftProportion
          rightProportion).symm
  have equivalent := NonNullProportion.equivalent_of_rotationMatrix_eq
    canonicalProduct productProportion twoNonzero matrixEqual
  have classEquivalent :=
    NonNullProportion.quadranceClass_respects_equivalent equivalent
  change (NonNullProportion.quadranceClass canonicalProduct).Equivalent
    (SquareClassRepresentative.mul (NonNullProportion.quadranceClass leftProportion)
      (NonNullProportion.quadranceClass rightProportion))
  exact SquareClassRepresentative.equivalent_trans classEquivalent
    (by
      rw [NonNullProportion.quadranceClass_mul]
      exact SquareClassRepresentative.equivalent_refl _)

end RotationQuadranceClass
end Purelib.Geometry.Rotations.Projective.SquareClass

end
